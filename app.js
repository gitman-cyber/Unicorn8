(() => {
'use strict';

// ===== imagefs.mjs =====
const MAGIC = 'M16IMG1\0';
const LEGACY_MAGIC = 'U8IMG01\0';
const VERSION = 1;
const DEFAULT_SECTOR_SIZE = 512;
const HEADER_SIZE = 512;
const ENTRY_SIZE = 128;
const PATH_BYTES = 96;
const FLAG_BOOTABLE = 1 << 0;
const FLAG_CART = 1 << 1;
const FLAG_SYSTEM = 1 << 2;
const MBR_SIZE = 512;
const MBR_PARTITION_OFFSET = 446;
const MBR_SIGNATURE_OFFSET = 510;
const M16_PARTITION_TYPE = 0x7f;
const FAT16_PARTITION_TYPE = 0x06;
const DEFAULT_PARTITION_START_LBA = 2048;
const FAT_ATTR_DIRECTORY = 0x10;
const FAT_ATTR_ARCHIVE = 0x20;

const encoder = new TextEncoder();
const decoder = new TextDecoder();

let crcTable = null;

function makeCrcTable() {
  const table = new Uint32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = (c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1);
    table[n] = c >>> 0;
  }
  return table;
}

function crc32(bytes) {
  if (!crcTable) crcTable = makeCrcTable();
  let c = 0xFFFFFFFF;
  for (let i = 0; i < bytes.length; i++) c = crcTable[(c ^ bytes[i]) & 0xFF] ^ (c >>> 8);
  return (c ^ 0xFFFFFFFF) >>> 0;
}

function align(value, size) {
  return Math.ceil(value / size) * size;
}

function asBytes(value) {
  if (value instanceof Uint8Array) return value;
  if (value instanceof ArrayBuffer) return new Uint8Array(value);
  if (ArrayBuffer.isView(value)) return new Uint8Array(value.buffer, value.byteOffset, value.byteLength);
  if (typeof value === 'string') return encoder.encode(value);
  if (value && typeof value === 'object') return encoder.encode(JSON.stringify(value, null, 2));
  throw new TypeError('File value must be Uint8Array, ArrayBuffer, string, or JSON-compatible object.');
}

function normalizePath(path) {
  if (typeof path !== 'string' || !path.trim()) throw new Error('Empty path inside image.');
  let p = path.replace(/\\+/g, '/').trim();
  if (!p.startsWith('/')) p = '/' + p;
  const parts = [];
  for (const part of p.split('/')) {
    if (!part || part === '.') continue;
    if (part === '..') throw new Error(`Parent traversal is not allowed in image path: ${path}`);
    parts.push(part);
  }
  return '/' + parts.join('/');
}

function writeFixedString(target, offset, length, text) {
  const bytes = encoder.encode(String(text ?? ''));
  const n = Math.min(length - 1, bytes.length);
  target.fill(0, offset, offset + length);
  target.set(bytes.subarray(0, n), offset);
}

function readFixedString(source, offset, length) {
  let end = offset;
  const max = offset + length;
  while (end < max && source[end] !== 0) end++;
  return decoder.decode(source.subarray(offset, end));
}

function readMagic(bytes) {
  return decoder.decode(bytes.subarray(0, 8));
}

function isSupportedMagic(magic) {
  return magic === MAGIC || magic === LEGACY_MAGIC;
}

class ImageFileSystem {
  constructor(bytes, header, entries, diskBytes = bytes) {
    this.bytes = bytes;
    this.diskBytes = diskBytes;
    this.header = Object.freeze({ ...header });
    this.entries = entries.map(e => Object.freeze({ ...e }));
    this.index = new Map(this.entries.map(e => [e.path, e]));
  }

  list(prefix = '/') {
    const p = normalizePath(prefix);
    return this.entries.filter(e => e.path.startsWith(p === '/' ? '/' : p + '/')).map(e => e.path);
  }

  stat(path) {
    const entry = this.index.get(normalizePath(path));
    if (!entry) return null;
    return { ...entry };
  }

  has(path) {
    return this.index.has(normalizePath(path));
  }

  readFile(path) {
    const entry = this.index.get(normalizePath(path));
    if (!entry) throw new Error(`Image file not found: ${path}`);
    let out;
    if (entry.chunks) {
      out = new Uint8Array(entry.length);
      let written = 0;
      for (const chunk of entry.chunks) {
        const n = Math.min(chunk.length, entry.length - written);
        out.set(this.bytes.subarray(chunk.offset, chunk.offset + n), written);
        written += n;
        if (written >= entry.length) break;
      }
    } else {
      out = this.bytes.slice(entry.offset, entry.offset + entry.length);
    }
    const actual = crc32(out);
    if (actual !== entry.crc32) {
      throw new Error(`CRC mismatch for ${entry.path}: expected ${entry.crc32.toString(16)}, got ${actual.toString(16)}`);
    }
    return out;
  }

  readText(path) {
    return decoder.decode(this.readFile(path));
  }

  readJSON(path) {
    return JSON.parse(this.readText(path));
  }

  isBootable() {
    return Boolean(this.header.flags & FLAG_BOOTABLE);
  }

  isSystem() {
    return Boolean(this.header.flags & FLAG_SYSTEM);
  }

  isCart() {
    return Boolean(this.header.flags & FLAG_CART);
  }

  isPartitioned() {
    return Boolean(this.header.partition);
  }
}

function writeMbrPartitionEntry(target, entryOffset, partition) {
  target[entryOffset + 0] = 0x00;
  target[entryOffset + 1] = 0x00;
  target[entryOffset + 2] = 0x02;
  target[entryOffset + 3] = 0x00;
  target[entryOffset + 4] = partition.type;
  target[entryOffset + 5] = 0xfe;
  target[entryOffset + 6] = 0xff;
  target[entryOffset + 7] = 0xff;
  const view = new DataView(target.buffer, target.byteOffset, target.byteLength);
  view.setUint32(entryOffset + 8, partition.startLba, true);
  view.setUint32(entryOffset + 12, partition.sectorCount, true);
}

function wrapImageInMbrPartition(payload, options = {}) {
  const sectorSize = options.sectorSize || DEFAULT_SECTOR_SIZE;
  if (sectorSize !== MBR_SIZE) throw new Error('Partitioned images currently require 512-byte sectors.');

  const startLba = options.partitionStartLba || DEFAULT_PARTITION_START_LBA;
  const partitionOffset = startLba * sectorSize;
  const partitionBytes = align(payload.length, sectorSize);
  const sectorCount = partitionBytes / sectorSize;
  const totalBytes = partitionOffset + partitionBytes;
  const disk = new Uint8Array(totalBytes);

  disk.set(payload, partitionOffset);
  writeMbrPartitionEntry(disk, MBR_PARTITION_OFFSET, {
    type: options.partitionType || M16_PARTITION_TYPE,
    startLba,
    sectorCount,
  });
  disk[MBR_SIGNATURE_OFFSET] = 0x55;
  disk[MBR_SIGNATURE_OFFSET + 1] = 0xaa;
  return disk;
}

function fatDateTime(date = new Date()) {
  const year = Math.max(1980, date.getFullYear());
  const fatDate = ((year - 1980) << 9) | ((date.getMonth() + 1) << 5) | date.getDate();
  const fatTime = (date.getHours() << 11) | (date.getMinutes() << 5) | Math.floor(date.getSeconds() / 2);
  return { fatDate, fatTime };
}

function toFatName(pathPart) {
  const cleaned = String(pathPart).toUpperCase().replace(/[^A-Z0-9._-]/g, '_');
  const dot = cleaned.lastIndexOf('.');
  const base = (dot >= 0 ? cleaned.slice(0, dot) : cleaned).replace(/[^A-Z0-9_-]/g, '_').slice(0, 8);
  const ext = (dot >= 0 ? cleaned.slice(dot + 1) : '').replace(/[^A-Z0-9_-]/g, '_').slice(0, 3);
  if (!base) throw new Error(`Cannot make FAT name for ${pathPart}`);
  return (base.padEnd(8, ' ') + ext.padEnd(3, ' ')).slice(0, 11);
}

function fromFatName(bytes, offset) {
  const rawBase = decoder.decode(bytes.subarray(offset, offset + 8)).trim().toLowerCase();
  const rawExt = decoder.decode(bytes.subarray(offset + 8, offset + 11)).trim().toLowerCase();
  return rawExt ? `${rawBase}.${rawExt}` : rawBase;
}

function writeFatName(target, offset, name) {
  const bytes = encoder.encode(name === '.' ? '.          ' : name === '..' ? '..         ' : toFatName(name));
  target.set(bytes, offset);
}

function writeFatDirEntry(target, offset, entry) {
  writeFatName(target, offset, entry.name);
  target[offset + 11] = entry.attr;
  const stamp = fatDateTime();
  const view = new DataView(target.buffer, target.byteOffset, target.byteLength);
  view.setUint16(offset + 14, stamp.fatTime, true);
  view.setUint16(offset + 16, stamp.fatDate, true);
  view.setUint16(offset + 22, stamp.fatTime, true);
  view.setUint16(offset + 24, stamp.fatDate, true);
  view.setUint16(offset + 26, entry.cluster || 0, true);
  view.setUint32(offset + 28, entry.size || 0, true);
}

function writeFatValue(disk, fatOffset, cluster, value) {
  const view = new DataView(disk.buffer, disk.byteOffset, disk.byteLength);
  view.setUint16(fatOffset + cluster * 2, value, true);
}

function fatClusterOffset(layout, cluster) {
  return layout.partitionOffset + (layout.firstDataSector + (cluster - 2) * layout.sectorsPerCluster) * layout.bytesPerSector;
}

function createFat16CartDisk(options = {}) {
  const bytesPerSector = DEFAULT_SECTOR_SIZE;
  const sectorsPerCluster = 1;
  const reservedSectors = 1;
  const fatCount = 2;
  const rootEntryCount = 512;
  const rootDirSectors = Math.ceil(rootEntryCount * 32 / bytesPerSector);
  const startLba = options.partitionStartLba || DEFAULT_PARTITION_START_LBA;
  const volumeLabel = String(options.label || 'M16 CART').toUpperCase().replace(/[^A-Z0-9 ]/g, ' ').slice(0, 11).padEnd(11, ' ');

  const rawFiles = options.files || {};
  const files = Object.entries(rawFiles).map(([path, value]) => ({ path: normalizePath(path), bytes: asBytes(value) }));
  files.sort((a, b) => a.path.localeCompare(b.path));
  const dirs = new Set();
  for (const file of files) {
    const parts = file.path.split('/').filter(Boolean);
    for (let i = 0; i < parts.length - 1; i++) dirs.add('/' + parts.slice(0, i + 1).join('/'));
  }
  const dirList = [...dirs].sort((a, b) => a.localeCompare(b));
  const usedDataClusters = dirList.length + files.reduce((sum, file) => sum + Math.max(1, Math.ceil(file.bytes.length / bytesPerSector)), 0);
  const dataClusterNeed = Math.max(4096, usedDataClusters);
  let sectorsPerFat = 1;
  for (;;) {
    const totalSectors = reservedSectors + fatCount * sectorsPerFat + rootDirSectors + dataClusterNeed + 16;
    const dataSectors = totalSectors - reservedSectors - fatCount * sectorsPerFat - rootDirSectors;
    const clusterCount = Math.floor(dataSectors / sectorsPerCluster);
    const neededFatSectors = Math.ceil((clusterCount + 2) * 2 / bytesPerSector);
    if (neededFatSectors === sectorsPerFat) break;
    sectorsPerFat = neededFatSectors;
  }

  const totalSectors = reservedSectors + fatCount * sectorsPerFat + rootDirSectors + dataClusterNeed + 16;
  const partitionOffset = startLba * bytesPerSector;
  const partitionBytes = totalSectors * bytesPerSector;
  const disk = new Uint8Array(partitionOffset + partitionBytes);
  const view = new DataView(disk.buffer);
  const layout = {
    bytesPerSector,
    sectorsPerCluster,
    partitionOffset,
    firstFatSector: reservedSectors,
    rootDirSector: reservedSectors + fatCount * sectorsPerFat,
    firstDataSector: reservedSectors + fatCount * sectorsPerFat + rootDirSectors,
  };
  const fatOffset = partitionOffset + layout.firstFatSector * bytesPerSector;
  const rootOffset = partitionOffset + layout.rootDirSector * bytesPerSector;

  writeMbrPartitionEntry(disk, MBR_PARTITION_OFFSET, {
    type: FAT16_PARTITION_TYPE,
    startLba,
    sectorCount: totalSectors,
  });
  disk[MBR_SIGNATURE_OFFSET] = 0x55;
  disk[MBR_SIGNATURE_OFFSET + 1] = 0xaa;

  const vbr = partitionOffset;
  disk[vbr + 0] = 0xeb;
  disk[vbr + 1] = 0x3c;
  disk[vbr + 2] = 0x90;
  disk.set(encoder.encode('MEGA16  '), vbr + 3);
  view.setUint16(vbr + 11, bytesPerSector, true);
  disk[vbr + 13] = sectorsPerCluster;
  view.setUint16(vbr + 14, reservedSectors, true);
  disk[vbr + 16] = fatCount;
  view.setUint16(vbr + 17, rootEntryCount, true);
  view.setUint16(vbr + 19, totalSectors < 0x10000 ? totalSectors : 0, true);
  disk[vbr + 21] = 0xf8;
  view.setUint16(vbr + 22, sectorsPerFat, true);
  view.setUint16(vbr + 24, 63, true);
  view.setUint16(vbr + 26, 255, true);
  view.setUint32(vbr + 28, startLba, true);
  view.setUint32(vbr + 32, totalSectors >= 0x10000 ? totalSectors : 0, true);
  disk[vbr + 36] = 0x80;
  disk[vbr + 38] = 0x29;
  view.setUint32(vbr + 39, crc32(encoder.encode(options.label || 'M16 CART')), true);
  disk.set(encoder.encode(volumeLabel), vbr + 43);
  disk.set(encoder.encode('FAT16   '), vbr + 54);
  disk.set(encoder.encode('This is a data cartridge, not bootable.\r\n'), vbr + 90);
  disk[vbr + 510] = 0x55;
  disk[vbr + 511] = 0xaa;

  for (let fat = 0; fat < fatCount; fat++) {
    const off = fatOffset + fat * sectorsPerFat * bytesPerSector;
    writeFatValue(disk, off, 0, 0xfff8);
    writeFatValue(disk, off, 1, 0xffff);
  }

  let nextCluster = 2;
  const dirClusters = new Map();
  for (const dir of dirList) dirClusters.set(dir, nextCluster++);
  const fileRecords = files.map(file => {
    const clusters = [];
    const count = Math.max(1, Math.ceil(file.bytes.length / bytesPerSector));
    for (let i = 0; i < count; i++) clusters.push(nextCluster++);
    return { ...file, clusters };
  });

  const setFatChain = clusters => {
    for (let i = 0; i < clusters.length; i++) {
      const value = i + 1 < clusters.length ? clusters[i + 1] : 0xffff;
      for (let fat = 0; fat < fatCount; fat++) {
        writeFatValue(disk, fatOffset + fat * sectorsPerFat * bytesPerSector, clusters[i], value);
      }
    }
  };
  for (const cluster of dirClusters.values()) setFatChain([cluster]);
  for (const file of fileRecords) setFatChain(file.clusters);

  for (const file of fileRecords) {
    let copied = 0;
    for (const cluster of file.clusters) {
      const off = fatClusterOffset(layout, cluster);
      const chunk = file.bytes.subarray(copied, copied + bytesPerSector);
      disk.set(chunk, off);
      copied += chunk.length;
    }
  }

  const children = new Map([['/', []]]);
  for (const dir of dirList) children.set(dir, []);
  for (const dir of dirList) {
    const parts = dir.split('/').filter(Boolean);
    const parent = parts.length === 1 ? '/' : '/' + parts.slice(0, -1).join('/');
    children.get(parent).push({ name: parts[parts.length - 1], attr: FAT_ATTR_DIRECTORY, cluster: dirClusters.get(dir), size: 0, path: dir });
  }
  for (const file of fileRecords) {
    const parts = file.path.split('/').filter(Boolean);
    const parent = parts.length === 1 ? '/' : '/' + parts.slice(0, -1).join('/');
    children.get(parent).push({ name: parts[parts.length - 1], attr: FAT_ATTR_ARCHIVE, cluster: file.clusters[0], size: file.bytes.length, path: file.path });
  }

  const writeDirectory = (dirPath, offset, parentCluster) => {
    let pos = offset;
    if (dirPath !== '/') {
      const cluster = dirClusters.get(dirPath);
      writeFatDirEntry(disk, pos, { name: '.', attr: FAT_ATTR_DIRECTORY, cluster, size: 0 });
      pos += 32;
      writeFatDirEntry(disk, pos, { name: '..', attr: FAT_ATTR_DIRECTORY, cluster: parentCluster || 0, size: 0 });
      pos += 32;
    }
    for (const child of children.get(dirPath) || []) {
      writeFatDirEntry(disk, pos, child);
      pos += 32;
    }
  };
  writeDirectory('/', rootOffset, 0);
  for (const dir of dirList) {
    const parts = dir.split('/').filter(Boolean);
    const parent = parts.length === 1 ? '/' : '/' + parts.slice(0, -1).join('/');
    const parentCluster = parent === '/' ? 0 : dirClusters.get(parent);
    writeDirectory(dir, fatClusterOffset(layout, dirClusters.get(dir)), parentCluster);
  }

  return disk;
}

function findImagePayload(bytes) {
  if (isSupportedMagic(readMagic(bytes))) {
    return { bytes, partition: null };
  }

  if (bytes.byteLength >= MBR_SIZE && bytes[MBR_SIGNATURE_OFFSET] === 0x55 && bytes[MBR_SIGNATURE_OFFSET + 1] === 0xaa) {
    const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
    for (let i = 0; i < 4; i++) {
      const off = MBR_PARTITION_OFFSET + i * 16;
      const status = bytes[off];
      const type = bytes[off + 4];
      const startLba = view.getUint32(off + 8, true);
      const sectorCount = view.getUint32(off + 12, true);
      if (type === 0 || sectorCount === 0) continue;
      if (status === 0x80) throw new Error('Cart disk has a bootable partition; carts must stay non-bootable.');
      const byteOffset = startLba * MBR_SIZE;
      const byteLength = sectorCount * MBR_SIZE;
      if (byteOffset < MBR_SIZE || byteOffset + byteLength > bytes.byteLength) {
        throw new Error('Partition table points outside the image.');
      }
      const payload = bytes.slice(byteOffset, byteOffset + byteLength);
      if (isSupportedMagic(readMagic(payload))) {
        return {
          bytes: payload,
          partition: { index: i + 1, type, bootable: false, startLba, sectorCount, byteOffset, byteLength },
        };
      }
    }
  }

  return { bytes, partition: null };
}

function parseFat16CartDisk(input) {
  const bytes = input instanceof Uint8Array ? input : new Uint8Array(input);
  if (bytes.byteLength < MBR_SIZE || bytes[MBR_SIGNATURE_OFFSET] !== 0x55 || bytes[MBR_SIGNATURE_OFFSET + 1] !== 0xaa) return null;
  const diskView = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let lastReason = 'no usable partition entries';

  for (let i = 0; i < 4; i++) {
    const partOff = MBR_PARTITION_OFFSET + i * 16;
    const status = bytes[partOff];
    const type = bytes[partOff + 4];
    const startLba = diskView.getUint32(partOff + 8, true);
    const sectorCount = diskView.getUint32(partOff + 12, true);
    if (type === 0 || sectorCount === 0) continue;
    if (status === 0x80) throw new Error('Cart disk has a bootable partition; carts must stay non-bootable.');
    if (type !== FAT16_PARTITION_TYPE && type !== 0x0e) { lastReason = `partition ${i + 1} type 0x${type.toString(16)} is not FAT16`; continue; }

    const partitionOffset = startLba * MBR_SIZE;
    const partitionBytes = sectorCount * MBR_SIZE;
    if (partitionOffset < MBR_SIZE || partitionOffset + partitionBytes > bytes.byteLength) {
      throw new Error('FAT16 partition points outside the image.');
    }

    const vbr = partitionOffset;
    if (bytes[vbr + 510] !== 0x55 || bytes[vbr + 511] !== 0xaa) { lastReason = `partition ${i + 1} has no VBR signature`; continue; }
    const bytesPerSector = diskView.getUint16(vbr + 11, true);
    const sectorsPerCluster = bytes[vbr + 13];
    const reservedSectors = diskView.getUint16(vbr + 14, true);
    const fatCount = bytes[vbr + 16];
    const rootEntryCount = diskView.getUint16(vbr + 17, true);
    const totalSectors16 = diskView.getUint16(vbr + 19, true);
    const sectorsPerFat = diskView.getUint16(vbr + 22, true);
    const totalSectors32 = diskView.getUint32(vbr + 32, true);
    const totalSectors = totalSectors16 || totalSectors32 || sectorCount;
    if (bytesPerSector !== MBR_SIZE || !sectorsPerCluster || !fatCount || !sectorsPerFat || !rootEntryCount) {
      lastReason = `partition ${i + 1} has invalid FAT BPB bps=${bytesPerSector} spc=${sectorsPerCluster} fats=${fatCount} spf=${sectorsPerFat} root=${rootEntryCount}`;
      continue;
    }

    const rootDirSectors = Math.ceil(rootEntryCount * 32 / bytesPerSector);
    const firstFatOffset = partitionOffset + reservedSectors * bytesPerSector;
    const rootOffset = partitionOffset + (reservedSectors + fatCount * sectorsPerFat) * bytesPerSector;
    const firstDataSector = reservedSectors + fatCount * sectorsPerFat + rootDirSectors;
    const clusterOffset = cluster => partitionOffset + (firstDataSector + (cluster - 2) * sectorsPerCluster) * bytesPerSector;
    const clusterBytes = sectorsPerCluster * bytesPerSector;
    const readFat = cluster => diskView.getUint16(firstFatOffset + cluster * 2, true);
    const clusterChain = firstCluster => {
      const chain = [];
      let cluster = firstCluster;
      const seen = new Set();
      while (cluster >= 2 && cluster < 0xfff8 && !seen.has(cluster)) {
        seen.add(cluster);
        chain.push(cluster);
        cluster = readFat(cluster);
      }
      return chain;
    };
    const readDirectoryEntries = (offset, byteLength, prefix) => {
      const out = [];
      for (let pos = offset; pos < offset + byteLength; pos += 32) {
        const first = bytes[pos];
        if (first === 0x00) break;
        if (first === 0xe5 || bytes[pos + 11] === 0x0f) continue;
        const name = fromFatName(bytes, pos);
        if (!name || name === '.' || name === '..') continue;
        const attr = bytes[pos + 11];
        const cluster = diskView.getUint16(pos + 26, true);
        const size = diskView.getUint32(pos + 28, true);
        const path = `${prefix === '/' ? '' : prefix}/${name.toLowerCase()}`;
        out.push({ name, attr, cluster, size, path });
      }
      return out;
    };

    const entries = [];
    const walk = (prefix, offset, byteLength) => {
      for (const entry of readDirectoryEntries(offset, byteLength, prefix)) {
        if (entry.attr & FAT_ATTR_DIRECTORY) {
          const chain = clusterChain(entry.cluster);
          for (const cluster of chain) walk(entry.path, clusterOffset(cluster), clusterBytes);
        } else {
          const chain = clusterChain(entry.cluster);
          if (!chain.length && entry.size > 0) throw new Error(`FAT file has no cluster chain: ${entry.path}`);
          const chunks = chain.map(cluster => ({ offset: clusterOffset(cluster), length: clusterBytes }));
          const fileBytes = new Uint8Array(entry.size);
          let written = 0;
          for (const chunk of chunks) {
            const n = Math.min(chunk.length, entry.size - written);
            fileBytes.set(bytes.subarray(chunk.offset, chunk.offset + n), written);
            written += n;
            if (written >= entry.size) break;
          }
          const fileOffset = chunks.length ? chunks[0].offset : partitionOffset;
          entries.push({
            path: normalizePath(entry.path.toLowerCase()),
            offset: fileOffset,
            length: entry.size,
            crc32: crc32(fileBytes),
            flags: 0,
            type: guessType(entry.path),
            chunks,
          });
        }
      }
    };
    walk('/', rootOffset, rootDirSectors * bytesPerSector);

    if (!entries.some(entry => entry.path === '/cart/meta.jso' || entry.path === '/meta.jso' || entry.path === '/cart/meta.json' || entry.path === '/meta.json')) {
      lastReason = `partition ${i + 1} FAT parsed but no cart meta found; files=${entries.map(e => e.path).slice(0, 12).join(',')}`;
      continue;
    }
    const label = readFixedString(bytes, vbr + 43, 11).trim() || 'FAT16-CART';
    return new ImageFileSystem(bytes, {
      magic: 'FAT16',
      version: 1,
      sectorSize: bytesPerSector,
      flags: FLAG_CART,
      totalBytes: partitionBytes,
      dirOffset: rootOffset,
      dirBytes: rootDirSectors * bytesPerSector,
      dataOffset: partitionOffset + firstDataSector * bytesPerSector,
      entryCount: entries.length,
      createdUnix: 0,
      label,
      bootFile: '',
      filesystem: 'FAT16',
      partition: { index: i + 1, type, bootable: false, startLba, sectorCount: totalSectors, byteOffset: partitionOffset, byteLength: partitionBytes },
    }, entries, bytes);
  }

  parseFat16CartDisk.lastReason = lastReason;
  return null;
}

function createImage(options = {}) {
  const sectorSize = options.sectorSize || DEFAULT_SECTOR_SIZE;
  if (sectorSize < 256 || (sectorSize & (sectorSize - 1)) !== 0) {
    throw new Error('sectorSize must be a power of two and at least 256.');
  }

  const rawFiles = options.files || {};
  const items = Object.entries(rawFiles).map(([path, value]) => ({ path: normalizePath(path), bytes: asBytes(value) }));
  items.sort((a, b) => a.path.localeCompare(b.path));

  const typeFlag = options.type === 'system' ? FLAG_SYSTEM : options.type === 'cart' ? FLAG_CART : 0;
  const bootable = Boolean(options.bootable);
  const bootFile = bootable ? normalizePath(options.bootFile || '/boot/kernel.json') : '';
  if (bootable && !items.some(item => item.path === bootFile)) {
    throw new Error(`Bootable image must contain bootFile ${bootFile}.`);
  }

  if (!bootable && options.bootFile) {
    throw new Error('Non-bootable cartridge images cannot define bootFile.');
  }

  const directoryBytes = align(Math.max(sectorSize, items.length * ENTRY_SIZE), sectorSize);
  const dataOffset = HEADER_SIZE + directoryBytes;
  let cursor = dataOffset;
  const entries = [];
  for (const item of items) {
    cursor = align(cursor, 16);
    entries.push({
      path: item.path,
      offset: cursor,
      length: item.bytes.length,
      crc32: crc32(item.bytes),
      flags: 0,
      type: guessType(item.path),
      bytes: item.bytes,
    });
    cursor += item.bytes.length;
  }

  const totalBytes = align(cursor, sectorSize);
  const image = new Uint8Array(totalBytes);
  const view = new DataView(image.buffer);

  writeFixedString(image, 0, 8, MAGIC);
  view.setUint16(8, VERSION, true);
  view.setUint16(10, sectorSize, true);
  view.setUint32(12, (bootable ? FLAG_BOOTABLE : 0) | typeFlag, true);
  view.setUint32(16, totalBytes, true);
  view.setUint32(20, HEADER_SIZE, true);
  view.setUint32(24, directoryBytes, true);
  view.setUint32(28, dataOffset, true);
  view.setUint32(32, entries.length, true);
  view.setUint32(36, Math.floor(Date.now() / 1000), true);
  writeFixedString(image, 40, 48, options.label || 'UNTITLED');
  writeFixedString(image, 88, 64, bootFile);

  let dir = HEADER_SIZE;
  for (const entry of entries) {
    writeFixedString(image, dir, PATH_BYTES, entry.path);
    view.setUint32(dir + 96, entry.offset, true);
    view.setUint32(dir + 100, entry.length, true);
    view.setUint32(dir + 104, entry.crc32, true);
    view.setUint32(dir + 108, entry.flags, true);
    view.setUint32(dir + 112, entry.type, true);
    image.set(entry.bytes, entry.offset);
    dir += ENTRY_SIZE;
  }

  if (options.partitioned) {
    if (bootable) throw new Error('Partitioned cart images must not be bootable.');
    return wrapImageInMbrPartition(image, {
      sectorSize,
      diskLabel: options.diskLabel || `${options.label || 'UNTITLED'} CART DISK`,
      partitionStartLba: options.partitionStartLba,
      partitionType: options.partitionType,
    });
  }

  return image;
}

function parseImage(input) {
  const sourceBytes = input instanceof Uint8Array ? input : new Uint8Array(input);
  if (sourceBytes.byteLength < HEADER_SIZE) throw new Error('Image is too small.');
  const directFatCart = parseFat16CartDisk(sourceBytes);
  if (directFatCart) return directFatCart;

  const found = findImagePayload(sourceBytes);
  const bytes = found.bytes;
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  const magic = readMagic(bytes);
  if (!isSupportedMagic(magic)) {
    const fatCart = parseFat16CartDisk(sourceBytes);
    if (fatCart) return fatCart;
    const fatReason = parseFat16CartDisk.lastReason ? ` FAT16 reason: ${parseFat16CartDisk.lastReason}.` : '';
    throw new Error(`Bad image magic: ${JSON.stringify(magic)}. Not a M16IMG container and no readable non-bootable FAT16 cart partition was found.${fatReason}`);
  }
  const version = view.getUint16(8, true);
  if (version !== VERSION) throw new Error(`Unsupported image version ${version}.`);
  const sectorSize = view.getUint16(10, true);
  const flags = view.getUint32(12, true);
  const totalBytes = view.getUint32(16, true);
  const dirOffset = view.getUint32(20, true);
  const dirBytes = view.getUint32(24, true);
  const dataOffset = view.getUint32(28, true);
  const entryCount = view.getUint32(32, true);
  const createdUnix = view.getUint32(36, true);
  const label = readFixedString(bytes, 40, 48);
  const bootFile = readFixedString(bytes, 88, 64);

  if (totalBytes > bytes.byteLength) throw new Error('Image header totalBytes is larger than actual file.');
  if (dirOffset !== HEADER_SIZE) throw new Error('Invalid directory offset.');
  if (dirBytes < entryCount * ENTRY_SIZE) throw new Error('Directory too small for entry count.');
  if (dataOffset < dirOffset + dirBytes) throw new Error('Invalid data offset.');

  const entries = [];
  for (let i = 0; i < entryCount; i++) {
    const off = dirOffset + i * ENTRY_SIZE;
    const path = readFixedString(bytes, off, PATH_BYTES);
    const offset = view.getUint32(off + 96, true);
    const length = view.getUint32(off + 100, true);
    const storedCrc = view.getUint32(off + 104, true);
    const fileFlags = view.getUint32(off + 108, true);
    const type = view.getUint32(off + 112, true);
    if (!path.startsWith('/')) throw new Error(`Invalid image path entry: ${path}`);
    if (offset < dataOffset || offset + length > totalBytes) throw new Error(`Invalid data span for ${path}.`);
    entries.push({ path, offset, length, crc32: storedCrc, flags: fileFlags, type });
  }

  return new ImageFileSystem(bytes.slice(0, totalBytes), {
    magic,
    version,
    sectorSize,
    flags,
    totalBytes,
    dirOffset,
    dirBytes,
    dataOffset,
    entryCount,
    createdUnix,
    label,
    bootFile,
    partition: found.partition,
  }, entries, found.partition ? sourceBytes : bytes.slice(0, totalBytes));
}

function imageInfo(input) {
  const fs = input && input.list ? input : parseImage(input);
  return {
    label: fs.header.label,
    bootable: fs.isBootable(),
    system: fs.isSystem(),
    cart: fs.isCart(),
    bootFile: fs.header.bootFile,
    partitioned: fs.isPartitioned(),
    partition: fs.header.partition,
    filesystem: fs.header.filesystem || 'M16IMG',
    sectorSize: fs.header.sectorSize,
    totalBytes: fs.header.totalBytes,
    diskBytes: fs.diskBytes.length,
    entries: fs.entries.map(({ path, length, crc32, type }) => ({ path, length, crc32: crc32.toString(16).padStart(8, '0'), type })),
  };
}

function saveBytesAsDownload(bytes, filename) {
  const blob = new Blob([bytes], { type: 'application/octet-stream' });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = filename;
  document.body.appendChild(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(url), 5000);
}

function guessType(path) {
  const lower = path.toLowerCase();
  if (lower.endsWith('.json')) return 1;
  if (lower.endsWith('.js')) return 2;
  if (lower.endsWith('.bin')) return 3;
  if (lower.endsWith('.txt') || lower.endsWith('.md')) return 4;
  return 0;
}

const ImageFlags = Object.freeze({
  BOOTABLE: FLAG_BOOTABLE,
  CART: FLAG_CART,
  SYSTEM: FLAG_SYSTEM,
});

const ImageFormat = Object.freeze({
  MAGIC,
  VERSION,
  HEADER_SIZE,
  ENTRY_SIZE,
  PATH_BYTES,
  DEFAULT_SECTOR_SIZE,
  MBR_SIZE,
  M16_PARTITION_TYPE,
  FAT16_PARTITION_TYPE,
  DEFAULT_PARTITION_START_LBA,
});



// ===== display.mjs =====
const WIDTH = 128;
const HEIGHT = 128;
const CANVAS_SCALE = 4;
const SYSTEM_NAME = 'Mega 16';
const SYSTEM_SHORT = 'M16';
const COLOR_DEPTH_BITS = 16;

const PICO_PALETTE = [
  0x000000ff, 0x1d2b53ff, 0x7e2553ff, 0x008751ff,
  0xab5236ff, 0x5f574fff, 0xc2c3c7ff, 0xfff1e8ff,
  0xff004dff, 0xffa300ff, 0xffec27ff, 0x00e436ff,
  0x29adffff, 0x83769cff, 0xff77a8ff, 0xffccaaff,
];

const FONT = {
  ' ': ['000','000','000','000','000'], '!': ['010','010','010','000','010'], '"': ['101','101','000','000','000'], '#': ['101','111','101','111','101'],
  '$': ['111','110','011','111','010'], '%': ['101','001','010','100','101'], '&': ['010','101','010','101','011'], "'": ['010','010','000','000','000'],
  '(': ['001','010','010','010','001'], ')': ['100','010','010','010','100'], '*': ['000','101','010','101','000'], '+': ['000','010','111','010','000'],
  ',': ['000','000','000','010','100'], '-': ['000','000','111','000','000'], '.': ['000','000','000','000','010'], '/': ['001','001','010','100','100'],
  '0': ['111','101','101','101','111'], '1': ['010','110','010','010','111'], '2': ['111','001','111','100','111'], '3': ['111','001','111','001','111'],
  '4': ['101','101','111','001','001'], '5': ['111','100','111','001','111'], '6': ['111','100','111','101','111'], '7': ['111','001','010','010','010'],
  '8': ['111','101','111','101','111'], '9': ['111','101','111','001','111'], ':': ['000','010','000','010','000'], ';': ['000','010','000','010','100'],
  '<': ['001','010','100','010','001'], '=': ['000','111','000','111','000'], '>': ['100','010','001','010','100'], '?': ['111','001','011','000','010'],
  '@': ['111','101','101','100','111'], 'A': ['010','101','111','101','101'], 'B': ['110','101','110','101','110'], 'C': ['111','100','100','100','111'],
  'D': ['110','101','101','101','110'], 'E': ['111','100','110','100','111'], 'F': ['111','100','110','100','100'], 'G': ['111','100','101','101','111'],
  'H': ['101','101','111','101','101'], 'I': ['111','010','010','010','111'], 'J': ['001','001','001','101','111'], 'K': ['101','101','110','101','101'],
  'L': ['100','100','100','100','111'], 'M': ['101','111','111','101','101'], 'N': ['101','111','111','111','101'], 'O': ['111','101','101','101','111'],
  'P': ['111','101','111','100','100'], 'Q': ['111','101','101','111','001'], 'R': ['111','101','111','110','101'], 'S': ['111','100','111','001','111'],
  'T': ['111','010','010','010','010'], 'U': ['101','101','101','101','111'], 'V': ['101','101','101','101','010'], 'W': ['101','101','111','111','101'],
  'X': ['101','101','010','101','101'], 'Y': ['101','101','010','010','010'], 'Z': ['111','001','010','100','111'], '[': ['011','010','010','010','011'],
  '\\': ['100','100','010','001','001'], ']': ['110','010','010','010','110'], '^': ['010','101','000','000','000'], '_': ['000','000','000','000','111'],
  '`': ['100','010','000','000','000'], '{': ['001','010','110','010','001'], '|': ['010','010','010','010','010'], '}': ['100','010','011','010','100'], '~': ['000','011','110','000','000'],
};

class Display {
  constructor(canvas) {
    this.canvas = canvas;
    this.ctx = canvas.getContext('2d', { alpha: false, desynchronized: true });
    this.canvas.width = WIDTH * CANVAS_SCALE;
    this.canvas.height = HEIGHT * CANVAS_SCALE;
    this.ctx.imageSmoothingEnabled = false;
    this.backCanvas = document.createElement('canvas');
    this.backCanvas.width = WIDTH;
    this.backCanvas.height = HEIGHT;
    this.backCtx = this.backCanvas.getContext('2d', { alpha: false, desynchronized: true });
    this.palette = PICO_PALETTE.slice();
    this.palMap = Array.from({ length: 16 }, (_, i) => i);
    this.transparent = new Set([0]);
    this.pixels = new Uint16Array(WIDTH * HEIGHT);
    this.image = this.ctx.createImageData(WIDTH, HEIGHT);
    this.clipX = 0;
    this.clipY = 0;
    this.clipW = WIDTH;
    this.clipH = HEIGHT;
    this.cameraX = 0;
    this.cameraY = 0;
    this.cursorX = 0;
    this.cursorY = 0;
    this.color = 7;
  }

  reset() {
    this.palette = PICO_PALETTE.slice();
    this.palMap = Array.from({ length: 16 }, (_, i) => i);
    this.transparent = new Set([0]);
    this.clip();
    this.camera(0, 0);
    this.color = 7;
    this.cursorX = 0;
    this.cursorY = 0;
    this.cls(0);
  }

  setPalette(colors) {
    if (!Array.isArray(colors) || colors.length !== 16) throw new Error('Palette must be an array of 16 RGBA integers.');
    this.palette = colors.map(v => v >>> 0);
  }

  cls(color = 0) {
    this.pixels.fill(this.mapColor(color));
    this.cursorX = 0;
    this.cursorY = 0;
  }

  camera(x = 0, y = 0) {
    this.cameraX = Math.trunc(x);
    this.cameraY = Math.trunc(y);
  }

  clip(x = 0, y = 0, w = WIDTH, h = HEIGHT) {
    this.clipX = Math.max(0, Math.trunc(x));
    this.clipY = Math.max(0, Math.trunc(y));
    this.clipW = Math.max(0, Math.min(WIDTH - this.clipX, Math.trunc(w)));
    this.clipH = Math.max(0, Math.min(HEIGHT - this.clipY, Math.trunc(h)));
  }

  pal(c0 = null, c1 = null) {
    if (c0 === null) {
      this.palMap = Array.from({ length: 16 }, (_, i) => i);
      return;
    }
    this.palMap[c0 & 15] = c1 & 15;
  }

  palt(c = null, transparent = true) {
    if (c === null) {
      this.transparent = new Set([0]);
      return;
    }
    if (transparent) this.transparent.add(c & 15);
    else this.transparent.delete(c & 15);
  }

  pset(x, y, color = this.color) {
    x = Math.trunc(x - this.cameraX);
    y = Math.trunc(y - this.cameraY);
    if (!this.inClip(x, y)) return;
    this.pixels[y * WIDTH + x] = this.mapColor(color);
  }

  rawPset(x, y, color = this.color) {
    x = Math.trunc(x);
    y = Math.trunc(y);
    if (!this.inClip(x, y)) return;
    this.pixels[y * WIDTH + x] = this.mapColor(color);
  }

  pget(x, y) {
    x = Math.trunc(x - this.cameraX);
    y = Math.trunc(y - this.cameraY);
    if (x < 0 || y < 0 || x >= WIDTH || y >= HEIGHT) return 0;
    return this.pixels[y * WIDTH + x];
  }

  line(x0, y0, x1, y1, color = this.color) {
    x0 = Math.trunc(x0); y0 = Math.trunc(y0); x1 = Math.trunc(x1); y1 = Math.trunc(y1);
    let dx = Math.abs(x1 - x0), sx = x0 < x1 ? 1 : -1;
    let dy = -Math.abs(y1 - y0), sy = y0 < y1 ? 1 : -1;
    let err = dx + dy;
    while (true) {
      this.pset(x0, y0, color);
      if (x0 === x1 && y0 === y1) break;
      const e2 = 2 * err;
      if (e2 >= dy) { err += dy; x0 += sx; }
      if (e2 <= dx) { err += dx; y0 += sy; }
    }
  }

  rect(x0, y0, x1, y1, color = this.color) {
    this.line(x0, y0, x1, y0, color);
    this.line(x1, y0, x1, y1, color);
    this.line(x1, y1, x0, y1, color);
    this.line(x0, y1, x0, y0, color);
  }

  rectfill(x0, y0, x1, y1, color = this.color) {
    x0 = Math.trunc(x0); y0 = Math.trunc(y0); x1 = Math.trunc(x1); y1 = Math.trunc(y1);
    if (x1 < x0) [x0, x1] = [x1, x0];
    if (y1 < y0) [y0, y1] = [y1, y0];
    for (let y = y0; y <= y1; y++) for (let x = x0; x <= x1; x++) this.pset(x, y, color);
  }

  circ(xc, yc, r, color = this.color) {
    xc = Math.trunc(xc); yc = Math.trunc(yc); r = Math.trunc(r);
    let x = r, y = 0, err = 0;
    while (x >= y) {
      this.pset(xc + x, yc + y, color); this.pset(xc + y, yc + x, color);
      this.pset(xc - y, yc + x, color); this.pset(xc - x, yc + y, color);
      this.pset(xc - x, yc - y, color); this.pset(xc - y, yc - x, color);
      this.pset(xc + y, yc - x, color); this.pset(xc + x, yc - y, color);
      y++;
      if (err <= 0) err += 2 * y + 1;
      if (err > 0) { x--; err -= 2 * x + 1; }
    }
  }

  circfill(xc, yc, r, color = this.color) {
    xc = Math.trunc(xc); yc = Math.trunc(yc); r = Math.trunc(r);
    for (let y = -r; y <= r; y++) {
      const span = Math.floor(Math.sqrt(r * r - y * y));
      for (let x = -span; x <= span; x++) this.pset(xc + x, yc + y, color);
    }
  }

  oval(x0, y0, x1, y1, color = this.color, fill = false) {
    x0 = Math.trunc(x0); y0 = Math.trunc(y0); x1 = Math.trunc(x1); y1 = Math.trunc(y1);
    const cx = (x0 + x1) / 2, cy = (y0 + y1) / 2;
    const rx = Math.abs(x1 - x0) / 2, ry = Math.abs(y1 - y0) / 2;
    if (rx === 0 || ry === 0) return;
    if (fill) {
      for (let y = Math.floor(y0); y <= Math.ceil(y1); y++) {
        const yy = (y - cy) / ry;
        const span = rx * Math.sqrt(Math.max(0, 1 - yy * yy));
        for (let x = Math.ceil(cx - span); x <= Math.floor(cx + span); x++) this.pset(x, y, color);
      }
      return;
    }
    const steps = Math.max(24, Math.ceil(Math.PI * Math.max(rx, ry) * 2));
    let px = cx + rx, py = cy;
    for (let i = 1; i <= steps; i++) {
      const a = (i / steps) * Math.PI * 2;
      const x = cx + Math.cos(a) * rx;
      const y = cy + Math.sin(a) * ry;
      this.line(px, py, x, y, color);
      px = x; py = y;
    }
  }

  print(text, x = this.cursorX, y = this.cursorY, color = this.color) {
    text = String(text);
    let cx = Math.trunc(x), cy = Math.trunc(y);
    const startX = cx;
    for (const ch of text) {
      if (ch === '\n') { cx = startX; cy += 6; continue; }
      this.char(ch, cx, cy, color);
      cx += 4;
    }
    this.cursorX = cx;
    this.cursorY = cy;
    return text.length * 4;
  }

  char(ch, x, y, color) {
    let glyph = FONT[ch] || FONT[ch.toUpperCase()] || FONT['?'];
    for (let gy = 0; gy < glyph.length; gy++) {
      const row = glyph[gy];
      for (let gx = 0; gx < row.length; gx++) if (row[gx] === '1') this.pset(x + gx, y + gy, color);
    }
  }

  sprite(spriteSheet, n, x, y, w = 1, h = 1, flipX = false, flipY = false) {
    if (!spriteSheet) return;
    const sx0 = (n % 16) * 8;
    const sy0 = Math.floor(n / 16) * 8;
    const width = Math.trunc(w) * 8;
    const height = Math.trunc(h) * 8;
    for (let yy = 0; yy < height; yy++) {
      for (let xx = 0; xx < width; xx++) {
        const sx = sx0 + (flipX ? width - 1 - xx : xx);
        const sy = sy0 + (flipY ? height - 1 - yy : yy);
        const c = spriteSheet.get(sx, sy);
        if (!(c <= 15 && this.transparent.has(c))) this.pset(x + xx, y + yy, c);
      }
    }
  }

  sspr(spriteSheet, sx, sy, sw, sh, dx, dy, dw = sw, dh = sh, flipX = false, flipY = false) {
    if (!spriteSheet) return;
    for (let yy = 0; yy < dh; yy++) {
      for (let xx = 0; xx < dw; xx++) {
        const u = Math.floor((xx / dw) * sw);
        const v = Math.floor((yy / dh) * sh);
        const px = sx + (flipX ? sw - 1 - u : u);
        const py = sy + (flipY ? sh - 1 - v : v);
        const c = spriteSheet.get(px, py);
        if (!(c <= 15 && this.transparent.has(c))) this.pset(dx + xx, dy + yy, c);
      }
    }
  }

  map(mapData, spriteSheet, cellX = 0, cellY = 0, screenX = 0, screenY = 0, cellW = 16, cellH = 16, layerMask = 0) {
    if (!mapData || !spriteSheet) return;
    for (let my = 0; my < cellH; my++) {
      for (let mx = 0; mx < cellW; mx++) {
        const id = mapData.get(cellX + mx, cellY + my);
        if (id === 0 && layerMask !== 0) continue;
        this.sprite(spriteSheet, id, screenX + mx * 8, screenY + my * 8);
      }
    }
  }

  render() {
    const data = this.image.data;
    for (let i = 0, j = 0; i < this.pixels.length; i++, j += 4) {
      const pixel = this.pixels[i] & 0xffff;
      const rgba = Display.rgb565ToRgba(pixel);
      data[j] = (rgba >>> 24) & 0xFF;
      data[j + 1] = (rgba >>> 16) & 0xFF;
      data[j + 2] = (rgba >>> 8) & 0xFF;
      data[j + 3] = rgba & 0xFF;
    }
    this.backCtx.putImageData(this.image, 0, 0);
    this.ctx.clearRect(0, 0, this.canvas.width, this.canvas.height);
    this.ctx.imageSmoothingEnabled = false;
    this.ctx.drawImage(this.backCanvas, 0, 0, this.canvas.width, this.canvas.height);
  }

  inClip(x, y) {
    return x >= this.clipX && y >= this.clipY && x < this.clipX + this.clipW && y < this.clipY + this.clipH;
  }

  mapColor(color) {
    color = Number(color) || 0;
    if (color > 0xffff) return color & 0xffff;
    if (color >= 0 && color <= 15) return Display.rgbaToRgb565(this.palette[this.palMap[color & 15] & 15]);
    return color & 0xffff;
  }

  static rgb565(r = 0, g = 0, b = 0) {
    r = Math.max(0, Math.min(255, Math.trunc(r)));
    g = Math.max(0, Math.min(255, Math.trunc(g)));
    b = Math.max(0, Math.min(255, Math.trunc(b)));
    return ((r & 0xf8) << 8) | ((g & 0xf8) << 3) | (b >>> 3);
  }

  static rgbaToRgb565(rgba) {
    return Display.rgb565((rgba >>> 24) & 0xff, (rgba >>> 16) & 0xff, (rgba >>> 8) & 0xff);
  }

  static rgb565ToRgba(value) {
    const r5 = (value >>> 11) & 0x1f;
    const g6 = (value >>> 5) & 0x3f;
    const b5 = value & 0x1f;
    const r = (r5 << 3) | (r5 >>> 2);
    const g = (g6 << 2) | (g6 >>> 4);
    const b = (b5 << 3) | (b5 >>> 2);
    return ((r & 0xff) << 24) | ((g & 0xff) << 16) | ((b & 0xff) << 8) | 0xff;
  }
}

class SpriteSheet {
  constructor(bytes = null) {
    this.width = 128;
    this.height = 128;
    this.pixels = new Uint16Array(this.width * this.height);
    if (bytes) this.load(bytes);
  }

  load(bytes) {
    const src = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes);
    if (src.length === this.pixels.length * 2) {
      const view = new DataView(src.buffer, src.byteOffset, src.byteLength);
      for (let i = 0; i < this.pixels.length; i++) this.pixels[i] = view.getUint16(i * 2, true);
      return;
    }
    if (src.length === this.pixels.length) {
      for (let i = 0; i < src.length; i++) this.pixels[i] = src[i] & 15;
      return;
    }
    if (src.length === this.pixels.length / 2) {
      for (let i = 0, j = 0; i < src.length; i++) {
        this.pixels[j++] = src[i] & 15;
        this.pixels[j++] = (src[i] >>> 4) & 15;
      }
      return;
    }
    throw new Error(`Sprite sheet size must be ${this.pixels.length * 2} RGB565 bytes, ${this.pixels.length} indexed bytes, or ${this.pixels.length / 2} packed bytes.`);
  }

  dumpPacked() {
    const out = new Uint8Array(this.pixels.length / 2);
    for (let i = 0, j = 0; i < out.length; i++) out[i] = (this.pixels[j++] & 15) | ((this.pixels[j++] & 15) << 4);
    return out;
  }

  dump16() {
    const out = new Uint8Array(this.pixels.length * 2);
    const view = new DataView(out.buffer);
    for (let i = 0; i < this.pixels.length; i++) view.setUint16(i * 2, this.pixels[i] & 0xffff, true);
    return out;
  }

  get(x, y) {
    x = Math.trunc(x); y = Math.trunc(y);
    if (x < 0 || y < 0 || x >= this.width || y >= this.height) return 0;
    return this.pixels[y * this.width + x] & 0xffff;
  }

  set(x, y, color) {
    x = Math.trunc(x); y = Math.trunc(y);
    if (x < 0 || y < 0 || x >= this.width || y >= this.height) return;
    this.pixels[y * this.width + x] = color & 0xffff;
  }

  drawSprite(index, pattern) {
    const sx = (index % 16) * 8;
    const sy = Math.floor(index / 16) * 8;
    for (let y = 0; y < Math.min(8, pattern.length); y++) {
      for (let x = 0; x < Math.min(8, pattern[y].length); x++) {
        const v = pattern[y][x];
        const c = typeof v === 'string' ? parseInt(v, 16) : v;
        if (!Number.isNaN(c)) this.set(sx + x, sy + y, c);
      }
    }
  }
}

class TileMap {
  constructor(bytes = null) {
    this.width = 128;
    this.height = 64;
    this.cells = new Uint8Array(this.width * this.height);
    if (bytes) this.load(bytes);
  }

  load(bytes) {
    const src = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes);
    if (src.length !== this.cells.length) throw new Error(`Map size must be ${this.cells.length} bytes.`);
    this.cells.set(src);
  }

  dump() {
    return new Uint8Array(this.cells);
  }

  get(x, y) {
    x = Math.trunc(x); y = Math.trunc(y);
    if (x < 0 || y < 0 || x >= this.width || y >= this.height) return 0;
    return this.cells[y * this.width + x];
  }

  set(x, y, value) {
    x = Math.trunc(x); y = Math.trunc(y);
    if (x < 0 || y < 0 || x >= this.width || y >= this.height) return;
    this.cells[y * this.width + x] = value & 255;
  }
}



// ===== input.mjs =====
const Buttons = Object.freeze({ LEFT: 0, RIGHT: 1, UP: 2, DOWN: 3, O: 4, X: 5, MENU: 6, PAUSE: 7 });

const KEY_TO_BUTTON = new Map([
  ['ArrowLeft', Buttons.LEFT], ['KeyA', Buttons.LEFT],
  ['ArrowRight', Buttons.RIGHT], ['KeyD', Buttons.RIGHT],
  ['ArrowUp', Buttons.UP], ['KeyW', Buttons.UP],
  ['ArrowDown', Buttons.DOWN], ['KeyS', Buttons.DOWN],
  ['KeyZ', Buttons.O], ['KeyJ', Buttons.O], ['Space', Buttons.O],
  ['KeyX', Buttons.X], ['KeyK', Buttons.X], ['Enter', Buttons.X],
  ['Escape', Buttons.MENU], ['Tab', Buttons.MENU],
  ['ShiftLeft', Buttons.PAUSE], ['ShiftRight', Buttons.PAUSE],
]);

class InputState {
  constructor(target = window, canvas = null) {
    this.target = target;
    this.canvas = canvas;
    this.down = new Uint8Array(8);
    this.prev = new Uint8Array(8);
    this.pressedLatch = new Uint8Array(8);
    this.keyDown = new Set();
    this.keyPressedLatch = new Set();
    this.mouseX = 0;
    this.mouseY = 0;
    this.mouseDx = 0;
    this.mouseDy = 0;
    this.mouseButtons = 0;
    this.mousePressedLatch = 0;
    this.pointerLocked = false;
    this.enabled = false;
    this.onKeyDown = this.onKeyDown.bind(this);
    this.onKeyUp = this.onKeyUp.bind(this);
    this.onMouseMove = this.onMouseMove.bind(this);
    this.onMouseDown = this.onMouseDown.bind(this);
    this.onMouseUp = this.onMouseUp.bind(this);
    this.onPointerLockChange = this.onPointerLockChange.bind(this);
    this.onBlur = this.onBlur.bind(this);
  }

  attach() {
    if (this.enabled) return;
    this.enabled = true;
    this.target.addEventListener('keydown', this.onKeyDown);
    this.target.addEventListener('keyup', this.onKeyUp);
    this.target.addEventListener('mousemove', this.onMouseMove);
    this.target.addEventListener('mousedown', this.onMouseDown);
    this.target.addEventListener('mouseup', this.onMouseUp);
    document.addEventListener('pointerlockchange', this.onPointerLockChange);
    window.addEventListener('blur', this.onBlur);
  }

  detach() {
    if (!this.enabled) return;
    this.enabled = false;
    this.target.removeEventListener('keydown', this.onKeyDown);
    this.target.removeEventListener('keyup', this.onKeyUp);
    this.target.removeEventListener('mousemove', this.onMouseMove);
    this.target.removeEventListener('mousedown', this.onMouseDown);
    this.target.removeEventListener('mouseup', this.onMouseUp);
    document.removeEventListener('pointerlockchange', this.onPointerLockChange);
    window.removeEventListener('blur', this.onBlur);
  }

  onKeyDown(event) {
    const btn = KEY_TO_BUTTON.get(event.code);
    if (!this.keyDown.has(event.code)) this.keyPressedLatch.add(event.code);
    this.keyDown.add(event.code);
    if (btn !== undefined) {
      if (!this.down[btn]) this.pressedLatch[btn] = 1;
      this.down[btn] = 1;
      event.preventDefault();
    }
  }

  onKeyUp(event) {
    const btn = KEY_TO_BUTTON.get(event.code);
    this.keyDown.delete(event.code);
    if (btn !== undefined) {
      this.down[btn] = 0;
      event.preventDefault();
    }
  }

  onMouseMove(event) {
    this.mouseDx += event.movementX || 0;
    this.mouseDy += event.movementY || 0;
    const rect = this.canvas?.getBoundingClientRect?.();
    if (rect) {
      this.mouseX = Math.max(0, Math.min(WIDTH - 1, (event.clientX - rect.left) * WIDTH / rect.width));
      this.mouseY = Math.max(0, Math.min(HEIGHT - 1, (event.clientY - rect.top) * HEIGHT / rect.height));
    } else {
      this.mouseX = event.clientX || 0;
      this.mouseY = event.clientY || 0;
    }
  }

  onMouseDown(event) {
    const bit = 1 << (event.button & 7);
    if (!(this.mouseButtons & bit)) this.mousePressedLatch |= bit;
    this.mouseButtons |= bit;
    if (this.canvas && event.target === this.canvas) event.preventDefault();
  }

  onMouseUp(event) {
    this.mouseButtons &= ~(1 << (event.button & 7));
    if (this.canvas && event.target === this.canvas) event.preventDefault();
  }

  onPointerLockChange() {
    this.pointerLocked = Boolean(this.canvas && document.pointerLockElement === this.canvas);
  }

  onBlur() {
    this.down.fill(0);
    this.prev.fill(0);
    this.pressedLatch.fill(0);
    this.keyDown.clear();
    this.keyPressedLatch.clear();
    this.mouseButtons = 0;
    this.mousePressedLatch = 0;
    this.mouseDx = 0;
    this.mouseDy = 0;
  }

  frameStart() {
    for (let i = 0; i < this.down.length; i++) {
      if (this.down[i] && !this.prev[i]) this.pressedLatch[i] = 1;
    }
  }

  frameEnd() {
    this.prev.set(this.down);
    this.pressedLatch.fill(0);
    this.keyPressedLatch.clear();
    this.mousePressedLatch = 0;
    this.mouseDx = 0;
    this.mouseDy = 0;
  }

  btn(index) {
    return Boolean(this.down[index & 7]);
  }

  btnp(index) {
    return Boolean(this.pressedLatch[index & 7]);
  }

  key(code) {
    return this.keyDown.has(String(code));
  }

  keyp(code) {
    return this.keyPressedLatch.has(String(code));
  }

  mouse() {
    return {
      x: this.mouseX,
      y: this.mouseY,
      dx: this.mouseDx,
      dy: this.mouseDy,
      buttons: this.mouseButtons,
      locked: this.pointerLocked,
    };
  }

  mousep(button = 0) {
    return Boolean(this.mousePressedLatch & (1 << (button & 7)));
  }

  lockMouse() {
    if (!this.canvas?.requestPointerLock) return false;
    this.canvas.requestPointerLock();
    return true;
  }
}



// ===== audio.mjs =====
class AudioHost {
  constructor() {
    this.context = null;
    this.masterGain = null;
    this.enabled = true;
  }

  ensure() {
    if (!this.enabled) return null;
    if (!this.context) {
      const AudioContext = window.AudioContext || window.webkitAudioContext;
      if (!AudioContext) return null;
      this.context = new AudioContext();
      this.masterGain = this.context.createGain();
      this.masterGain.gain.value = 0.12;
      this.masterGain.connect(this.context.destination);
    }
    if (this.context.state === 'suspended') this.context.resume();
    return this.context;
  }

  beep(freq = 440, duration = 0.08, wave = 'square', volume = 0.8) {
    const ctx = this.ensure();
    if (!ctx) return;
    const now = ctx.currentTime;
    const osc = ctx.createOscillator();
    const gain = ctx.createGain();
    osc.type = wave;
    osc.frequency.setValueAtTime(Math.max(20, Math.min(20000, freq)), now);
    gain.gain.setValueAtTime(Math.max(0, Math.min(1, volume)), now);
    gain.gain.exponentialRampToValueAtTime(0.001, now + Math.max(0.01, duration));
    osc.connect(gain);
    gain.connect(this.masterGain);
    osc.start(now);
    osc.stop(now + duration + 0.02);
  }

  sfx(id = 0, note = 48, duration = 0.08) {
    const scale = [0, 2, 3, 5, 7, 8, 10];
    const octave = Math.floor(note / 12);
    const degree = note % 7;
    const semitone = scale[((degree % 7) + 7) % 7] + octave * 12;
    const freq = 220 * Math.pow(2, (semitone - 33) / 12);
    const waves = ['square', 'triangle', 'sawtooth', 'sine'];
    this.beep(freq, duration, waves[id & 3], 0.7);
  }
}



// ===== mega16ArmHost.mjs =====
class Mega16ArmHost {
  constructor(logger = console.log) {
    this.logger = logger;
    this.uc = null;
    this.engine = null;
    this.ready = false;
    this.selfTestResult = null;
  }

  detect() {
    this.uc = globalThis.uc || null;
    this.ready = Boolean(this.uc && this.uc.Unicorn);
    return this.ready;
  }

  selfTest() {
    if (!this.detect()) {
      this.selfTestResult = { ok: false, mode: 'fallback', message: 'Mega 16 ARM backend was not loaded; using JavaScript VM backend.' };
      return this.selfTestResult;
    }
    try {
      const uc = this.uc;
      const addr = 0x10000;
      const code = new Uint8Array([
        0x37, 0x00, 0xA0, 0xE3,
        0x03, 0x10, 0x42, 0xE0,
      ]);
      const e = new uc.Unicorn(uc.ARCH_ARM, uc.MODE_ARM);
      e.reg_write_i32(uc.ARM_REG_R2, 0x456);
      e.reg_write_i32(uc.ARM_REG_R3, 0x123);
      e.mem_map(addr, 4 * 1024, uc.PROT_ALL);
      e.mem_write(addr, Array.from(code));
      e.emu_start(addr, addr + code.length, 0, 0);
      const r0 = e.reg_read_i32(uc.ARM_REG_R0) >>> 0;
      const r1 = e.reg_read_i32(uc.ARM_REG_R1) >>> 0;
      this.engine = e;
      this.selfTestResult = {
        ok: r0 === 0x37 && r1 === 0x333,
        mode: 'mega16-arm',
        r0,
        r1,
        message: `Mega 16 ARM backend online: r0=0x${r0.toString(16)}, r1=0x${r1.toString(16)}.`,
      };
      return this.selfTestResult;
    } catch (error) {
      this.selfTestResult = { ok: false, mode: 'fallback', message: `Mega 16 ARM backend failed self-test: ${error.message}` };
      return this.selfTestResult;
    }
  }

  createArmMachine(memoryBase = 0x10000, memorySize = 1024 * 1024) {
    if (!this.detect()) throw new Error('Mega 16 ARM backend is not available.');
    const uc = this.uc;
    const e = new uc.Unicorn(uc.ARCH_ARM, uc.MODE_ARM);
    e.mem_map(memoryBase, memorySize, uc.PROT_ALL);
    return new Mega16ArmMachine(uc, e, memoryBase, memorySize);
  }
}

class Mega16ArmMachine {
  constructor(uc, engine, memoryBase, memorySize) {
    this.uc = uc;
    this.engine = engine;
    this.memoryBase = memoryBase;
    this.memorySize = memorySize;
  }

  load(offset, bytes) {
    const arr = bytes instanceof Uint8Array ? Array.from(bytes) : Array.from(new Uint8Array(bytes));
    const addr = this.memoryBase + offset;
    this.check(addr, arr.length);
    this.engine.mem_write(addr, arr);
    return addr;
  }

  start(offset, length, timeoutUsec = 0, instructionLimit = 0) {
    const begin = this.memoryBase + offset;
    const until = begin + length;
    this.check(begin, length);
    this.engine.emu_start(begin, until, timeoutUsec, instructionLimit);
  }

  reg(nameOrId, value = undefined) {
    const id = typeof nameOrId === 'number' ? nameOrId : this.registerId(nameOrId);
    if (value === undefined) return this.engine.reg_read_i32(id) >>> 0;
    this.engine.reg_write_i32(id, value >>> 0);
  }

  registerId(name) {
    const uc = this.uc;
    const key = `ARM_REG_${String(name).toUpperCase()}`;
    if (!(key in uc)) throw new Error(`Unknown ARM register ${name}.`);
    return uc[key];
  }

  check(addr, length) {
    if (addr < this.memoryBase || addr + length > this.memoryBase + this.memorySize) {
      throw new Error('Mega 16 ARM machine memory access is outside mapped memory.');
    }
  }
}



// ===== console.mjs =====

const API_BINDINGS = [
  'WIDTH','HEIGHT','BITS','SYSTEM','cls','camera','clip','color','rgb','pal','palt','pset','pget','line','rect','rectfill','circ','circfill','oval','ovalfill','print','spr','sspr','map','mget','mset','fget','fset','btn','btnp','key','keyp','mouse','mousep','lockmouse','sfx','beep','rnd','flr','ceil','abs','sgn','min','max','mid','sin','cos','atan2','sqrt','time','stat','reload','loadit','cartloaded','cartname','cartaddr','cartbytes','cartdata','dset','dget','memcpy','memset','peek','poke','trace'
];

class FantasyConsole {
  constructor({ canvas, log = console.log, fps = 30 }) {
    this.display = new Display(canvas);
    this.input = new InputState(window, canvas);
    this.audio = new AudioHost();
    this.unicorn = new Mega16ArmHost(message => this.log(message));
    this.log = log;
    this.fps = fps;
    this.system = null;
    this.cart = null;
    this.spriteSheet = new SpriteSheet();
    this.mapData = new TileMap();
    this.flags = new Uint8Array(256);
    this.ram = new Uint8Array(0x8000);
    this.persist = new Float64Array(64);
    this.running = false;
    this.frameHandle = 0;
    this.last = 0;
    this.accum = 0;
    this.frame = 0;
    this.startTime = performance.now();
    this.cartModule = null;
    this.systemModule = null;
    this.cartName = 'empty';
    this.cartError = null;
    this.stagedCart = null;
    this.systemBoot = { autoChainload: true, cartLoadAddress: 0x4000 };
    this.api = this.makeAPI();
  }

  bootSystem(imageBytes) {
    const fs = imageBytes && imageBytes.list ? imageBytes : parseImage(imageBytes);
    if (!fs.isSystem()) throw new Error('System image must be marked as system.');
    if (!fs.isBootable()) throw new Error('System image must be bootable.');
    const bootFile = fs.header.bootFile || '/sys/kernel.json';
    const kernel = fs.readJSON(bootFile);
    if (fs.has('/sys/palette.bin')) {
      const p = fs.readFile('/sys/palette.bin');
      if (p.length >= 64) {
        const palette = [];
        const view = new DataView(p.buffer, p.byteOffset, p.byteLength);
        for (let i = 0; i < 16; i++) palette.push(view.getUint32(i * 4, true));
        this.display.setPalette(palette);
      }
    } else {
      this.display.setPalette(PICO_PALETTE);
    }
    const boot = kernel.bootloader || {};
    this.systemBoot = {
      autoChainload: boot.autoChainload !== false,
      cartLoadAddress: Number.isFinite(boot.cartLoadAddress) ? boot.cartLoadAddress : 0x4000,
    };
    this.system = { fs, kernel };
    this.cartModule = null;
    this.cart = null;
    this.cartName = 'empty';
    this.display.reset();
    this.input.attach();
    this.compileSystem();
    const test = this.unicorn.selfTest();
    this.log(`booted ${fs.header.label}: ${kernel.name} ${kernel.version}`);
    this.log(`system bootloader ready: cart load address $${this.systemBoot.cartLoadAddress.toString(16)}, auto-chainload=${this.systemBoot.autoChainload}`);
    this.log(test.message);
    if (this.stagedCart && this.systemBoot.autoChainload) this.jumpToStagedCart();
    return kernel;
  }

  compileSystem() {
    this.systemModule = null;
    if (!this.system?.fs) return;
    const mainPath = this.system.kernel.main || '/sys/main.js';
    if (!this.system.fs.has(mainPath)) return;
    const source = this.system.fs.readText(mainPath);
    const destructure = `const {${API_BINDINGS.join(',')}} = api;`;
    const wrapped = `\n'use strict';\n${destructure}\nlet system = undefined;\n${source}\nreturn (typeof system === 'object' && system) ? system : {\n  _init: (typeof _init === 'function') ? _init : undefined,\n  _update: (typeof _update === 'function') ? _update : undefined,\n  _draw: (typeof _draw === 'function') ? _draw : undefined\n};\n//# sourceURL=${mainPath}`;
    try {
      this.systemModule = new Function('api', wrapped)(this.api) || null;
      if (typeof this.systemModule?._init === 'function') this.safeSystemCall('_init');
    } catch (error) {
      throw new Error(`System compile error in ${mainPath}: ${error.message}`);
    }
  }

  readCartImage(imageBytes) {
    const fs = imageBytes && imageBytes.list ? imageBytes : parseImage(imageBytes);
    if (!fs.isCart()) throw new Error('Cartridge image must be marked as cart.');
    if (fs.isBootable()) throw new Error('Cartridges in this remake must not contain bootable media.');
    const metaPath = fs.has('/cart/meta.jso') ? '/cart/meta.jso' : fs.has('/meta.jso') ? '/meta.jso' : fs.has('/cart/meta.json') ? '/cart/meta.json' : fs.has('/meta.json') ? '/meta.json' : '';
    const meta = metaPath ? fs.readJSON(metaPath) : { title: fs.header.label };
    const codePath = meta.main || '/cart/main.js';
    const code = fs.readText(codePath);
    const compiledAssembly = meta.assembly && fs.has(meta.assembly) ? fs.readText(meta.assembly) : '';
    const compiledBytecode = meta.bytecode && fs.has(meta.bytecode) ? fs.readFile(meta.bytecode) : null;
    if (compiledBytecode && !['M16BCASM', 'U8BCASM1'].includes(readFixedString(compiledBytecode, 0, 8))) {
      throw new Error(`Invalid compiled cart bytecode header in ${meta.bytecode}`);
    }
    return {
      fs,
      meta,
      codePath,
      code,
      compiledAssembly,
      compiledBytecode,
      diskBytes: fs.diskBytes || fs.bytes,
      name: meta.title || fs.header.label || 'cart',
    };
  }

  loadCart(imageBytes) {
    const staged = this.readCartImage(imageBytes);
    this.stageCart(staged);
    if (this.system && this.systemBoot.autoChainload) this.jumpToStagedCart();
    else this.log('cart staged; waiting for system bootloader jump');
  }

  stageCart(cart) {
    const bytes = cart.diskBytes || cart.fs.diskBytes || cart.fs.bytes;
    const loadAddress = this.systemBoot.cartLoadAddress;
    const copyLength = Math.max(0, Math.min(this.ram.length - loadAddress, bytes.length));
    if (copyLength > 0) this.ram.set(bytes.subarray(0, copyLength), loadAddress);
    this.stagedCart = {
      ...cart,
      memory: { loadAddress, size: bytes.length, copiedToRam: copyLength },
    };
    this.log(`loaded ${cart.name} into memory at $${loadAddress.toString(16)} (${copyLength}/${bytes.length} bytes mirrored to RAM)`);
  }

  jumpToStagedCart() {
    if (!this.system) throw new Error('No system image booted.');
    if (!this.stagedCart) throw new Error('No cartridge loaded into memory.');
    const cart = this.stagedCart;
    this.log(`system bootloader jumping to ${cart.name}`);
    this.spriteSheet = cart.fs.has('/cart/sprites.bin') ? new SpriteSheet(cart.fs.readFile('/cart/sprites.bin')) : new SpriteSheet();
    this.mapData = cart.fs.has('/cart/map.bin') ? new TileMap(cart.fs.readFile('/cart/map.bin')) : new TileMap();
    this.flags = cart.fs.has('/cart/flags.bin') ? normalizedBytes(cart.fs.readFile('/cart/flags.bin'), 256) : new Uint8Array(256);
    this.cart = cart;
    this.cartName = cart.name;
    this.compileCart(cart.code, cart.codePath);
    this.frame = 0;
    this.startTime = performance.now();
    this.display.reset();
    this.cartError = null;
    if (typeof this.cartModule._init === 'function') this.safeCall('_init');
    this.log(`running cart ${this.cartName}${cart.compiledBytecode ? ' with M16BC bytecode' : ''}`);
  }

  compileCart(source, filename = '/cart/main.js') {
    const destructure = `const {${API_BINDINGS.join(',')}} = api;`;
    const wrapped = `\n'use strict';\n${destructure}\nlet cart = undefined;\n${source}\nreturn (typeof cart === 'object' && cart) ? cart : {\n  _init: (typeof _init === 'function') ? _init : undefined,\n  _update: (typeof _update === 'function') ? _update : undefined,\n  _draw: (typeof _draw === 'function') ? _draw : undefined\n};\n//# sourceURL=${filename}`;
    try {
      this.cartModule = new Function('api', wrapped)(this.api) || {};
    } catch (error) {
      throw new Error(`Cart compile error in ${filename}: ${error.message}`);
    }
  }

  start() {
    if (!this.system) throw new Error('No system image booted.');
    this.running = true;
    this.last = performance.now();
    cancelAnimationFrame(this.frameHandle);
    this.frameHandle = requestAnimationFrame(t => this.tick(t));
  }

  stop() {
    this.running = false;
    cancelAnimationFrame(this.frameHandle);
  }

  clearCart() {
    this.cart = null;
    this.cartModule = null;
    this.cartName = 'empty';
    this.cartError = null;
    this.stagedCart = null;
    this.spriteSheet = new SpriteSheet();
    this.mapData = new TileMap();
    this.flags = new Uint8Array(256);
  }

  returnToSystem() {
    if (!this.cartModule) return false;
    this.cart = null;
    this.cartModule = null;
    this.cartName = 'empty';
    this.cartError = null;
    this.spriteSheet = new SpriteSheet();
    this.mapData = new TileMap();
    this.flags = new Uint8Array(256);
    this.display.reset();
    this.log('returned to system cartridge');
    return true;
  }

  reboot() {
    if (!this.stagedCart && !this.cart) return;
    if (!this.stagedCart && this.cart) this.stagedCart = this.cart;
    this.jumpToStagedCart();
    this.log(`rebooted ${this.cartName} through system bootloader`);
  }

  tick(now) {
    if (!this.running) return;
    const step = 1000 / this.fps;
    this.accum += Math.min(100, now - this.last);
    this.last = now;
    while (this.accum >= step) {
      this.updateFrame();
      this.accum -= step;
    }
    this.drawFrame();
    this.frameHandle = requestAnimationFrame(t => this.tick(t));
  }

  updateFrame() {
    this.input.frameStart();
    if (this.cartModule && typeof this.cartModule._update === 'function') this.safeCall('_update');
    else if (this.systemModule && typeof this.systemModule._update === 'function') this.safeSystemCall('_update');
    this.input.frameEnd();
    this.frame++;
  }

  drawFrame() {
    if (this.cartModule && typeof this.cartModule._draw === 'function') this.safeCall('_draw');
    else if (this.systemModule && typeof this.systemModule._draw === 'function') this.safeSystemCall('_draw');
    else this.drawBootScreen();
    this.display.render();
  }

  safeCall(name) {
    if (!this.cartModule || typeof this.cartModule[name] !== 'function') return;
    try {
      return this.cartModule[name]();
    } catch (error) {
      this.cartError = error;
      this.stop();
      this.display.cls(0);
      this.display.print('cart crashed', 2, 2, 8);
      this.display.print(error.message.slice(0, 60), 2, 10, 7);
      this.display.render();
      this.log(`${name} error: ${error.stack || error.message}`);
    }
  }

  safeSystemCall(name) {
    if (!this.systemModule || typeof this.systemModule[name] !== 'function') return;
    try {
      return this.systemModule[name]();
    } catch (error) {
      this.stop();
      this.display.cls(0);
      this.display.print('system crashed', 2, 2, 8);
      this.display.print(error.message.slice(0, 60), 2, 10, 7);
      this.display.render();
      this.log(`${name} system error: ${error.stack || error.message}`);
    }
  }

  drawBootScreen() {
    const d = this.display;
    d.cls(1);
    d.rect(0, 0, 127, 127, 12);
    d.print('MEGA 16', 46, 36, 10);
    d.print('NO CART LOADED :(', 31, 50, 8);
    d.print('load a cart image', 31, 62, 7);
    d.print('system: ' + (this.system?.kernel?.version || 'none'), 20, 74, 6);
  }

  makeAPI() {
    const fc = this;
    const api = {
      WIDTH, HEIGHT, BITS: COLOR_DEPTH_BITS, SYSTEM: SYSTEM_NAME,
      cls: c => fc.display.cls(c ?? 0),
      camera: (x = 0, y = 0) => fc.display.camera(x, y),
      clip: (x = 0, y = 0, w = WIDTH, h = HEIGHT) => fc.display.clip(x, y, w, h),
      color: c => { fc.display.color = Number(c) || 0; },
      rgb: (r = 0, g = 0, b = 0) => 0x10000 | Display.rgb565(r, g, b),
      pal: (c0 = null, c1 = null) => fc.display.pal(c0, c1),
      palt: (c = null, t = true) => fc.display.palt(c, t),
      pset: (x, y, c) => fc.display.pset(x, y, c ?? fc.display.color),
      pget: (x, y) => fc.display.pget(x, y),
      line: (x0, y0, x1, y1, c) => fc.display.line(x0, y0, x1, y1, c ?? fc.display.color),
      rect: (x0, y0, x1, y1, c) => fc.display.rect(x0, y0, x1, y1, c ?? fc.display.color),
      rectfill: (x0, y0, x1, y1, c) => fc.display.rectfill(x0, y0, x1, y1, c ?? fc.display.color),
      circ: (x, y, r, c) => fc.display.circ(x, y, r, c ?? fc.display.color),
      circfill: (x, y, r, c) => fc.display.circfill(x, y, r, c ?? fc.display.color),
      oval: (x0, y0, x1, y1, c) => fc.display.oval(x0, y0, x1, y1, c ?? fc.display.color, false),
      ovalfill: (x0, y0, x1, y1, c) => fc.display.oval(x0, y0, x1, y1, c ?? fc.display.color, true),
      print: (text, x, y, c) => fc.display.print(text, x, y, c ?? fc.display.color),
      spr: (n, x, y, w = 1, h = 1, fx = false, fy = false) => fc.display.sprite(fc.spriteSheet, n, x, y, w, h, fx, fy),
      sspr: (sx, sy, sw, sh, dx, dy, dw = sw, dh = sh, fx = false, fy = false) => fc.display.sspr(fc.spriteSheet, sx, sy, sw, sh, dx, dy, dw, dh, fx, fy),
      map: (cx = 0, cy = 0, sx = 0, sy = 0, cw = 16, ch = 16, layer = 0) => fc.display.map(fc.mapData, fc.spriteSheet, cx, cy, sx, sy, cw, ch, layer),
      mget: (x, y) => fc.mapData.get(x, y),
      mset: (x, y, v) => fc.mapData.set(x, y, v),
      fget: (n, f = null) => f === null ? fc.flags[n & 255] : Boolean(fc.flags[n & 255] & (1 << (f & 7))),
      fset: (n, f, v = true) => {
        n &= 255; f &= 7;
        if (v) fc.flags[n] |= 1 << f;
        else fc.flags[n] &= ~(1 << f);
      },
      btn: i => fc.input.btn(i),
      btnp: i => fc.input.btnp(i),
      key: code => fc.input.key(code),
      keyp: code => fc.input.keyp(code),
      mouse: () => fc.input.mouse(),
      mousep: button => fc.input.mousep(button),
      lockmouse: () => fc.input.lockMouse(),
      sfx: (id = 0, note = 48, duration = 0.08) => fc.audio.sfx(id, note, duration),
      beep: (freq = 440, duration = 0.08, wave = 'square', volume = 0.8) => fc.audio.beep(freq, duration, wave, volume),
      rnd: x => Math.random() * (x ?? 1),
      flr: Math.floor,
      ceil: Math.ceil,
      abs: Math.abs,
      sgn: x => x < 0 ? -1 : x > 0 ? 1 : 0,
      min: Math.min,
      max: Math.max,
      mid: (a, b, c) => Math.max(Math.min(a, c), Math.min(Math.max(a, c), b)),
      sin: x => Math.sin(x * Math.PI * 2),
      cos: x => Math.cos(x * Math.PI * 2),
      atan2: (dy, dx) => Math.atan2(dy, dx) / (Math.PI * 2),
      sqrt: Math.sqrt,
      time: () => (performance.now() - fc.startTime) / 1000,
      stat: n => fc.stat(n),
      reload: () => fc.reboot(),
      loadit: () => {
        if (!fc.stagedCart) return false;
        fc.jumpToStagedCart();
        return true;
      },
      cartloaded: () => Boolean(fc.stagedCart),
      cartname: () => fc.stagedCart?.name || '',
      cartaddr: () => fc.stagedCart?.memory?.loadAddress || 0,
      cartbytes: () => fc.stagedCart?.memory?.size || 0,
      cartdata: () => true,
      dset: (i, v) => { fc.persist[i & 63] = Number(v) || 0; },
      dget: i => fc.persist[i & 63],
      memcpy: (dest, src, len) => fc.ram.copyWithin(dest & 0x7fff, src & 0x7fff, (src & 0x7fff) + Math.max(0, len | 0)),
      memset: (dest, val, len) => fc.ram.fill(val & 255, dest & 0x7fff, (dest & 0x7fff) + Math.max(0, len | 0)),
      peek: addr => fc.ram[addr & 0x7fff],
      poke: (addr, val) => { fc.ram[addr & 0x7fff] = val & 255; },
      trace: message => fc.log(String(message)),
    };
    return Object.freeze(api);
  }

  stat(n) {
    switch (n | 0) {
      case 0: return this.frame;
      case 1: return this.fps;
      case 2: return this.cartName;
      case 3: return this.system?.kernel?.name || '';
      case 4: return this.unicorn.selfTestResult?.mode || 'unknown';
      case 5: return COLOR_DEPTH_BITS;
      case 6: return SYSTEM_NAME;
      default: return 0;
    }
  }
}

function normalizedBytes(bytes, length) {
  const out = new Uint8Array(length);
  out.set(bytes.subarray(0, length));
  return out;
}



// ===== fixtures.mjs =====

function paletteBin() {
  const out = new Uint8Array(16 * 4);
  const view = new DataView(out.buffer);
  for (let i = 0; i < PICO_PALETTE.length; i++) view.setUint32(i * 4, PICO_PALETTE[i] >>> 0, true);
  return out;
}

function escapeAsmString(value) {
  return JSON.stringify(String(value));
}

function jsNodeName(node) {
  if (!node) return 'null';
  if (node.type === 'Identifier') return node.name;
  if (node.type === 'Literal') return JSON.stringify(node.value);
  if (node.type === 'MemberExpression') return `${jsNodeName(node.object)}.${jsNodeName(node.property)}`;
  return node.type;
}

function compileExpressionToU8Asm(node, out) {
  if (!node) return;
  switch (node.type) {
    case 'Literal':
      out.push(`  const ${escapeAsmString(node.value)}`);
      break;
    case 'Identifier':
      out.push(`  load ${node.name}`);
      break;
    case 'ArrayExpression':
      for (const item of node.elements) compileExpressionToU8Asm(item, out);
      out.push(`  array ${node.elements.length}`);
      break;
    case 'ObjectExpression':
      for (const prop of node.properties) {
        out.push(`  key ${escapeAsmString(jsNodeName(prop.key))}`);
        compileExpressionToU8Asm(prop.value, out);
      }
      out.push(`  object ${node.properties.length}`);
      break;
    case 'UnaryExpression':
      compileExpressionToU8Asm(node.argument, out);
      out.push(`  unary ${node.operator}`);
      break;
    case 'BinaryExpression':
    case 'LogicalExpression':
      compileExpressionToU8Asm(node.left, out);
      compileExpressionToU8Asm(node.right, out);
      out.push(`  binary ${node.operator}`);
      break;
    case 'AssignmentExpression':
      compileExpressionToU8Asm(node.right, out);
      out.push(`  assign ${jsNodeName(node.left)} ${node.operator}`);
      break;
    case 'UpdateExpression':
      out.push(`  update ${jsNodeName(node.argument)} ${node.operator} ${node.prefix ? 'prefix' : 'postfix'}`);
      break;
    case 'CallExpression':
      for (const arg of node.arguments) compileExpressionToU8Asm(arg, out);
      out.push(`  call ${jsNodeName(node.callee)} ${node.arguments.length}`);
      break;
    case 'MemberExpression':
      compileExpressionToU8Asm(node.object, out);
      if (node.computed) compileExpressionToU8Asm(node.property, out);
      out.push(`  member ${node.computed ? 'computed' : jsNodeName(node.property)}`);
      break;
    case 'ConditionalExpression':
      compileExpressionToU8Asm(node.test, out);
      compileExpressionToU8Asm(node.consequent, out);
      compileExpressionToU8Asm(node.alternate, out);
      out.push('  conditional');
      break;
    case 'TemplateLiteral':
      out.push(`  template ${escapeAsmString(node.quasis.map(q => q.value.cooked).join('${}'))}`);
      for (const expr of node.expressions) compileExpressionToU8Asm(expr, out);
      break;
    case 'ArrowFunctionExpression':
    case 'FunctionExpression':
      out.push(`  function_expr ${node.params.map(jsNodeName).join(',')}`);
      compileStatementToU8Asm(node.body, out);
      out.push('  end_function_expr');
      break;
    default:
      out.push(`  ast_expr ${escapeAsmString(JSON.stringify(node))}`);
      break;
  }
}

function compileStatementToU8Asm(node, out) {
  if (!node) return;
  switch (node.type) {
    case 'Program':
    case 'BlockStatement':
      for (const child of node.body) compileStatementToU8Asm(child, out);
      break;
    case 'VariableDeclaration':
      for (const decl of node.declarations) {
        if (decl.init) compileExpressionToU8Asm(decl.init, out);
        out.push(`  var ${node.kind} ${jsNodeName(decl.id)}`);
      }
      break;
    case 'FunctionDeclaration':
      out.push(`fn ${node.id.name} ${node.params.map(jsNodeName).join(' ')}`);
      compileStatementToU8Asm(node.body, out);
      out.push(`endfn ${node.id.name}`);
      break;
    case 'ExpressionStatement':
      compileExpressionToU8Asm(node.expression, out);
      out.push('  pop');
      break;
    case 'ReturnStatement':
      compileExpressionToU8Asm(node.argument, out);
      out.push('  return');
      break;
    case 'IfStatement':
      compileExpressionToU8Asm(node.test, out);
      out.push('  if');
      compileStatementToU8Asm(node.consequent, out);
      if (node.alternate) {
        out.push('  else');
        compileStatementToU8Asm(node.alternate, out);
      }
      out.push('  endif');
      break;
    case 'ForStatement':
      out.push('  for_begin');
      compileStatementToU8Asm(node.init, out);
      compileExpressionToU8Asm(node.test, out);
      compileExpressionToU8Asm(node.update, out);
      compileStatementToU8Asm(node.body, out);
      out.push('  for_end');
      break;
    case 'ForOfStatement':
      compileExpressionToU8Asm(node.right, out);
      out.push(`  forof ${jsNodeName(node.left.declarations?.[0]?.id || node.left)}`);
      compileStatementToU8Asm(node.body, out);
      out.push('  endforof');
      break;
    case 'WhileStatement':
      out.push('  while_begin');
      compileExpressionToU8Asm(node.test, out);
      compileStatementToU8Asm(node.body, out);
      out.push('  while_end');
      break;
    case 'BreakStatement':
      out.push('  break');
      break;
    case 'ContinueStatement':
      out.push('  continue');
      break;
    case 'EmptyStatement':
      break;
    default:
      out.push(`  ast_stmt ${escapeAsmString(JSON.stringify(node))}`);
      break;
  }
}

function compileJavaScriptToU8Assembly(source, filename = '/cart/main.js') {
  if (!window.acorn) throw new Error('Acorn parser library is required to compile cart JavaScript.');
  const ast = window.acorn.parse(source, { ecmaVersion: 2020, sourceType: 'script', allowReturnOutsideFunction: false });
  const out = [
    '; Mega 16 assembly generated from JavaScript',
    `; source ${filename}`,
    '.target m16bc-v1',
    '.requires acorn-js-parser',
  ];
  compileStatementToU8Asm(ast, out);
  out.push('.end');
  return out.join('\n') + '\n';
}

function assembleU8Assembly(assembly) {
  const lines = assembly.split(/\r?\n/).map(line => line.trim()).filter(line => line && !line.startsWith(';'));
  const payload = encoder.encode(JSON.stringify({ format: 'M16BC-v1', lines }, null, 2));
  const out = new Uint8Array(16 + payload.length);
  out.set(encoder.encode('M16BCASM'), 0);
  const view = new DataView(out.buffer);
  view.setUint32(8, payload.length, true);
  view.setUint32(12, crc32(payload), true);
  out.set(payload, 16);
  return out;
}

function compilerSourceText() {
  return [
    '/* Mega 16 JavaScript to M16 assembly compiler.',
    '   Uses Acorn for parsing and emits M16BC-v1 assembly plus assembled bytecode.',
    '   This source is embedded in system images as the cart compiler toolchain. */',
    escapeAsmString.toString(),
    jsNodeName.toString(),
    compileExpressionToU8Asm.toString(),
    compileStatementToU8Asm.toString(),
    compileJavaScriptToU8Assembly.toString(),
    assembleU8Assembly.toString(),
  ].join('\n\n');
}

function buildSystemImage() {
  const systemMain = String.raw`
let lines = [];
let input = '';
let blink = 0;
let bootStep = 0;
let booting = true;
let env = {};
let files = {};
let fileApps = {};
let kernel = {};

function add(text) {
  for (const raw of String(text).split('\n')) {
    let line = raw;
    if (!line) {
      lines.push('');
      continue;
    }
    while (line.length > 31) {
      let cut = line.lastIndexOf(' ', 31);
      if (cut < 8) cut = 31;
      lines.push(line.slice(0, cut));
      line = line.slice(cut).trimStart();
    }
    lines.push(line);
  }
  while (lines.length > 13) lines.shift();
}

function prompt() { return 'C:\\M16>'; }
function up(s) { return String(s || '').toUpperCase(); }
function hex(n) { return '$' + (n || 0).toString(16).toUpperCase().padStart(4, '0'); }
function bytehex(n) { return (n & 255).toString(16).toUpperCase().padStart(2, '0'); }

function make_u8dos_sys(versionMajor = 0, versionMinor = 97) {
  const bytes = new Uint8Array(64);
  bytes.set([0x4D, 0x31, 0x36, 0x44], 0); // M16D
  bytes[4] = versionMajor;
  bytes[5] = versionMinor;
  bytes[6] = 16; // FILES
  bytes[7] = 8;  // BUFFERS
  bytes[8] = 0x01; // resident kernel flag
  bytes[9] = 0x40; // cart load high byte: $4000
  bytes[10] = 0x2A; // API bitmap low
  bytes[11] = 0x81; // API bitmap high
  const name = 'COMMAND.COM';
  for (let i = 0; i < name.length; i++) bytes[16 + i] = name.charCodeAt(i);
  let crc = 0;
  for (let i = 0; i < 60; i++) crc = (crc + bytes[i]) & 255;
  bytes[60] = crc;
  bytes[61] = 0x0D;
  bytes[62] = 0x0A;
  bytes[63] = 0x1A;
  return bytes;
}

function binary_text(bytes) {
  const rows = [];
  for (let i = 0; i < bytes.length; i += 8) {
    const chunk = Array.from(bytes.slice(i, i + 8)).map(bytehex).join(' ');
    rows.push(bytehex(i) + ': ' + chunk);
  }
  return rows.join('\n');
}

function file_size(body) {
  return body instanceof Uint8Array ? body.length : String(body).length;
}

function reset_shell() {
  lines = [];
  input = '';
  bootStep = 0;
  booting = true;
  add('TYPE LOADIT ONCE YOUVE LOADED A CART');
  files = {
    'M16DOS.SYS': make_u8dos_sys(),
    'COMMAND.COM': new Uint8Array([0x4D,0x31,0x36,0x43,0x4F,0x4D,0x01,0x00]),
    'README.TXT': 'M16DOS is the embedded system cartridge.\nLoad a regular cart image, then type LOADIT.\nPress Escape from a running cart to return here.',
    'CONFIG.SYS': 'DEVICE=M16ANSI.SYS\nFILES=16\nBUFFERS=8\nSHELL=COMMAND.COM',
    'AUTOEXEC.BAT': '@ECHO OFF\nVER\nDIR',
    'NOTES.TXT': 'Use EDIT filename to create or replace a small text file.',
    'LOADIT.COM': new Uint8Array([0x55,0x38,0x43,0x4F,0x4D,0x02,0x00,0x00]),
    'HELLO.COM': new Uint8Array([0x55,0x38,0x43,0x4F,0x4D,0x03,0x00,0x00]),
    'CLOCK.COM': new Uint8Array([0x55,0x38,0x43,0x4F,0x4D,0x04,0x00,0x00]),
    'ABOUT.COM': new Uint8Array([0x55,0x38,0x43,0x4F,0x4D,0x05,0x00,0x00]),
    'FILES.COM': new Uint8Array([0x55,0x38,0x43,0x4F,0x4D,0x06,0x00,0x00]),
  };
  fileApps = {
    'COMMAND.COM': 'COMMAND',
    'LOADIT.COM': 'LOADIT',
    'HELLO.COM': 'HELLO',
    'CLOCK.COM': 'CLOCK',
    'ABOUT.COM': 'ABOUT',
    'FILES.COM': 'FILES',
  };
  load_kernel();
}

function load_kernel() {
  const sys = files['M16DOS.SYS'];
  if (!(sys instanceof Uint8Array) || sys[0] !== 0x4D || sys[1] !== 0x31 || sys[2] !== 0x36 || sys[3] !== 0x44) {
    kernel = { version: 'CORRUPT', files: 0, buffers: 0, api: '' };
    env = { version: 'CORRUPT', path: 'C:\\M16;C:\\DOS', comspec: 'COMMAND.COM' };
    return false;
  }
  let crc = 0;
  for (let i = 0; i < 60; i++) crc = (crc + sys[i]) & 255;
  const ok = crc === sys[60];
  const comspec = String.fromCharCode(...sys.slice(16, 27)).replace(/\0+$/g, '') || 'COMMAND.COM';
  kernel = {
    version: ok ? sys[4] + '.' + String(sys[5]).padStart(2, '0') : 'CORRUPT',
    files: sys[6],
    buffers: sys[7],
    resident: Boolean(sys[8] & 1),
    cartLoadAddress: sys[9] << 8,
    api: ((sys[11] << 8) | sys[10]).toString(16).toUpperCase(),
    crcOk: ok,
  };
  env = {
    version: kernel.version,
    path: 'C:\\M16;C:\\DOS',
    comspec,
  };
  return ok;
}

function dir() {
  add(' Volume in drive C is M16DOS');
  add(' Directory of C:\\M16');
  add('');
  for (const [name, body] of Object.entries(files)) {
    const [base, ext = ''] = name.split('.');
    add(base.slice(0, 8).padEnd(8, ' ') + ' ' + ext.slice(0, 3).padEnd(3, ' ') + String(file_size(body)).padStart(7, ' '));
  }
  if (cartloaded()) add('STAGED   CRT' + String(cartbytes()).padStart(7, ' '));
  add('        ' + (Object.keys(files).length + (cartloaded() ? 1 : 0)) + ' File(s)');
}

function type_file(name) {
  const file = up(name || 'README.TXT');
  if (files[file] instanceof Uint8Array) { add(binary_text(files[file])); return; }
  if (files[file]) { add(files[file]); return; }
  add('File not found - ' + file);
}

function dos_name(name) {
  const raw = up(name || '').replace(/^C:\\\\?/, '').replace(/^\\+/, '').trim();
  const safe = raw.replace(/[^A-Z0-9._-]/g, '_');
  const parts = safe.split('.');
  const base = (parts[0] || 'UNTITLED').slice(0, 8);
  const ext = (parts[1] || 'TXT').slice(0, 3);
  return base + '.' + ext;
}

function write_file(args) {
  const firstSpace = args.indexOf(' ');
  if (firstSpace < 0) { add('Usage: WRITE FILE.TXT text'); return; }
  const name = dos_name(args.slice(0, firstSpace));
  files[name] = args.slice(firstSpace + 1);
  delete fileApps[name];
  add('Wrote ' + name);
}

function edit_file(name) {
  const file = dos_name(name || 'NOTES.TXT');
  files[file] = 'Edited in M16DOS at ' + new Date().toLocaleTimeString();
  add('EDIT saved ' + file);
}

function copy_file(args) {
  const parts = args.trim().split(/\s+/);
  if (parts.length < 2) { add('Usage: COPY SRC DST'); return; }
  const src = dos_name(parts[0]);
  const dst = dos_name(parts[1]);
  if (!files[src]) { add('File not found - ' + src); return; }
  files[dst] = files[src] instanceof Uint8Array ? new Uint8Array(files[src]) : files[src];
  if (fileApps[src]) fileApps[dst] = fileApps[src];
  else delete fileApps[dst];
  add('1 file(s) copied.');
}

function rename_file(args) {
  const parts = args.trim().split(/\s+/);
  if (parts.length < 2) { add('Usage: REN OLD NEW'); return; }
  const oldName = dos_name(parts[0]);
  const newName = dos_name(parts[1]);
  if (!files[oldName]) { add('File not found - ' + oldName); return; }
  files[newName] = files[oldName];
  if (fileApps[oldName]) fileApps[newName] = fileApps[oldName];
  else delete fileApps[newName];
  delete files[oldName];
  delete fileApps[oldName];
  add('Renamed ' + oldName + ' to ' + newName);
}

function delete_file(name) {
  const file = dos_name(name);
  if (!files[file]) { add('File not found - ' + file); return; }
  delete files[file];
  delete fileApps[file];
  add('Deleted ' + file);
}

function run_loadit() {
  if (!cartloaded()) {
    add('No regular cartridge is loaded.');
    add('Use Load cartridge image, then type LOADIT.');
    return;
  }
  add('Loading ' + cartname());
  add('Cart image at ' + hex(cartaddr()) + ', ' + cartbytes() + ' bytes');
  add('Jumping to cartridge entry...');
  loadit();
}

function kernel_status() {
  const ok = load_kernel();
  add(ok ? 'M16DOS.SYS loaded' : 'M16DOS.SYS CORRUPT');
  add('Version ' + kernel.version);
  add('FILES=' + kernel.files + ' BUFFERS=' + kernel.buffers);
  add('COMSPEC=' + env.comspec);
  add('CRC=' + (kernel.crcOk ? 'OK' : 'BAD') + ' API=' + kernel.api);
}

function corrupt_file(name) {
  const file = dos_name(name || 'M16DOS.SYS');
  const body = files[file];
  if (!(body instanceof Uint8Array)) { add('Not a binary - ' + file); return; }
  if (!body.length) { add('Empty binary - ' + file); return; }
  const pos = (blink + body.length) % body.length;
  body[pos] = body[pos] ^ 0xFF;
  add('Corrupted ' + file + ' at +' + bytehex(pos));
}

function run_com(name) {
  const file = dos_name(name.endsWith('.COM') ? name : name + '.COM');
  if (!files[file]) return false;
  const app = fileApps[file];
  if (!app) {
    add('Cannot execute ' + file);
    add('Not a M16DOS .COM app.');
    return true;
  }
  add('Loading ' + file + '...');
  if (app === 'COMMAND') { add('COMMAND.COM already resident.'); return true; }
  if (app === 'LOADIT') { run_loadit(); return true; }
  if (app === 'HELLO') { add('Hello from ' + file + '!'); return true; }
  if (app === 'CLOCK') { add('CLOCK.COM ' + new Date().toLocaleTimeString()); return true; }
  if (app === 'ABOUT') { add('M16DOS ' + env.version + '\nM16DOS.SYS backs the kernel settings.\n.COM apps run from the in-memory file table.'); return true; }
  if (app === 'FILES') { add(Object.keys(files).join('\n')); return true; }
  add('App loader error - ' + file);
  return true;
}

function run_command(raw) {
  const text = raw.trim();
  if (!text) return;
  add(prompt() + text);
  const command = up(text.split(/\s+/)[0]);
  const arg = text.slice(command.length).trim();
  if (command === 'CLS') { lines = []; return; }
  if (command === 'HELP') { add('Commands: DIR CLS VER MEM TYPE WRITE EDIT COPY REN DEL CORRUPT SYS KERNEL LOADSYS PATH SET CART LOADIT BOOT HELP\nApps: COMMAND HELLO CLOCK ABOUT FILES LOADIT'); return; }
  if (command === 'VER') { load_kernel(); add('M16DOS System Kernel ' + env.version); return; }
  if (command === 'DIR') { dir(); return; }
  if (command === 'MEM') { add('32768 bytes Mega 16 RAM'); add((cartloaded() ? cartbytes() : 0) + ' bytes staged cart image'); return; }
  if (command === 'PATH') { add('PATH=' + env.path); return; }
  if (command === 'SET') { add('COMSPEC=' + env.comspec + '\nPATH=' + env.path); return; }
  if (command === 'SYS' || command === 'KERNEL') { kernel_status(); return; }
  if (command === 'LOADSYS') { load_kernel(); add('Reloaded M16DOS.SYS'); return; }
  if (command === 'TYPE') { type_file(arg); return; }
  if (command === 'WRITE') { write_file(arg); return; }
  if (command === 'EDIT') { edit_file(arg); return; }
  if (command === 'COPY') { copy_file(arg); return; }
  if (command === 'REN' || command === 'RENAME') { rename_file(arg); return; }
  if (command === 'DEL' || command === 'ERASE') { delete_file(arg); return; }
  if (command === 'CORRUPT') { corrupt_file(arg); return; }
  if (command === 'CART') { add(cartloaded() ? ('Cart: ' + cartname() + '\nAddress: ' + hex(cartaddr()) + '\nBytes: ' + cartbytes()) : 'No cart staged.'); return; }
  if (command === 'LOADIT' || command === 'LOADIT.COM') { run_loadit(); return; }
  if (command === 'BOOT') { reset_shell(); return; }
  if (run_com(command)) return;
  add('Bad command or file name');
}

function keyText(event) {
  if (event.ctrlKey || event.metaKey || event.altKey) return '';
  if (event.key.length === 1) return event.key;
  if (event.key === 'Enter') return '\n';
  if (event.key === 'Backspace') return '\b';
  if (event.key === 'Escape') return '\x1b';
  return '';
}

function handleKey(event) {
  const key = keyText(event);
  if (!key) return;
  event.preventDefault();
  if (booting) return;
  if (key === '\n') { run_command(input); input = ''; return; }
  if (key === '\b') { input = input.slice(0, -1); return; }
  if (key === '\x1b') { input = ''; return; }
  if (input.length < 38) input += key;
}

function _init() {
  reset_shell();
  if (globalThis.__u8dosSystemKeyHandler) globalThis.removeEventListener('keydown', globalThis.__u8dosSystemKeyHandler, true);
  globalThis.__u8dosSystemKeyHandler = handleKey;
  globalThis.addEventListener('keydown', handleKey, true);
  trace('M16DOS system cartridge booted. Type HELP.');
  trace('TYPE LOADIT ONCE YOUVE LOADED A CART');
}

function _update() {
  blink++;
  if (!booting) return;
  bootStep++;
  if (bootStep === 1) add('M16BOOT system loader v0.96');
  if (bootStep === 15) { load_kernel(); add('Loading M16DOS.SYS v' + kernel.version); }
  if (bootStep === 30) add('Loading COMMAND.COM');
  if (bootStep === 45) add('Installing cart memory loader');
  if (bootStep === 60) add('Ready. Load a regular cart, then type LOADIT.');
  if (bootStep > 78) {
    booting = false;
    add('');
    add('M16DOS System Kernel ' + env.version);
    add('Type HELP for commands.');
  }
}

function _draw() {
  cls(0);
  rect(0, 0, 127, 127, 1);
  rectfill(0, 0, 127, 8, 1);
  print('M16DOS SYSTEM', 2, 1, 7);
  print(cartloaded() ? 'CART READY' : 'NO CART', 78, 1, cartloaded() ? 11 : 8);
  let y = 13;
  for (const line of lines) {
    print(line, 2, y, 11);
    y += 8;
  }
  if (!booting) {
    const promptText = prompt() + input + ((blink % 30) < 15 ? '_' : ' ');
    const start = Math.max(0, promptText.length - 31);
    print(promptText.slice(start), 2, 118, 7);
  }
}
`;
  const kernel = {
    name: 'M16DOS System Cartridge',
    version: '0.96',
    main: '/sys/main.js',
    screen: { width: 128, height: 128, fps: 30 },
    cpu: { backend: 'Mega 16 ARM backend + JavaScript fantasy kernel' },
    imageFormat: {
      magic: 'MBR/FAT16 for carts; M16IMG1 system container',
      sectorSize: 512,
      systemBootable: true,
      cartBootable: false,
      description: 'System image has boot metadata. Cartridges are non-bootable MBR/FAT16 disk images with standard 55 AA sector signatures.',
    },
    compiler: {
      parser: 'Acorn',
      assembly: 'M16BC-v1',
      bytecodeMagic: 'M16BCASM',
    },
    bootloader: {
      path: '/sys/bootloader.m16asm',
      autoChainload: false,
      cartLoadAddress: 0x4000,
      behavior: 'Stage regular carts in memory. Type LOADIT in M16DOS to jump to the staged cart.',
    },
  };
  const bootloader = [
    '; M16DOS embedded system bootloader',
    '.target m16-system',
    '.org $0000',
    'BOOT:',
    '  call SYS_INIT',
    '  call COMMAND_START',
    'LOADIT:',
    '  call CART_REQUIRE_STAGED',
    '  call CART_MAP_MEMORY',
    '  jmp CART_ENTRY',
    '.end',
    '',
  ].join('\n');
  return createImage({
    label: 'M16DOS-SYSTEM',
    type: 'system',
    bootable: true,
    bootFile: '/sys/kernel.json',
    files: {
      '/sys/kernel.json': kernel,
      '/sys/main.js': systemMain,
      '/sys/bootloader.m16asm': bootloader,
      '/sys/palette.bin': paletteBin(),
      '/sys/compiler/js-to-m16asm.js': compilerSourceText(),
      '/sys/compiler/readme.txt': 'Complete Mega 16 cart compiler source. Uses Acorn to parse JavaScript, emits M16BC-v1 assembly, then assembles M16BCASM bytecode artifacts.',
      '/sys/readme.txt': 'Embedded M16DOS system image. Load a regular cart image, then type LOADIT. Press Escape while a cart runs to return to DOS.',
    },
  });
}

function buildDemoCartImage() {
  const sheet = new SpriteSheet();
  sheet.drawSprite(1, [
    '000cc000',
    '00c77c00',
    '0c7777c0',
    '0c7777c0',
    '0c7aa7c0',
    '00c77c00',
    '00c55c00',
    '0c5005c0',
  ]);
  sheet.drawSprite(2, [
    '000aa000',
    '00a99a00',
    '0a9999a0',
    'a999999a',
    '0a9999a0',
    '00a99a00',
    '000aa000',
    '00000000',
  ]);
  sheet.drawSprite(3, [
    '44444444',
    '43333334',
    '43434334',
    '43333334',
    '44343444',
    '43333334',
    '43443334',
    '44444444',
  ]);
  sheet.drawSprite(4, [
    '00070000',
    '00070000',
    '77077000',
    '07777700',
    '00777000',
    '00707000',
    '07000700',
    '00000000',
  ]);
  sheet.drawSprite(5, [
    '00088000',
    '00888800',
    '08800880',
    '08888880',
    '08888880',
    '00800800',
    '08000080',
    '00000000',
  ]);
  sheet.drawSprite(6, [
    '00000000',
    '00555500',
    '05555550',
    '05511150',
    '05511150',
    '05555550',
    '00555500',
    '00000000',
  ]);

  const map = new TileMap();
  for (let x = 0; x < 64; x++) map.set(x, 15, 3);
  for (let x = 0; x < 64; x += 7) map.set(x, 14, 3);
  for (let x = 6; x < 16; x++) map.set(x, 11, 3);
  for (let x = 22; x < 34; x++) map.set(x, 9, 3);
  for (let x = 40; x < 51; x++) map.set(x, 12, 3);
  for (let y = 0; y < 16; y++) { map.set(0, y, 3); map.set(63, y, 3); }

  const flags = new Uint8Array(256);
  flags[3] = 1;

  const code = `
let px = 20, py = 80, vx = 0, vy = 0;
let score = 0, jumps = 0, shake = 0, win = false;
let gems = [
  {x:52,y:80,on:true},{x:88,y:64,on:true},{x:160,y:48,on:true},
  {x:232,y:88,on:true},{x:304,y:64,on:true},{x:384,y:88,on:true}
];
let stars = [];
for (let i=0;i<48;i++) stars.push({x:rnd(512),y:rnd(88),s:1+rnd(2)});

function solid_at(x,y){
  const tx = flr(x/8), ty = flr(y/8);
  return fget(mget(tx,ty),0);
}

function move_x(amount){
  px += amount;
  if (amount > 0 && (solid_at(px+7,py) || solid_at(px+7,py+7))) px = flr((px+7)/8)*8-8;
  if (amount < 0 && (solid_at(px,py) || solid_at(px,py+7))) px = flr(px/8)*8+8;
}

function move_y(amount){
  py += amount;
  if (amount > 0 && (solid_at(px,py+7) || solid_at(px+7,py+7))) { py = flr((py+7)/8)*8-8; vy = 0; jumps = 0; }
  if (amount < 0 && (solid_at(px,py) || solid_at(px+7,py))) { py = flr(py/8)*8+8; vy = 0; }
}

function _init(){
  trace('Star Hopper loaded. Arrow/WASD move, Z/J/Space jump.');
  beep(330,0.06,'triangle');
}

function _update(){
  const accel = 0.35;
  if (btn(0)) vx -= accel;
  if (btn(1)) vx += accel;
  vx *= 0.82;
  vx = mid(-2.2, vx, 2.2);
  vy += 0.22;
  vy = min(vy, 3.2);
  if (btnp(4) && jumps < 2) { vy = -3.9; jumps++; sfx(1, 50+jumps*3, 0.08); }
  move_x(vx);
  move_y(vy);
  px = mid(8, px, 496);
  if (py > 130) { px=20; py=40; vx=0; vy=0; shake=8; sfx(2,24,0.2); }
  for (const gem of gems) {
    if (gem.on && abs((px+4)-(gem.x+4)) < 7 && abs((py+4)-(gem.y+4)) < 7) {
      gem.on = false; score++; shake=4; sfx(0, 62+score, 0.09);
    }
  }
  win = score === gems.length;
  if (shake > 0) shake--;
}

function _draw(){
  cls(1);
  const camx = flr(px - 64);
  const sx = shake ? flr(rnd(3))-1 : 0;
  const sy = shake ? flr(rnd(3))-1 : 0;
  camera(camx - sx, -sy);
  for (const star of stars) pset(star.x, star.y, 5 + flr(star.s));
  map(0,0,0,0,64,16);
  for (const gem of gems) if (gem.on) spr(2, gem.x, gem.y + sin(time()*0.8 + gem.x)*2);
  spr(1, px, py, 1, 1, vx < -0.1, false);
  camera(0,0);
  rectfill(0,0,127,12,0);
  print('STAR HOPPER', 2, 3, 10);
  print('GEMS '+score+'/'+gems.length, 80, 3, 7);
  if (win) {
    rectfill(17,45,111,79,0);
    rect(17,45,111,79,10);
    print('YOU CLEARED IT!', 37, 55, 11);
    print('PRESS ESC TO ADMIRE', 28, 67, 6);
  }
}
`;

  const assembly = compileJavaScriptToU8Assembly(code, '/cart/main.js');
  const bytecode = assembleU8Assembly(assembly);

  return createFat16CartDisk({
    label: 'STAR-HOPPER',
    files: {
      '/cart/meta.jso': {
        title: 'Star Hopper',
        author: 'Mega 16',
        main: '/cart/main.js',
        assembly: '/cart/main.asm',
        bytecode: '/cart/main.bc',
        compiler: '/cart/compiler/jsc.js',
        format: 'mbr-fat16-m16cart.img',
      },
      '/meta.jso': {
        title: 'Star Hopper',
        author: 'Mega 16',
        main: '/cart/main.js',
        assembly: '/cart/main.asm',
        bytecode: '/cart/main.bc',
        compiler: '/cart/compiler/jsc.js',
        format: 'mbr-fat16-m16cart.img',
      },
      '/cart/main.js': code,
      '/cart/main.asm': assembly,
      '/cart/main.bc': bytecode,
      '/cart/compiler/jsc.js': compilerSourceText(),
      '/cart/sprites.bin': sheet.dumpPacked(),
      '/cart/map.bin': map.dump(),
      '/cart/flags.bin': flags,
      '/cart/readme.txt': 'Non-bootable cartridge disk image. MBR sector 0 has signature 55 AA and an inactive FAT16 partition. JavaScript source, generated M16 assembly, assembled M16BC bytecode, and compiler source are all included.',
      '/readme.txt': 'Mega 16 non-bootable FAT16 cartridge disk. Open /cart for source, assembly, bytecode, data, and compiler files.',
    },
  });
}


// ===== app.mjs =====

const $ = selector => document.querySelector(selector);
const logEl = $('#log');
const fileEl = $('#file');
const canvas = $('#screen');
const cartInfoEl = $('#cart-info');

const lines = [];
function log(message) {
  const stamp = new Date().toLocaleTimeString();
  lines.push(`[${stamp}] ${message}`);
  while (lines.length > 120) lines.shift();
  logEl.textContent = lines.join('\n');
  logEl.scrollTop = logEl.scrollHeight;
}

const fc = new FantasyConsole({ canvas, log, fps: 30 });
let builtSystem = buildSystemImage();
let builtCart = buildDemoCartImage();
try {
  parseImage(builtCart);
} catch (error) {
  log(`built-in cart image check failed: ${error.message}`);
}

function bootDefault() {
  try {
    fc.clearCart();
    fc.bootSystem(builtSystem);
    fc.start();
    renderInfo();
  } catch (error) {
    log(error.stack || error.message);
  }
}

function renderInfo() {
  try {
    if (fc.cart?.fs) {
      const cart = imageInfo(fc.cart.fs);
      const part = cart.partitioned ? ` | partition=${cart.partition.index} lba=${cart.partition.startLba} sectors=${cart.partition.sectorCount}` : '';
      const staged = fc.stagedCart?.memory ? ` | memory=$${fc.stagedCart.memory.loadAddress.toString(16)} copied=${fc.stagedCart.memory.copiedToRam}/${fc.stagedCart.memory.size}` : '';
      cartInfoEl.textContent = `${cart.label} | bootable=${cart.bootable} | filesystem=${cart.filesystem} | partitioned=${cart.partitioned}${part} | files=${cart.entries.length} | fs=${cart.totalBytes} bytes${staged}`;
    } else if (fc.stagedCart?.fs) {
      const cart = imageInfo(fc.stagedCart.fs);
      cartInfoEl.textContent = `${cart.label} | staged in memory at $${fc.stagedCart.memory.loadAddress.toString(16)} | waiting for system bootloader`;
    } else {
      cartInfoEl.textContent = 'NO CART LOADED :(';
    }
  } catch (error) {
    cartInfoEl.textContent = 'cart info unavailable';
  }
}

async function readFileInput(input) {
  const file = input.files && input.files[0];
  if (!file) return null;
  return new Uint8Array(await file.arrayBuffer());
}

$('#load-cart').addEventListener('click', async () => {
  try {
    const bytes = await readFileInput(fileEl);
    if (!bytes) { log('choose a cartridge image first'); return; }
    fc.stop();
    fc.loadCart(bytes);
    fc.start();
    renderInfo();
  } catch (error) {
    log(error.stack || error.message);
  }
});

$('#reboot').addEventListener('click', () => {
  try { fc.reboot(); fc.start(); } catch (error) { log(error.stack || error.message); }
});

$('#pause').addEventListener('click', event => {
  if (fc.running) { fc.stop(); event.currentTarget.textContent = 'Resume'; log('paused'); }
  else { fc.start(); event.currentTarget.textContent = 'Pause'; log('resumed'); }
});

window.addEventListener('keydown', event => {
  if (event.key !== 'Escape') return;
  if (!fc.cartModule) return;
  event.preventDefault();
  event.stopPropagation();
  fc.returnToSystem();
  fc.start();
  renderInfo();
}, true);

$('#export-system').addEventListener('click', () => saveBytesAsDownload(builtSystem, 'mega16-system.m16sys.img'));
$('#export-cart').addEventListener('click', () => saveBytesAsDownload(builtCart, 'star-hopper.m16cart.img'));
$('#reset-builtins').addEventListener('click', () => {
  builtSystem = buildSystemImage();
  builtCart = buildDemoCartImage();
  fc.stop();
  bootDefault();
  log('rebuilt built-in system and cart images');
});

window.addEventListener('pointerdown', () => fc.audio.ensure(), { once: true });
window.addEventListener('keydown', () => fc.audio.ensure(), { once: true });

bootDefault();
log('controls: arrows/wasd move, z/j/space jump, x/k/enter action');
log('format: system uses M16IMG boot metadata; carts are non-bootable MBR/FAT16 disks with compiled M16BC artifacts');


})();
