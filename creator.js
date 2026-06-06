(() => {
'use strict';

const W = 128;
const H = 128;
const SECTOR = 512;
const MBR_PARTITION_OFFSET = 446;
const MBR_SIGNATURE_OFFSET = 510;
const FAT16_PARTITION_TYPE = 0x06;
const DEFAULT_PARTITION_START_LBA = 2048;
const FAT_ATTR_DIRECTORY = 0x10;
const FAT_ATTR_ARCHIVE = 0x20;
const encoder = new TextEncoder();
const decoder = new TextDecoder();

const palette = [
  '#000000', '#1d2b53', '#7e2553', '#008751',
  '#ab5236', '#5f574f', '#c2c3c7', '#fff1e8',
  '#ff004d', '#ffa300', '#ffec27', '#00e436',
  '#29adff', '#83769c', '#ff77a8', '#ffccaa',
];

const $ = sel => document.querySelector(sel);
const spriteCanvas = $('#sprite');
const spriteCtx = spriteCanvas.getContext('2d');
const sceneCanvas = $('#scene');
const sceneCtx = sceneCanvas.getContext('2d');
const screen = $('#screen');
const screenCtx = screen.getContext('2d');
const sprites = [];
const sceneObjects = [];
const basFiles = new Map();
const keysDown = new Set();
let color = 11;
let compiled = null;
let raf = 0;
let start = performance.now();
let selectedObjectId = 0;
let currentBasPath = 'main.bas';
let currentSpriteId = 1;
let currentFrameIndex = 0;

function log(message) {
  const el = $('#log');
  el.textContent += `${new Date().toLocaleTimeString()} ${message}\n`;
  el.scrollTop = el.scrollHeight;
}

function crc32(bytes) {
  let c = 0xffffffff;
  for (let i = 0; i < bytes.length; i++) {
    c ^= bytes[i];
    for (let k = 0; k < 8; k++) c = (c & 1) ? (0xedb88320 ^ (c >>> 1)) : (c >>> 1);
  }
  return (c ^ 0xffffffff) >>> 0;
}

function align(value, size) {
  return Math.ceil(value / size) * size;
}

function asBytes(value) {
  if (value instanceof Uint8Array) return value;
  if (value instanceof ArrayBuffer) return new Uint8Array(value);
  if (ArrayBuffer.isView(value)) return new Uint8Array(value.buffer, value.byteOffset, value.byteLength);
  if (typeof value === 'string') return encoder.encode(value);
  return encoder.encode(JSON.stringify(value, null, 2));
}

function normalizePath(path) {
  let p = String(path).replace(/\\+/g, '/').trim();
  if (!p.startsWith('/')) p = '/' + p;
  const parts = [];
  for (const part of p.split('/')) {
    if (!part || part === '.') continue;
    if (part === '..') throw new Error(`Invalid path ${path}`);
    parts.push(part);
  }
  return '/' + parts.join('/');
}

function writeFixedString(target, offset, length, text) {
  const bytes = encoder.encode(String(text ?? ''));
  target.fill(0, offset, offset + length);
  target.set(bytes.subarray(0, Math.min(length, bytes.length)), offset);
}

function toFatName(pathPart) {
  if (pathPart === '.') return '.          ';
  if (pathPart === '..') return '..         ';
  const cleaned = String(pathPart).toUpperCase().replace(/[^A-Z0-9._-]/g, '_');
  const dot = cleaned.lastIndexOf('.');
  const base = (dot >= 0 ? cleaned.slice(0, dot) : cleaned).replace(/[^A-Z0-9_-]/g, '_').slice(0, 8);
  const ext = (dot >= 0 ? cleaned.slice(dot + 1) : '').replace(/[^A-Z0-9_-]/g, '_').slice(0, 3);
  if (!base) throw new Error(`Bad FAT name ${pathPart}`);
  return (base.padEnd(8, ' ') + ext.padEnd(3, ' ')).slice(0, 11);
}

function writeFatName(target, offset, name) {
  target.set(encoder.encode(toFatName(name)), offset);
}

function fatDateTime(date = new Date()) {
  const year = Math.max(1980, date.getFullYear());
  return {
    date: ((year - 1980) << 9) | ((date.getMonth() + 1) << 5) | date.getDate(),
    time: (date.getHours() << 11) | (date.getMinutes() << 5) | Math.floor(date.getSeconds() / 2),
  };
}

function writeFatDirEntry(target, offset, entry) {
  const view = new DataView(target.buffer);
  const stamp = fatDateTime();
  writeFatName(target, offset, entry.name);
  target[offset + 11] = entry.attr;
  view.setUint16(offset + 14, stamp.time, true);
  view.setUint16(offset + 16, stamp.date, true);
  view.setUint16(offset + 22, stamp.time, true);
  view.setUint16(offset + 24, stamp.date, true);
  view.setUint16(offset + 26, entry.cluster || 0, true);
  view.setUint32(offset + 28, entry.size || 0, true);
}

function writeMbrPartitionEntry(target, offset, part) {
  const view = new DataView(target.buffer);
  target[offset] = 0x00;
  target[offset + 1] = 0x00;
  target[offset + 2] = 0x02;
  target[offset + 3] = 0x00;
  target[offset + 4] = part.type;
  target[offset + 5] = 0xfe;
  target[offset + 6] = 0xff;
  target[offset + 7] = 0xff;
  view.setUint32(offset + 8, part.startLba, true);
  view.setUint32(offset + 12, part.sectorCount, true);
}

function writeFatValue(disk, fatOffset, cluster, value) {
  new DataView(disk.buffer).setUint16(fatOffset + cluster * 2, value, true);
}

function createFat16Image(label, fileMap) {
  const bytesPerSector = SECTOR;
  const sectorsPerCluster = 1;
  const reservedSectors = 1;
  const fatCount = 2;
  const rootEntryCount = 512;
  const rootDirSectors = Math.ceil(rootEntryCount * 32 / bytesPerSector);
  const startLba = DEFAULT_PARTITION_START_LBA;
  const files = Object.entries(fileMap).map(([path, value]) => ({ path: normalizePath(path), bytes: asBytes(value) })).sort((a, b) => a.path.localeCompare(b.path));
  const dirs = new Set();
  for (const file of files) {
    const parts = file.path.split('/').filter(Boolean);
    for (let i = 0; i < parts.length - 1; i++) dirs.add('/' + parts.slice(0, i + 1).join('/'));
  }
  const dirList = [...dirs].sort((a, b) => a.localeCompare(b));
  const usedClusters = dirList.length + files.reduce((n, f) => n + Math.max(1, Math.ceil(f.bytes.length / bytesPerSector)), 0);
  const dataClusters = Math.max(4096, usedClusters);
  let sectorsPerFat = 1;
  for (;;) {
    const total = reservedSectors + fatCount * sectorsPerFat + rootDirSectors + dataClusters + 16;
    const count = total - reservedSectors - fatCount * sectorsPerFat - rootDirSectors;
    const needed = Math.ceil((count + 2) * 2 / bytesPerSector);
    if (needed === sectorsPerFat) break;
    sectorsPerFat = needed;
  }

  const totalSectors = reservedSectors + fatCount * sectorsPerFat + rootDirSectors + dataClusters + 16;
  const partitionOffset = startLba * bytesPerSector;
  const disk = new Uint8Array(partitionOffset + totalSectors * bytesPerSector);
  const view = new DataView(disk.buffer);
  const firstFatSector = reservedSectors;
  const rootDirSector = reservedSectors + fatCount * sectorsPerFat;
  const firstDataSector = reservedSectors + fatCount * sectorsPerFat + rootDirSectors;
  const fatOffset = partitionOffset + firstFatSector * bytesPerSector;
  const rootOffset = partitionOffset + rootDirSector * bytesPerSector;
  const clusterOffset = cluster => partitionOffset + (firstDataSector + (cluster - 2) * sectorsPerCluster) * bytesPerSector;

  writeMbrPartitionEntry(disk, MBR_PARTITION_OFFSET, { type: FAT16_PARTITION_TYPE, startLba, sectorCount: totalSectors });
  disk[MBR_SIGNATURE_OFFSET] = 0x55;
  disk[MBR_SIGNATURE_OFFSET + 1] = 0xaa;

  const vbr = partitionOffset;
  disk[vbr] = 0xeb;
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
  view.setUint32(vbr + 39, crc32(encoder.encode(label)), true);
  disk.set(encoder.encode(label.toUpperCase().replace(/[^A-Z0-9 ]/g, ' ').slice(0, 11).padEnd(11, ' ')), vbr + 43);
  disk.set(encoder.encode('FAT16   '), vbr + 54);
  disk[vbr + 510] = 0x55;
  disk[vbr + 511] = 0xaa;

  for (let f = 0; f < fatCount; f++) {
    const off = fatOffset + f * sectorsPerFat * bytesPerSector;
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
  const chain = clusters => {
    for (let i = 0; i < clusters.length; i++) {
      const value = i + 1 < clusters.length ? clusters[i + 1] : 0xffff;
      for (let f = 0; f < fatCount; f++) writeFatValue(disk, fatOffset + f * sectorsPerFat * bytesPerSector, clusters[i], value);
    }
  };
  for (const cluster of dirClusters.values()) chain([cluster]);
  for (const file of fileRecords) chain(file.clusters);
  for (const file of fileRecords) {
    let copied = 0;
    for (const cluster of file.clusters) {
      const chunk = file.bytes.subarray(copied, copied + bytesPerSector);
      disk.set(chunk, clusterOffset(cluster));
      copied += chunk.length;
    }
  }

  const children = new Map([['/', []]]);
  for (const dir of dirList) children.set(dir, []);
  for (const dir of dirList) {
    const parts = dir.split('/').filter(Boolean);
    const parent = parts.length === 1 ? '/' : '/' + parts.slice(0, -1).join('/');
    children.get(parent).push({ name: parts.at(-1), attr: FAT_ATTR_DIRECTORY, cluster: dirClusters.get(dir), size: 0 });
  }
  for (const file of fileRecords) {
    const parts = file.path.split('/').filter(Boolean);
    const parent = parts.length === 1 ? '/' : '/' + parts.slice(0, -1).join('/');
    children.get(parent).push({ name: parts.at(-1), attr: FAT_ATTR_ARCHIVE, cluster: file.clusters[0], size: file.bytes.length });
  }
  const writeDirectory = (path, offset, parentCluster) => {
    let pos = offset;
    if (path !== '/') {
      writeFatDirEntry(disk, pos, { name: '.', attr: FAT_ATTR_DIRECTORY, cluster: dirClusters.get(path) }); pos += 32;
      writeFatDirEntry(disk, pos, { name: '..', attr: FAT_ATTR_DIRECTORY, cluster: parentCluster || 0 }); pos += 32;
    }
    for (const child of children.get(path) || []) {
      writeFatDirEntry(disk, pos, child);
      pos += 32;
    }
  };
  writeDirectory('/', rootOffset, 0);
  for (const dir of dirList) {
    const parts = dir.split('/').filter(Boolean);
    const parent = parts.length === 1 ? '/' : '/' + parts.slice(0, -1).join('/');
    writeDirectory(dir, clusterOffset(dirClusters.get(dir)), parent === '/' ? 0 : dirClusters.get(parent));
  }
  return disk;
}

function saveBytes(bytes, filename) {
  const blob = new Blob([bytes], { type: 'application/octet-stream' });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = filename;
  document.body.appendChild(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(url), 3000);
}

function makeBlankFrame() {
  return new Uint8Array(16 * 16);
}

function currentSprite() {
  return sprites.find(s => s.id === currentSpriteId) || sprites[0];
}

function currentFramePixels() {
  const sprite = currentSprite();
  return sprite.frames[Math.max(0, Math.min(sprite.frames.length - 1, currentFrameIndex))];
}

function spriteById(id) {
  return sprites.find(s => s.id === Number(id)) || sprites[0];
}

function spriteFramePixels(spriteId, tick = 0) {
  const sprite = spriteById(spriteId);
  if (!sprite) return makeBlankFrame();
  const fps = Math.max(1, sprite.fps || 8);
  const frame = Math.floor((tick / 60) * fps) % sprite.frames.length;
  return sprite.frames[frame];
}

function refreshSpriteControls() {
  const spriteSelect = $('#sprite-select');
  const objectSprite = $('#object-sprite');
  const selectedObjectSprite = objectSprite.value;
  spriteSelect.textContent = '';
  objectSprite.textContent = '';
  for (const sprite of sprites) {
    const label = `${sprite.id}: ${sprite.name}`;
    const a = new Option(label, String(sprite.id));
    const b = new Option(label, String(sprite.id));
    spriteSelect.add(a);
    objectSprite.add(b);
  }
  spriteSelect.value = String(currentSpriteId);
  objectSprite.value = selectedObjectSprite || String(currentObject()?.sprite || currentSpriteId);
  refreshFrameControls();
}

function refreshFrameControls() {
  const sprite = currentSprite();
  const frameSelect = $('#frame-select');
  frameSelect.textContent = '';
  sprite.frames.forEach((_, i) => frameSelect.add(new Option(`Frame ${i + 1}`, String(i))));
  currentFrameIndex = Math.max(0, Math.min(sprite.frames.length - 1, currentFrameIndex));
  frameSelect.value = String(currentFrameIndex);
  $('#sprite-fps').value = sprite.fps;
}

function renderSprite() {
  const pixels = currentFramePixels();
  spriteCtx.imageSmoothingEnabled = false;
  spriteCtx.fillStyle = '#000';
  spriteCtx.fillRect(0, 0, 256, 256);
  for (let y = 0; y < 16; y++) {
    for (let x = 0; x < 16; x++) {
      spriteCtx.fillStyle = palette[pixels[y * 16 + x]];
      spriteCtx.fillRect(x * 16, y * 16, 16, 16);
    }
  }
  spriteCtx.strokeStyle = 'rgba(255,255,255,.16)';
  for (let i = 0; i <= 16; i++) {
    spriteCtx.beginPath(); spriteCtx.moveTo(i * 16, 0); spriteCtx.lineTo(i * 16, 256); spriteCtx.stroke();
    spriteCtx.beginPath(); spriteCtx.moveTo(0, i * 16); spriteCtx.lineTo(256, i * 16); spriteCtx.stroke();
  }
}

function drawSpritePixels(ctx, x, y, scale = 1, spriteId = currentSpriteId, tick = 0) {
  const pixels = spriteFramePixels(spriteId, tick);
  for (let sy = 0; sy < 16; sy++) {
    for (let sx = 0; sx < 16; sx++) {
      const c = pixels[sy * 16 + sx];
      if (!c) continue;
      ctx.fillStyle = palette[c & 15];
      ctx.fillRect((x + sx) * scale, (y + sy) * scale, scale, scale);
    }
  }
}

function spriteBytes() {
  const sheet = new Uint8Array(128 * 128);
  const animations = animationMetadata();
  for (const sprite of sprites) {
    const anim = animations.find(a => a.id === sprite.id);
    sprite.frames.forEach((frame, frameIndex) => {
      const slot = anim?.frames[frameIndex] ?? sprite.id;
      if (slot < 0 || slot > 255) return;
      const tileX = (slot % 16) * 8;
      const tileY = Math.floor(slot / 16) * 8;
      for (let y = 0; y < 16; y++) {
        for (let x = 0; x < 16; x++) {
          const dstX = tileX + x;
          const dstY = tileY + y;
          if (dstX < 128 && dstY < 128) sheet[dstY * 128 + dstX] = frame[y * 16 + x];
        }
      }
    });
  }
  const out = new Uint8Array(sheet.length / 2);
  for (let i = 0, j = 0; i < out.length; i++) out[i] = (sheet[j++] & 15) | ((sheet[j++] & 15) << 4);
  return out;
}

function animationMetadata() {
  let slot = 1;
  return sprites.map(sprite => ({
    id: sprite.id,
    name: sprite.name,
    fps: sprite.fps,
    frames: sprite.frames.map(() => slot++).filter(frameSlot => frameSlot <= 255),
  }));
}

function newSprite() {
  const id = sprites.length ? Math.max(...sprites.map(s => s.id + s.frames.length)) + 1 : 1;
  sprites.push({ id, name: `sprite${id}`, fps: 8, frames: [makeBlankFrame()] });
  currentSpriteId = id;
  currentFrameIndex = 0;
  refreshSpriteControls();
  renderSprite();
  renderSceneEditor();
}

function addFrame() {
  const sprite = currentSprite();
  sprite.frames.push(new Uint8Array(currentFramePixels()));
  currentFrameIndex = sprite.frames.length - 1;
  refreshFrameControls();
  renderSprite();
  renderSceneEditor();
}

function deleteFrame() {
  const sprite = currentSprite();
  if (sprite.frames.length <= 1) {
    sprite.frames[0].fill(0);
  } else {
    sprite.frames.splice(currentFrameIndex, 1);
  }
  currentFrameIndex = Math.max(0, currentFrameIndex - 1);
  refreshFrameControls();
  renderSprite();
  renderSceneEditor();
}

function initSprites() {
  sprites.length = 0;
  sprites.push({ id: 1, name: 'sprite1', fps: 8, frames: [makeBlankFrame()] });
  currentSpriteId = 1;
  currentFrameIndex = 0;
  refreshSpriteControls();
}

function handleSpriteSelection() {
  currentSpriteId = Number($('#sprite-select').value) || 1;
  currentFrameIndex = 0;
  refreshFrameControls();
  renderSprite();
}

function handleFrameSelection() {
  currentFrameIndex = Number($('#frame-select').value) || 0;
  renderSprite();
}

function handleSpriteFps() {
  currentSprite().fps = Math.max(1, Math.min(30, Number($('#sprite-fps').value) || 8));
  renderSceneEditor();
}

function currentObject() {
  return sceneObjects.find(o => o.id === selectedObjectId) || null;
}

function objectDefaultCode() {
  return `LOCAL INIT:
DIM dx = 0

LOCAL UPDATE:
x = x + dx

LOCAL DRAW:
SPR 1, x, y`;
}

function addObject(x = 48, y = 48) {
  const id = sceneObjects.length ? Math.max(...sceneObjects.map(o => o.id)) + 1 : 1;
  sceneObjects.push({ id, name: `sprite${id}`, x: x | 0, y: y | 0, sprite: 1, code: objectDefaultCode() });
  selectedObjectId = id;
  syncObjectForm();
  renderSceneEditor();
}

function deleteObject() {
  const i = sceneObjects.findIndex(o => o.id === selectedObjectId);
  if (i >= 0) sceneObjects.splice(i, 1);
  selectedObjectId = sceneObjects[0]?.id || 0;
  syncObjectForm();
  renderSceneEditor();
}

function syncObjectForm() {
  const obj = currentObject();
  $('#object-name').value = obj?.name || '';
  $('#object-x').value = obj?.x ?? '';
  $('#object-y').value = obj?.y ?? '';
  $('#object-sprite').value = String(obj?.sprite ?? 1);
  $('#object-code').value = obj?.code || '';
}

function updateSelectedObject() {
  const obj = currentObject();
  if (!obj) return;
  obj.name = $('#object-name').value || obj.name;
  obj.x = Math.max(0, Math.min(127, Number($('#object-x').value) || 0));
  obj.y = Math.max(0, Math.min(127, Number($('#object-y').value) || 0));
  obj.sprite = Number($('#object-sprite').value) || 1;
  obj.code = $('#object-code').value;
  renderSceneEditor();
}

function renderSceneEditor() {
  const tick = Math.floor((performance.now() / 1000) * 60);
  sceneCtx.imageSmoothingEnabled = false;
  sceneCtx.fillStyle = '#111a12';
  sceneCtx.fillRect(0, 0, sceneCanvas.width, sceneCanvas.height);
  sceneCtx.strokeStyle = 'rgba(255,255,255,.08)';
  for (let i = 0; i <= 128; i += 8) {
    sceneCtx.beginPath(); sceneCtx.moveTo(i * 4, 0); sceneCtx.lineTo(i * 4, 512); sceneCtx.stroke();
    sceneCtx.beginPath(); sceneCtx.moveTo(0, i * 4); sceneCtx.lineTo(512, i * 4); sceneCtx.stroke();
  }
  for (const obj of sceneObjects) {
    drawSpritePixels(sceneCtx, obj.x, obj.y, 4, obj.sprite, tick);
    if (obj.id === selectedObjectId) {
      sceneCtx.strokeStyle = '#fff';
      sceneCtx.lineWidth = 2;
      sceneCtx.strokeRect(obj.x * 4, obj.y * 4, 64, 64);
      sceneCtx.lineWidth = 1;
    }
  }
}

function initArt() {
  const paletteEl = $('#palette');
  palette.forEach((hex, i) => {
    const b = document.createElement('button');
    b.className = `swatch${i === color ? ' active' : ''}`;
    b.style.background = hex;
    b.title = String(i);
    b.addEventListener('click', () => {
      color = i;
      document.querySelectorAll('.swatch').forEach(el => el.classList.remove('active'));
      b.classList.add('active');
    });
    paletteEl.appendChild(b);
  });
  $('#new-sprite').addEventListener('click', newSprite);
  $('#new-frame').addEventListener('click', addFrame);
  $('#delete-frame').addEventListener('click', deleteFrame);
  $('#sprite-select').addEventListener('change', handleSpriteSelection);
  $('#frame-select').addEventListener('change', handleFrameSelection);
  $('#sprite-fps').addEventListener('input', handleSpriteFps);
  spriteCanvas.addEventListener('pointerdown', paint);
  spriteCanvas.addEventListener('pointermove', e => { if (e.buttons) paint(e); });
  renderSprite();
}

function paint(event) {
  const pixels = currentFramePixels();
  const r = spriteCanvas.getBoundingClientRect();
  const x = Math.max(0, Math.min(15, Math.floor(((event.clientX - r.left) / r.width) * 16)));
  const y = Math.max(0, Math.min(15, Math.floor(((event.clientY - r.top) / r.height) * 16)));
  pixels[y * 16 + x] = color;
  renderSprite();
  renderSceneEditor();
}

function normalizeBasPath(path) {
  let p = String(path || '').replace(/\\+/g, '/').trim();
  p = p.replace(/^\/+/, '');
  const parts = [];
  for (const part of p.split('/')) {
    if (!part || part === '.') continue;
    if (part === '..') continue;
    parts.push(part);
  }
  p = parts.join('/') || 'main.bas';
  if (!p.toLowerCase().endsWith('.bas')) p += '.bas';
  return p;
}

function saveCurrentBas() {
  basFiles.set(currentBasPath, $('#basic').value);
}

function renderBasFiles() {
  const root = $('#bas-files');
  root.textContent = '';
  [...basFiles.keys()].sort((a, b) => a.localeCompare(b)).forEach(path => {
    const button = document.createElement('button');
    button.className = `file-item${path === currentBasPath ? ' active' : ''}`;
    button.textContent = path;
    button.title = path;
    button.addEventListener('click', () => selectBasFile(path));
    root.appendChild(button);
  });
}

function selectBasFile(path) {
  saveCurrentBas();
  currentBasPath = normalizeBasPath(path);
  if (!basFiles.has(currentBasPath)) basFiles.set(currentBasPath, '');
  $('#bas-path').value = currentBasPath;
  $('#basic').value = basFiles.get(currentBasPath);
  renderBasFiles();
}

function newBasFile() {
  saveCurrentBas();
  let base = 'scripts/new.bas';
  let i = 1;
  while (basFiles.has(base)) base = `scripts/new${++i}.bas`;
  basFiles.set(base, `' ${base}\n`);
  selectBasFile(base);
}

function deleteBasFile() {
  if (currentBasPath === 'main.bas') {
    log('main.bas cannot be deleted');
    return;
  }
  basFiles.delete(currentBasPath);
  selectBasFile('main.bas');
}

function renameCurrentBas() {
  const next = normalizeBasPath($('#bas-path').value);
  if (next === currentBasPath) return;
  const text = $('#basic').value;
  basFiles.delete(currentBasPath);
  currentBasPath = next;
  basFiles.set(currentBasPath, text);
  $('#bas-path').value = currentBasPath;
  renderBasFiles();
}

function scenePoint(event) {
  const r = sceneCanvas.getBoundingClientRect();
  return {
    x: Math.max(0, Math.min(127, Math.floor(((event.clientX - r.left) / r.width) * 128))),
    y: Math.max(0, Math.min(127, Math.floor(((event.clientY - r.top) / r.height) * 128))),
  };
}

function objectAt(x, y) {
  for (let i = sceneObjects.length - 1; i >= 0; i--) {
    const o = sceneObjects[i];
    if (x >= o.x && y >= o.y && x < o.x + 16 && y < o.y + 16) return o;
  }
  return null;
}

function handleScenePointer(event) {
  const p = scenePoint(event);
  let obj = objectAt(p.x, p.y);
  if (!obj && event.type === 'pointerdown') {
    addObject(Math.max(0, p.x - 8), Math.max(0, p.y - 8));
    obj = currentObject();
  }
  if (obj) {
    selectedObjectId = obj.id;
    obj.x = Math.max(0, Math.min(112, p.x - 8));
    obj.y = Math.max(0, Math.min(112, p.y - 8));
    syncObjectForm();
    renderSceneEditor();
  }
}

function basicExpression(expr) {
  return String(expr)
    .replace(/\bTHREADS\s*\(\s*\)/gi, 'threads()')
    .replace(/\bBTN\s*\(/gi, 'btn(')
    .replace(/\bAND\b/gi, '&&')
    .replace(/\bOR\b/gi, '||')
    .replace(/\bNOT\b/gi, '!')
    .replace(/<>/g, '!=')
    .replace(/(?<![<>=!])=(?!=)/g, '==');
}

function resolveImportPath(fromPath, importPath) {
  const raw = String(importPath || '').trim();
  if (raw.startsWith('/')) return normalizeBasPath(raw);
  const baseParts = normalizeBasPath(fromPath).split('/');
  baseParts.pop();
  return normalizeBasPath([...baseParts, raw].join('/'));
}

function resolveBasicSource(entryPath = 'main.bas', seen = new Set()) {
  const path = normalizeBasPath(entryPath);
  if (seen.has(path)) return `' skipped circular import ${path}\n`;
  if (!basFiles.has(path)) throw new Error(`Missing PG BASIC import: ${path}`);
  seen.add(path);
  const out = [];
  for (const raw of basFiles.get(path).split(/\r?\n/)) {
    const m = raw.trim().match(/^IMPORT\s+["'](.+?)["']$/i);
    if (m) {
      const imported = resolveImportPath(path, m[1]);
      out.push(`' begin import ${imported}`);
      out.push(resolveBasicSource(imported, seen));
      out.push(`' end import ${imported}`);
    } else {
      out.push(raw);
    }
  }
  return out.join('\n');
}

function basicToJavaScript(source) {
  const buckets = { INIT: [], UPDATE: [], DRAW: [] };
  let section = 'DRAW';
  const stack = [];
  const globals = new Set(['x', 'y', 't']);
  const emit = line => buckets[section].push(line);
  for (const raw of source.split(/\r?\n/)) {
    let line = raw.trim();
    if (!line || line.startsWith("'") || /^REM\b/i.test(line)) continue;
    if (/^IMPORT\s+["'](.+?)["']$/i.test(line)) continue;
    const label = line.match(/^(INIT|UPDATE|DRAW)\s*:$/i);
    if (label) { section = label[1].toUpperCase(); continue; }
    const upper = line.toUpperCase();
    if (upper === 'END IF' || upper === 'ENDIF') { emit('}'); stack.pop(); continue; }
    if (upper === 'NEXT') { emit('}'); stack.pop(); continue; }
    if (upper === 'ELSE') { emit('} else {'); continue; }

    let m;
    if ((m = line.match(/^LET\s+([A-Za-z_]\w*)\s*=\s*(.+)$/i)) || (m = line.match(/^([A-Za-z_]\w*)\s*=\s*(.+)$/))) {
      emit(`${m[1]} = ${basicExpression(m[2])};`); continue;
    }
    if ((m = line.match(/^DIM\s+([A-Za-z_]\w*)\s*=\s*(.+)$/i))) { globals.add(m[1]); emit(`${m[1]} = ${basicExpression(m[2])};`); continue; }
    if ((m = line.match(/^PRINT\s+(.+)$/i))) { emit(`print(${m[1]}, 2, 2, 7);`); continue; }
    if ((m = line.match(/^CLS(?:\s+(.+))?$/i))) { emit(`cls(${m[1] || 0});`); continue; }
    if ((m = line.match(/^PSET\s+(.+),\s*(.+),\s*(.+)$/i))) { emit(`pset(${basicExpression(m[1])}, ${basicExpression(m[2])}, ${basicExpression(m[3])});`); continue; }
    if ((m = line.match(/^RECTFILL\s+(.+),\s*(.+),\s*(.+),\s*(.+),\s*(.+)$/i))) { emit(`rectfill(${basicExpression(m[1])}, ${basicExpression(m[2])}, ${basicExpression(m[3])}, ${basicExpression(m[4])}, ${basicExpression(m[5])});`); continue; }
    if ((m = line.match(/^SPR\s+(.+),\s*(.+),\s*(.+)$/i))) { emit(`spr(animSprite(${basicExpression(m[1])}), ${basicExpression(m[2])}, ${basicExpression(m[3])}, 2, 2);`); continue; }
    if ((m = line.match(/^BEEP\s+(.+),\s*(.+)$/i))) { emit(`beep(${basicExpression(m[1])}, ${basicExpression(m[2])});`); continue; }
    if ((m = line.match(/^IF\s+(.+)\s+THEN$/i))) { emit(`if (${basicExpression(m[1])}) {`); stack.push('if'); continue; }
    if ((m = line.match(/^FOR\s+([A-Za-z_]\w*)\s*=\s*(.+)\s+TO\s+(.+)$/i))) { emit(`for (${m[1]} = ${basicExpression(m[2])}; ${m[1]} <= ${basicExpression(m[3])}; ${m[1]}++) {`); stack.push('for'); continue; }
    if ((m = line.match(/^JS\s+(.+)$/i))) { emit(m[1]); continue; }
    emit(`trace(${JSON.stringify(`unknown PG BASIC: ${line}`)});`);
  }
  while (stack.length) { buckets[section].push('}'); stack.pop(); }
  return `let ${[...globals].join(', ')};\nx = 48; y = 48; t = 0;\nfunction _init(){\n${buckets.INIT.join('\n')}\n}\nfunction _update(){\nt++;\n${buckets.UPDATE.join('\n')}\n}\nfunction _draw(){\n${buckets.DRAW.join('\n')}\n}`;
}

function objectBasicToJavaScript(obj) {
  const source = obj.code || '';
  const buckets = { INIT: [], UPDATE: [], DRAW: [] };
  let section = 'DRAW';
  const vars = new Set(['x', 'y', 'sprite']);
  const objectExpr = expr => basicExpression(expr).replace(/\b[A-Za-z_]\w*\b/g, name => vars.has(name) ? `this.${name}` : name);
  const emit = line => buckets[section].push(line);
  const stack = [];
  for (const raw of source.split(/\r?\n/)) {
    const line = raw.trim();
    if (!line || line.startsWith("'") || /^REM\b/i.test(line)) continue;
    const label = line.match(/^LOCAL\s+(INIT|UPDATE|DRAW)\s*:$/i);
    if (label) { section = label[1].toUpperCase(); continue; }
    const upper = line.toUpperCase();
    if (upper === 'END IF' || upper === 'ENDIF') { emit('}'); stack.pop(); continue; }
    if (upper === 'NEXT') { emit('}'); stack.pop(); continue; }
    if (upper === 'ELSE') { emit('} else {'); continue; }
    let m;
    if ((m = line.match(/^DIM\s+([A-Za-z_]\w*)\s*=\s*(.+)$/i))) {
      vars.add(m[1]);
      emit(`this.${m[1]} = ${objectExpr(m[2])};`);
      continue;
    }
    if ((m = line.match(/^LET\s+([A-Za-z_]\w*)\s*=\s*(.+)$/i)) || (m = line.match(/^([A-Za-z_]\w*)\s*=\s*(.+)$/))) {
      vars.add(m[1]);
      emit(`this.${m[1]} = ${objectExpr(m[2])};`); continue;
    }
    if ((m = line.match(/^PRINT\s+(.+)$/i))) { emit(`print(${objectExpr(m[1])}, 2, 2, 7);`); continue; }
    if ((m = line.match(/^CLS(?:\s+(.+))?$/i))) { emit(`cls(${objectExpr(m[1] || 0)});`); continue; }
    if ((m = line.match(/^PSET\s+(.+),\s*(.+),\s*(.+)$/i))) { emit(`pset(${objectExpr(m[1])}, ${objectExpr(m[2])}, ${objectExpr(m[3])});`); continue; }
    if ((m = line.match(/^RECTFILL\s+(.+),\s*(.+),\s*(.+),\s*(.+),\s*(.+)$/i))) { emit(`rectfill(${objectExpr(m[1])}, ${objectExpr(m[2])}, ${objectExpr(m[3])}, ${objectExpr(m[4])}, ${objectExpr(m[5])});`); continue; }
    if ((m = line.match(/^SPR\s+(.+),\s*(.+),\s*(.+)$/i))) { emit(`spr(animSprite(${objectExpr(m[1])}), ${objectExpr(m[2])}, ${objectExpr(m[3])}, 2, 2);`); continue; }
    if ((m = line.match(/^BEEP\s+(.+),\s*(.+)$/i))) { emit(`beep(${basicExpression(m[1])}, ${basicExpression(m[2])});`); continue; }
    if ((m = line.match(/^IF\s+(.+)\s+THEN$/i))) { emit(`if (${objectExpr(m[1])}) {`); stack.push('if'); continue; }
    if ((m = line.match(/^FOR\s+([A-Za-z_]\w*)\s*=\s*(.+)\s+TO\s+(.+)$/i))) { vars.add(m[1]); emit(`for (this.${m[1]} = ${objectExpr(m[2])}; this.${m[1]} <= ${objectExpr(m[3])}; this.${m[1]}++) {`); stack.push('for'); continue; }
    if ((m = line.match(/^JS\s+(.+)$/i))) { emit(m[1]); continue; }
    emit(`trace(${JSON.stringify(`unknown object PG BASIC: ${line}`)});`);
  }
  while (stack.length) { buckets[section].push('}'); stack.pop(); }
  const safeName = obj.name.replace(/\W+/g, '_') || `sprite${obj.id}`;
  return `spawnObjectThread({ id:${obj.id}, name:${JSON.stringify(safeName)}, script:${JSON.stringify(obj.code || '')}, x:${obj.x|0}, y:${obj.y|0}, sprite:${obj.sprite|0}, init(){${buckets.INIT.join('\n')}}, update(){${buckets.UPDATE.join('\n')}}, draw(){${buckets.DRAW.join('\n') || 'spr(animSprite(this.sprite), this.x, this.y, 2, 2);'}} });`;
}

function sceneJavaScript() {
  return `const __animations = ${JSON.stringify(animationMetadata())};
function animSprite(id){
  const anim = __animations.find(a => a.id === id);
  if (!anim || !anim.frames.length) return id;
  return anim.frames[Math.floor(time() * Math.max(1, anim.fps || 8)) % anim.frames.length];
}
const __threads = [];
const objects = [];
function spawnThread(name, update, draw){
  const thread = { id: __threads.length + 1, name, alive: true, update, draw };
  __threads.push(thread);
  globalThis.__u8ThreadCount = __threads.length;
  return thread;
}
function spawnObjectThread(def){
  const obj = { id:def.id, name:def.name, script:def.script, x:def.x, y:def.y, sprite:def.sprite, init:def.init, update:def.update, draw:def.draw };
  objects.push(obj);
  spawnThread('object:update:' + obj.name + ':' + obj.id, () => obj.update?.call(obj), null);
  spawnThread('object:draw:' + obj.name + ':' + obj.id, null, () => obj.draw?.call(obj));
  obj.init?.call(obj);
  return obj;
}
${sceneObjects.map(objectBasicToJavaScript).join('\n')}
function _scene_init(){ }
function _scene_update(){ globalThis.__u8ThreadCount = __threads.length; for (const t of __threads) if (t.alive && t.update) t.update(); }
function _scene_draw(){ for (const t of __threads) if (t.alive && t.draw) t.draw(); }`;
}

function normalizeJavaScript(js) {
  if (!window.acorn || !window.astring) throw new Error('Acorn and Astring must be loaded.');
  const ast = window.acorn.parse(js, { ecmaVersion: 2020, sourceType: 'script' });
  return window.astring.generate(ast);
}

function compileExpression(node, out) {
  if (!node) return;
  if (node.type === 'Literal') out.push(`  const ${JSON.stringify(node.value)}`);
  else if (node.type === 'Identifier') out.push(`  load ${node.name}`);
  else if (node.type === 'CallExpression') { node.arguments.forEach(a => compileExpression(a, out)); out.push(`  call ${node.callee.name || node.callee.type} ${node.arguments.length}`); }
  else if (node.type === 'BinaryExpression' || node.type === 'LogicalExpression') { compileExpression(node.left, out); compileExpression(node.right, out); out.push(`  binary ${node.operator}`); }
  else if (node.type === 'AssignmentExpression') { compileExpression(node.right, out); out.push(`  assign ${node.left.name || node.left.type}`); }
  else if (node.type === 'UpdateExpression') out.push(`  update ${node.argument.name || node.argument.type} ${node.operator}`);
  else out.push(`  ast_expr ${JSON.stringify(node.type)}`);
}

function compileStatement(node, out) {
  if (!node) return;
  if (node.type === 'Program' || node.type === 'BlockStatement') node.body.forEach(n => compileStatement(n, out));
  else if (node.type === 'FunctionDeclaration') { out.push(`fn ${node.id.name}`); compileStatement(node.body, out); out.push(`endfn ${node.id.name}`); }
  else if (node.type === 'VariableDeclaration') node.declarations.forEach(d => { compileExpression(d.init, out); out.push(`  var ${node.kind} ${d.id.name}`); });
  else if (node.type === 'ExpressionStatement') { compileExpression(node.expression, out); out.push('  pop'); }
  else if (node.type === 'IfStatement') { compileExpression(node.test, out); out.push('  if'); compileStatement(node.consequent, out); if (node.alternate) { out.push('  else'); compileStatement(node.alternate, out); } out.push('  endif'); }
  else if (node.type === 'ForStatement') { out.push('  for'); compileStatement(node.init, out); compileExpression(node.test, out); compileExpression(node.update, out); compileStatement(node.body, out); out.push('  endfor'); }
  else out.push(`  ast_stmt ${JSON.stringify(node.type)}`);
}

function jsToAssembly(js) {
  const ast = window.acorn.parse(js, { ecmaVersion: 2020, sourceType: 'script' });
  const out = ['; M16BC-v1 assembly from PG BASIC via Acorn/Astring', '.target m16bc-v1'];
  compileStatement(ast, out);
  out.push('.end');
  return out.join('\n') + '\n';
}

function assemble(asm) {
  const lines = asm.split(/\r?\n/).map(s => s.trim()).filter(Boolean);
  const payload = encoder.encode(JSON.stringify({ format: 'M16BC-v1', lines }, null, 2));
  const out = new Uint8Array(16 + payload.length);
  out.set(encoder.encode('M16BCASM'), 0);
  new DataView(out.buffer).setUint32(8, payload.length, true);
  new DataView(out.buffer).setUint32(12, crc32(payload), true);
  out.set(payload, 16);
  return out;
}

function compileProject() {
  saveCurrentBas();
  const resolvedBasic = resolveBasicSource('main.bas');
  const mainRaw = basicToJavaScript(resolvedBasic);
  const jsRaw = `${sceneJavaScript()}\n${mainRaw}\nconst __user_init = _init;\nconst __user_update = _update;\nconst __user_draw = _draw;\n_init = function(){ _scene_init(); __user_init?.(); };\n_update = function(){ _scene_update(); __user_update?.(); };\n_draw = function(){ __user_draw?.(); _scene_draw(); };`;
  const js = normalizeJavaScript(jsRaw);
  const asm = jsToAssembly(js);
  const bytecode = assemble(asm);
  const sound = { note: +$('#note').value, duration: +$('#duration').value, wave: $('#wave').value };
  const scene = {
    threading: 'cooperative-object-threads',
    animations: animationMetadata(),
    objects: sceneObjects.map(o => ({ ...o })),
    threads: sceneObjects.flatMap(o => [
      { objectId: o.id, name: `${o.name}:update`, scriptHash: crc32(encoder.encode(o.code || '')), phase: 'update' },
      { objectId: o.id, name: `${o.name}:draw`, scriptHash: crc32(encoder.encode(o.code || '')), phase: 'draw' },
    ]),
  };
  compiled = { js, asm, bytecode, sound, scene, basic: Object.fromEntries(basFiles) };
  $('#js-out').textContent = js;
  $('#asm-out').textContent = asm;
  log(`compiled ${js.length} JS chars, ${asm.split('\n').length} assembly lines, ${bytecode.length} bytecode bytes`);
  return compiled;
}

function makeRuntimeAPI(ctx) {
  const img = ctx.createImageData(W, H);
  const rgba = palette.map(hex => {
    const n = parseInt(hex.slice(1), 16);
    return [(n >> 16) & 255, (n >> 8) & 255, n & 255, 255];
  });
  const fb = new Uint8Array(W * H);
  const flush = () => {
    for (let i = 0, j = 0; i < fb.length; i++, j += 4) img.data.set(rgba[fb[i] & 15], j);
    ctx.putImageData(img, 0, 0);
  };
  const pset = (x, y, c) => {
    x |= 0; y |= 0;
    if (x >= 0 && y >= 0 && x < W && y < H) fb[y * W + x] = c & 15;
  };
  return {
    cls(c = 0) { fb.fill(c & 15); },
    pset,
    rectfill(x0, y0, x1, y1, c) { for (let y = y0 | 0; y <= (y1 | 0); y++) for (let x = x0 | 0; x <= (x1 | 0); x++) pset(x, y, c); },
    print(text, x, y, c) { ctx.fillStyle = palette[c & 15]; ctx.font = '8px monospace'; ctx.fillText(String(text), x * 2, y * 2); },
    spr(n, x, y) {
      const tick = ((performance.now() - start) / 1000) * 60;
      const frame = spriteFramePixels(n, tick);
      for (let sy = 0; sy < 16; sy++) for (let sx = 0; sx < 16; sx++) {
        const c = frame[sy * 16 + sx];
        if (c) pset((x | 0) + sx, (y | 0) + sy, c);
      }
    },
    beep,
    trace: log,
    btn(index) {
      const groups = [
        ['arrowleft', 'a'],
        ['arrowright', 'd'],
        ['arrowup', 'w'],
        ['arrowdown', 's'],
        ['z', 'j', ' ', 'x', 'k', 'enter'],
      ];
      return (groups[index | 0] || []).some(key => keysDown.has(key));
    },
    threads: () => globalThis.__u8ThreadCount || 0,
    time: () => (performance.now() - start) / 1000,
    flush,
  };
}

function runProject() {
  const c = compileProject();
  cancelAnimationFrame(raf);
  const ctx = screenCtx;
  ctx.imageSmoothingEnabled = false;
  const api = makeRuntimeAPI(ctx);
  const names = Object.keys(api);
  const mod = new Function(...names, `${c.js}\nreturn { _init: typeof _init === 'function' ? _init : null, _update: typeof _update === 'function' ? _update : null, _draw: typeof _draw === 'function' ? _draw : null };`)(...Object.values(api));
  start = performance.now();
  mod._init?.();
  const frame = () => {
    mod._update?.();
    mod._draw?.();
    api.flush();
    raf = requestAnimationFrame(frame);
  };
  frame();
  log('running preview');
}

function noteToFreq(note) {
  return 440 * Math.pow(2, (note - 69) / 12);
}

function beep(freq = noteToFreq(+$('#note').value), duration = +$('#duration').value) {
  const Ctx = window.AudioContext || window.webkitAudioContext;
  const ctx = new Ctx();
  const osc = ctx.createOscillator();
  const gain = ctx.createGain();
  osc.type = $('#wave').value;
  osc.frequency.value = freq;
  gain.gain.setValueAtTime(0.0001, ctx.currentTime);
  gain.gain.exponentialRampToValueAtTime(0.25, ctx.currentTime + 0.01);
  gain.gain.exponentialRampToValueAtTime(0.0001, ctx.currentTime + duration);
  osc.connect(gain).connect(ctx.destination);
  osc.start();
  osc.stop(ctx.currentTime + duration + 0.03);
}

function exportImage() {
  const c = compiled || compileProject();
  const meta = {
    title: 'Creator Cart',
    author: 'Mega 16 Creator',
    main: '/cart/main.js',
    source: '/src/main.bas',
    assembly: '/cart/main.asm',
    bytecode: '/cart/main.bc',
    sounds: '/cart/sounds.jso',
    scene: '/cart/scene.jso',
    animations: '/cart/anims.jso',
    format: 'mbr-fat16-m16cart.img',
  };
  const files = {
    '/meta.jso': meta,
    '/readme.txt': 'Non-bootable Mega 16 FAT16 cart made by creator.html.',
    '/cart/meta.jso': meta,
    '/cart/main.js': c.js,
    '/cart/main.asm': c.asm,
    '/cart/main.bc': c.bytecode,
    '/cart/sprites.bin': spriteBytes(),
    '/cart/scene.jso': c.scene,
    '/cart/anims.jso': animationMetadata(),
    '/cart/sounds.jso': c.sound,
    '/cart/readme.txt': 'Source, assembly, bytecode, art, and sounds are all included.',
  };
  for (const [path, text] of Object.entries(c.basic)) {
    files[`/src/${normalizeBasPath(path)}`] = text;
  }
  saveBytes(createFat16Image('CREATORCART', files), 'creator-cart.m16cart.img');
  log('exported creator-cart.m16cart.img');
}

let blocklyWorkspace = null;
let blocklyLoading = null;
let blocklyBlocksDefined = false;

const extraValueBlockGroups = [
  {
    category: 'Math Helpers',
    colour: 45,
    blocks: [
      ['pg_expr_time_seconds', 'time seconds', [], 'time()'],
      ['pg_expr_time_frames', 'frame tick', [], 't'],
      ['pg_expr_random', 'random 0..1', [], 'Math.random()'],
      ['pg_expr_random_int', 'random int %1 to %2', [['MIN', 0], ['MAX', 10]], 'Math.floor(Math.random() * (B - A + 1)) + A'],
      ['pg_expr_floor', 'floor %1', [['A', 0]], 'Math.floor(A)'],
      ['pg_expr_ceil', 'ceil %1', [['A', 0]], 'Math.ceil(A)'],
      ['pg_expr_round', 'round %1', [['A', 0]], 'Math.round(A)'],
      ['pg_expr_abs', 'absolute %1', [['A', 0]], 'Math.abs(A)'],
      ['pg_expr_min', 'min %1 %2', [['A', 0], ['B', 10]], 'Math.min(A, B)'],
      ['pg_expr_max', 'max %1 %2', [['A', 0], ['B', 10]], 'Math.max(A, B)'],
      ['pg_expr_clamp', 'clamp %1 %2 %3', [['A', 'x'], ['B', 0], ['C', 112]], 'Math.max(B, Math.min(C, A))'],
      ['pg_expr_mod', 'mod %1 by %2', [['A', 't'], ['B', 60]], '((A) % (B))'],
      ['pg_expr_pow', 'power %1 ^ %2', [['A', 2], ['B', 3]], 'Math.pow(A, B)'],
      ['pg_expr_sqrt', 'sqrt %1', [['A', 16]], 'Math.sqrt(A)'],
      ['pg_expr_sin', 'sin %1', [['A', 'time()']], 'Math.sin(A)'],
      ['pg_expr_cos', 'cos %1', [['A', 'time()']], 'Math.cos(A)'],
      ['pg_expr_tan', 'tan %1', [['A', 'time()']], 'Math.tan(A)'],
      ['pg_expr_atan2', 'angle y %1 x %2', [['A', 'dy'], ['B', 'dx']], 'Math.atan2(A, B)'],
      ['pg_expr_lerp', 'lerp %1 to %2 by %3', [['A', 'x'], ['B', 64], ['C', 0.1]], 'A + (B - A) * C'],
      ['pg_expr_sine_wave', 'sine wave amp %1 speed %2', [['A', 8], ['B', 3]], 'Math.sin(time() * B) * A'],
      ['pg_expr_cos_wave', 'cos wave amp %1 speed %2', [['A', 8], ['B', 3]], 'Math.cos(time() * B) * A'],
      ['pg_expr_distance', 'distance x %1 y %2 to x %3 y %4', [['A', 'x'], ['B', 'y'], ['C', 64], ['D', 64]], 'Math.hypot(C - A, D - B)'],
      ['pg_expr_angle_to', 'angle x %1 y %2 to x %3 y %4', [['A', 'x'], ['B', 'y'], ['C', 64], ['D', 64]], 'Math.atan2(D - B, C - A)'],
      ['pg_expr_sign', 'sign %1', [['A', 'dx']], 'Math.sign(A)'],
      ['pg_expr_negate', 'negative %1', [['A', 1]], '-(A)'],
      ['pg_expr_percent', '%1 percent of %2', [['A', 50], ['B', 100]], '(A / 100) * B'],
      ['pg_expr_wrap', 'wrap %1 between 0 and %2', [['A', 'x'], ['B', 128]], '(((A) % (B)) + (B)) % (B)'],
      ['pg_expr_snap', 'snap %1 to grid %2', [['A', 'x'], ['B', 8]], 'Math.round(A / B) * B'],
      ['pg_expr_midpoint', 'midpoint %1 %2', [['A', 'x'], ['B', 'targetX']], '(A + B) / 2'],
      ['pg_expr_pick', 'pick %1 or %2', [['A', 1], ['B', -1]], '(Math.random() < 0.5 ? A : B)'],
    ],
  },
  {
    category: 'Logic Helpers',
    colour: 120,
    blocks: [
      ['pg_expr_between', '%1 between %2 and %3', [['A', 'x'], ['B', 0], ['C', 127]], '(A >= B && A <= C)'],
      ['pg_expr_outside', '%1 outside %2 and %3', [['A', 'x'], ['B', 0], ['C', 127]], '(A < B || A > C)'],
      ['pg_expr_aabb', 'rect hit ax %1 ay %2 aw %3 ah %4 bx %5 by %6 bw %7 bh %8', [['A', 'x'], ['B', 'y'], ['C', 16], ['D', 16], ['E', 'tx'], ['F', 'ty'], ['G', 16], ['H', 16]], '(A < E + G && A + C > E && B < F + H && B + D > F)'],
      ['pg_expr_circle_hit', 'circle hit x %1 y %2 r %3 x %4 y %5 r %6', [['A', 'x'], ['B', 'y'], ['C', 8], ['D', 'tx'], ['E', 'ty'], ['F', 8]], '(Math.hypot(D - A, E - B) <= C + F)'],
      ['pg_expr_not', 'not %1', [['A', 0]], '!(A)'],
      ['pg_expr_and3', '%1 and %2 and %3', [['A', 1], ['B', 1], ['C', 1]], '(A && B && C)'],
      ['pg_expr_or3', '%1 or %2 or %3', [['A', 0], ['B', 0], ['C', 1]], '(A || B || C)'],
      ['pg_expr_choose_if', 'if %1 then %2 else %3', [['A', 1], ['B', 10], ['C', 0]], '(A ? B : C)'],
      ['pg_expr_button_any', 'any direction pressed', [], '(BTN(0) || BTN(1) || BTN(2) || BTN(3))'],
      ['pg_expr_button_action', 'action pressed', [], 'BTN(4)'],
      ['pg_expr_every_frames', 'every %1 frames', [['A', 30]], '(t % A === 0)'],
      ['pg_expr_blink', 'blink every %1 frames', [['A', 15]], '(Math.floor(t / A) % 2 === 0)'],
      ['pg_expr_chance', 'chance 1 in %1', [['A', 60]], '(Math.random() < 1 / A)'],
      ['pg_expr_near', '%1 near %2 within %3', [['A', 'x'], ['B', 64], ['C', 4]], '(Math.abs(A - B) <= C)'],
      ['pg_expr_facing_left', 'moving left %1', [['A', 'dx']], '(A < 0)'],
      ['pg_expr_facing_right', 'moving right %1', [['A', 'dx']], '(A > 0)'],
      ['pg_expr_screen_left', 'past left %1', [['A', 'x']], '(A < -16)'],
      ['pg_expr_screen_right', 'past right %1', [['A', 'x']], '(A > 128)'],
      ['pg_expr_screen_top', 'past top %1', [['A', 'y']], '(A < -16)'],
      ['pg_expr_screen_bottom', 'past bottom %1', [['A', 'y']], '(A > 128)'],
    ],
  },
];

const extraStatementBlockGroups = [
  {
    category: 'Drawing Helpers',
    colour: 160,
    blocks: [
      ['pg_draw_print_at', 'print %1 at x %2 y %3 color %4', [['TEXT', '"HI"'], ['X', 2], ['Y', 2], ['COLOR', 7]], v => `JS print(${v.TEXT}, ${v.X}, ${v.Y}, ${v.COLOR})`],
      ['pg_draw_text_shadow', 'shadow text %1 at x %2 y %3', [['TEXT', '"READY"'], ['X', 2], ['Y', 2]], v => `JS print(${v.TEXT}, ${v.X} + 1, ${v.Y} + 1, 0); print(${v.TEXT}, ${v.X}, ${v.Y}, 7)`],
      ['pg_draw_center_text', 'center text %1 y %2 color %3', [['TEXT', '"LEVEL 1"'], ['Y', 10], ['COLOR', 7]], v => `JS print(${v.TEXT}, 64 - String(${v.TEXT}).length * 2, ${v.Y}, ${v.COLOR})`],
      ['pg_draw_outline_rect', 'outline rect x %1 y %2 w %3 h %4 color %5', [['X', 8], ['Y', 8], ['W', 32], ['H', 16], ['COLOR', 7]], v => `RECTFILL ${v.X}, ${v.Y}, ${v.X} + ${v.W}, ${v.Y}, ${v.COLOR}\nRECTFILL ${v.X}, ${v.Y} + ${v.H}, ${v.X} + ${v.W}, ${v.Y} + ${v.H}, ${v.COLOR}\nRECTFILL ${v.X}, ${v.Y}, ${v.X}, ${v.Y} + ${v.H}, ${v.COLOR}\nRECTFILL ${v.X} + ${v.W}, ${v.Y}, ${v.X} + ${v.W}, ${v.Y} + ${v.H}, ${v.COLOR}`],
      ['pg_draw_bar', 'bar x %1 y %2 w %3 h %4 value %5 max %6 color %7', [['X', 4], ['Y', 4], ['W', 40], ['H', 5], ['VALUE', 'hp'], ['MAX', 100], ['COLOR', 11]], v => `RECTFILL ${v.X}, ${v.Y}, ${v.X} + (${v.W} * ${v.VALUE} / ${v.MAX}), ${v.Y} + ${v.H}, ${v.COLOR}`],
      ['pg_draw_health_bar', 'health bar hp %1 max %2', [['HP', 'hp'], ['MAX', 100]], v => `RECTFILL 4, 4, 44, 8, 2\nRECTFILL 4, 4, 4 + (40 * ${v.HP} / ${v.MAX}), 8, 11`],
      ['pg_draw_score', 'score %1', [['SCORE', 'score']], v => `JS print("SCORE " + ${v.SCORE}, 2, 2, 7)`],
      ['pg_draw_lives', 'lives %1 sprite %2', [['LIVES', 'lives'], ['SPRITE', 1]], v => `JS for (let i = 0; i < ${v.LIVES}; i++) spr(animSprite(${v.SPRITE}), 2 + i * 10, 116)`],
      ['pg_draw_flash', 'screen flash color %1 every %2', [['COLOR', 7], ['FRAMES', 6]], v => `IF t < ${v.FRAMES} THEN\n  CLS ${v.COLOR}\nEND IF`],
      ['pg_draw_checker_bg', 'checker bg colors %1 %2 size %3', [['A', 1], ['B', 5], ['SIZE', 8]], v => `JS for (let yy = 0; yy < 128; yy += ${v.SIZE}) for (let xx = 0; xx < 128; xx += ${v.SIZE}) rectfill(xx, yy, xx + ${v.SIZE} - 1, yy + ${v.SIZE} - 1, ((xx / ${v.SIZE} + yy / ${v.SIZE}) & 1) ? ${v.A} : ${v.B})`],
      ['pg_draw_stars', 'star field count %1 color %2', [['COUNT', 32], ['COLOR', 7]], v => `JS for (let i = 0; i < ${v.COUNT}; i++) pset((i * 37 + t) % 128, (i * 53) % 128, ${v.COLOR})`],
      ['pg_draw_ground', 'ground y %1 color %2', [['Y', 108], ['COLOR', 3]], v => `RECTFILL 0, ${v.Y}, 127, 127, ${v.COLOR}`],
      ['pg_draw_skyline', 'skyline color %1', [['COLOR', 5]], v => `JS for (let i = 0; i < 8; i++) rectfill(i * 16, 96 - ((i * 13) % 32), i * 16 + 12, 127, ${v.COLOR})`],
      ['pg_draw_sprite_center', 'sprite %1 centered at x %2 y %3', [['SPRITE', 1], ['X', 64], ['Y', 64]], v => `SPR ${v.SPRITE}, ${v.X} - 8, ${v.Y} - 8`],
      ['pg_draw_sprite_blink', 'blink sprite %1 x %2 y %3 rate %4', [['SPRITE', 1], ['X', 'x'], ['Y', 'y'], ['RATE', 8]], v => `IF Math.floor(t / ${v.RATE}) % 2 = 0 THEN\n  SPR ${v.SPRITE}, ${v.X}, ${v.Y}\nEND IF`],
      ['pg_draw_sprite_shadow', 'shadow sprite %1 x %2 y %3', [['SPRITE', 1], ['X', 'x'], ['Y', 'y']], v => `RECTFILL ${v.X} + 3, ${v.Y} + 14, ${v.X} + 13, ${v.Y} + 16, 0\nSPR ${v.SPRITE}, ${v.X}, ${v.Y}`],
      ['pg_draw_crosshair', 'crosshair x %1 y %2 color %3', [['X', 'x'], ['Y', 'y'], ['COLOR', 8]], v => `RECTFILL ${v.X} - 4, ${v.Y}, ${v.X} + 4, ${v.Y}, ${v.COLOR}\nRECTFILL ${v.X}, ${v.Y} - 4, ${v.X}, ${v.Y} + 4, ${v.COLOR}`],
      ['pg_draw_vignette', 'simple border color %1', [['COLOR', 0]], v => `RECTFILL 0, 0, 127, 1, ${v.COLOR}\nRECTFILL 0, 126, 127, 127, ${v.COLOR}\nRECTFILL 0, 0, 1, 127, ${v.COLOR}\nRECTFILL 126, 0, 127, 127, ${v.COLOR}`],
      ['pg_draw_tile_row', 'tile row sprite %1 y %2 count %3', [['SPRITE', 1], ['Y', 112], ['COUNT', 8]], v => `JS for (let i = 0; i < ${v.COUNT}; i++) spr(animSprite(${v.SPRITE}), i * 16, ${v.Y})`],
      ['pg_draw_parallax_dots', 'parallax dots color %1 speed %2', [['COLOR', 6], ['SPEED', 0.5]], v => `JS for (let i = 0; i < 24; i++) pset((i * 29 - t * ${v.SPEED}) & 127, (i * 41) & 127, ${v.COLOR})`],
    ],
  },
  {
    category: 'Game Helpers',
    colour: 75,
    blocks: [
      ['pg_game_velocity', 'move %1 %2 by velocity %3 %4', [['X', 'x'], ['Y', 'y'], ['DX', 'dx'], ['DY', 'dy']], v => `${v.X} = ${v.X} + ${v.DX}\n${v.Y} = ${v.Y} + ${v.DY}`],
      ['pg_game_accel', 'accelerate %1 by %2', [['V', 'dx'], ['A', 0.2]], v => `${v.V} = ${v.V} + ${v.A}`],
      ['pg_game_friction', 'friction %1 amount %2', [['V', 'dx'], ['AMOUNT', 0.85]], v => `${v.V} = ${v.V} * ${v.AMOUNT}`],
      ['pg_game_gravity', 'gravity %1 amount %2 max %3', [['DY', 'dy'], ['G', 0.3], ['MAX', 4]], v => `${v.DY} = Math.min(${v.MAX}, ${v.DY} + ${v.G})`],
      ['pg_game_jump', 'jump button sets %1 to %2 when %3', [['DY', 'dy'], ['POWER', -5], ['GROUNDED', 'grounded']], v => `IF BTN(4) AND ${v.GROUNDED} THEN\n  ${v.DY} = ${v.POWER}\nEND IF`],
      ['pg_game_platformer', 'platformer x %1 y %2 dx %3 dy %4 speed %5 jump %6 floor %7', [['X', 'x'], ['Y', 'y'], ['DX', 'dx'], ['DY', 'dy'], ['SPEED', 0.4], ['JUMP', -5], ['FLOOR', 96]], v => `IF BTN(0) THEN\n  ${v.DX} = ${v.DX} - ${v.SPEED}\nEND IF\nIF BTN(1) THEN\n  ${v.DX} = ${v.DX} + ${v.SPEED}\nEND IF\nIF BTN(4) AND ${v.Y} >= ${v.FLOOR} THEN\n  ${v.DY} = ${v.JUMP}\nEND IF\n${v.DY} = Math.min(5, ${v.DY} + 0.3)\n${v.X} = ${v.X} + ${v.DX}\n${v.Y} = ${v.Y} + ${v.DY}\n${v.DX} = ${v.DX} * 0.82\nIF ${v.Y} > ${v.FLOOR} THEN\n  ${v.Y} = ${v.FLOOR}\n  ${v.DY} = 0\nEND IF`],
      ['pg_game_wrap_x', 'wrap x %1 width %2', [['X', 'x'], ['WIDTH', 128]], v => `${v.X} = (((${v.X}) % ${v.WIDTH}) + ${v.WIDTH}) % ${v.WIDTH}`],
      ['pg_game_wrap_y', 'wrap y %1 height %2', [['Y', 'y'], ['HEIGHT', 128]], v => `${v.Y} = (((${v.Y}) % ${v.HEIGHT}) + ${v.HEIGHT}) % ${v.HEIGHT}`],
      ['pg_game_clamp_screen', 'clamp sprite x %1 y %2', [['X', 'x'], ['Y', 'y']], v => `${v.X} = Math.max(0, Math.min(112, ${v.X}))\n${v.Y} = Math.max(0, Math.min(112, ${v.Y}))`],
      ['pg_game_chase_x', 'chase x %1 target %2 speed %3', [['X', 'x'], ['TARGET', 'tx'], ['SPEED', 1]], v => `${v.X} = ${v.X} + Math.sign(${v.TARGET} - ${v.X}) * ${v.SPEED}`],
      ['pg_game_chase_y', 'chase y %1 target %2 speed %3', [['Y', 'y'], ['TARGET', 'ty'], ['SPEED', 1]], v => `${v.Y} = ${v.Y} + Math.sign(${v.TARGET} - ${v.Y}) * ${v.SPEED}`],
      ['pg_game_patrol_x', 'patrol x %1 dx %2 min %3 max %4', [['X', 'x'], ['DX', 'dx'], ['MIN', 0], ['MAX', 112]], v => `${v.X} = ${v.X} + ${v.DX}\nIF ${v.X} < ${v.MIN} OR ${v.X} > ${v.MAX} THEN\n  ${v.DX} = -${v.DX}\nEND IF`],
      ['pg_game_patrol_y', 'patrol y %1 dy %2 min %3 max %4', [['Y', 'y'], ['DY', 'dy'], ['MIN', 0], ['MAX', 112]], v => `${v.Y} = ${v.Y} + ${v.DY}\nIF ${v.Y} < ${v.MIN} OR ${v.Y} > ${v.MAX} THEN\n  ${v.DY} = -${v.DY}\nEND IF`],
      ['pg_game_button_dx', 'set dx %1 from arrows speed %2', [['DX', 'dx'], ['SPEED', 1]], v => `${v.DX} = 0\nIF BTN(0) THEN\n  ${v.DX} = -${v.SPEED}\nEND IF\nIF BTN(1) THEN\n  ${v.DX} = ${v.SPEED}\nEND IF`],
      ['pg_game_button_dy', 'set dy %1 from arrows speed %2', [['DY', 'dy'], ['SPEED', 1]], v => `${v.DY} = 0\nIF BTN(2) THEN\n  ${v.DY} = -${v.SPEED}\nEND IF\nIF BTN(3) THEN\n  ${v.DY} = ${v.SPEED}\nEND IF`],
      ['pg_game_grid_move', 'grid move x %1 y %2 step %3', [['X', 'x'], ['Y', 'y'], ['STEP', 16]], v => `IF BTN(0) THEN\n  ${v.X} = ${v.X} - ${v.STEP}\nEND IF\nIF BTN(1) THEN\n  ${v.X} = ${v.X} + ${v.STEP}\nEND IF\nIF BTN(2) THEN\n  ${v.Y} = ${v.Y} - ${v.STEP}\nEND IF\nIF BTN(3) THEN\n  ${v.Y} = ${v.Y} + ${v.STEP}\nEND IF`],
      ['pg_game_timer', 'tick timer %1', [['TIMER', 'timer']], v => `${v.TIMER} = ${v.TIMER} + 1`],
      ['pg_game_countdown', 'countdown %1', [['TIMER', 'timer']], v => `${v.TIMER} = Math.max(0, ${v.TIMER} - 1)`],
      ['pg_game_cooldown', 'cooldown %1 fire when action reset %2', [['TIMER', 'cooldown'], ['RESET', 20]], v => `IF ${v.TIMER} > 0 THEN\n  ${v.TIMER} = ${v.TIMER} - 1\nEND IF\nIF BTN(4) AND ${v.TIMER} = 0 THEN\n  ${v.TIMER} = ${v.RESET}\nEND IF`],
      ['pg_game_add_score', 'add %1 to score %2', [['AMOUNT', 10], ['SCORE', 'score']], v => `${v.SCORE} = ${v.SCORE} + ${v.AMOUNT}`],
      ['pg_game_lose_life', 'lose life %1 if hit %2', [['LIVES', 'lives'], ['HIT', 'hit']], v => `IF ${v.HIT} THEN\n  ${v.LIVES} = ${v.LIVES} - 1\nEND IF`],
      ['pg_game_invuln', 'invulnerable timer %1 when hit %2 reset %3', [['TIMER', 'invuln'], ['HIT', 'hit'], ['RESET', 60]], v => `IF ${v.TIMER} > 0 THEN\n  ${v.TIMER} = ${v.TIMER} - 1\nEND IF\nIF ${v.HIT} AND ${v.TIMER} = 0 THEN\n  ${v.TIMER} = ${v.RESET}\nEND IF`],
      ['pg_game_collect', 'collect if player %1 %2 item %3 %4 score %5', [['PX', 'x'], ['PY', 'y'], ['IX', 'coinX'], ['IY', 'coinY'], ['SCORE', 'score']], v => `IF Math.abs(${v.PX} - ${v.IX}) < 12 AND Math.abs(${v.PY} - ${v.IY}) < 12 THEN\n  ${v.SCORE} = ${v.SCORE} + 1\n  ${v.IX} = Math.random() * 112\n  ${v.IY} = Math.random() * 112\nEND IF`],
      ['pg_game_bob', 'bob %1 base %2 amp %3 speed %4', [['Y', 'y'], ['BASE', 48], ['AMP', 4], ['SPEED', 4]], v => `${v.Y} = ${v.BASE} + Math.sin(time() * ${v.SPEED}) * ${v.AMP}`],
      ['pg_game_shake_decay', 'decay shake %1', [['SHAKE', 'shake']], v => `${v.SHAKE} = Math.max(0, ${v.SHAKE} - 1)`],
      ['pg_game_reset_fall', 'reset x %1 y %2 if below %3', [['X', 'x'], ['Y', 'y'], ['LIMIT', 140]], v => `IF ${v.Y} > ${v.LIMIT} THEN\n  ${v.X} = 48\n  ${v.Y} = 48\nEND IF`],
      ['pg_game_face_from_dx', 'face %1 from dx %2', [['FACE', 'face'], ['DX', 'dx']], v => `IF ${v.DX} < 0 THEN\n  ${v.FACE} = -1\nEND IF\nIF ${v.DX} > 0 THEN\n  ${v.FACE} = 1\nEND IF`],
      ['pg_game_spawn_point', 'set %1 %2 to spawn %3 %4', [['X', 'x'], ['Y', 'y'], ['SX', 48], ['SY', 48]], v => `${v.X} = ${v.SX}\n${v.Y} = ${v.SY}`],
      ['pg_game_camera_follow', 'camera %1 %2 follow %3 %4', [['CX', 'camX'], ['CY', 'camY'], ['X', 'x'], ['Y', 'y']], v => `${v.CX} = ${v.CX} + (${v.X} - 56 - ${v.CX}) * 0.1\n${v.CY} = ${v.CY} + (${v.Y} - 56 - ${v.CY}) * 0.1`],
      ['pg_game_keep_distance', 'keep %1 %2 away from %3 %4 dist %5', [['X', 'x'], ['Y', 'y'], ['TX', 'tx'], ['TY', 'ty'], ['DIST', 24]], v => `IF Math.hypot(${v.X} - ${v.TX}, ${v.Y} - ${v.TY}) < ${v.DIST} THEN\n  ${v.X} = ${v.X} + Math.sign(${v.X} - ${v.TX})\n  ${v.Y} = ${v.Y} + Math.sign(${v.Y} - ${v.TY})\nEND IF`],
    ],
  },
  {
    category: 'Sound Helpers',
    colour: 300,
    blocks: [
      ['pg_sound_c4', 'note C4', [], () => 'BEEP 261.63, 0.12'],
      ['pg_sound_d4', 'note D4', [], () => 'BEEP 293.66, 0.12'],
      ['pg_sound_e4', 'note E4', [], () => 'BEEP 329.63, 0.12'],
      ['pg_sound_f4', 'note F4', [], () => 'BEEP 349.23, 0.12'],
      ['pg_sound_g4', 'note G4', [], () => 'BEEP 392, 0.12'],
      ['pg_sound_a4', 'note A4', [], () => 'BEEP 440, 0.12'],
      ['pg_sound_b4', 'note B4', [], () => 'BEEP 493.88, 0.12'],
      ['pg_sound_c5', 'note C5', [], () => 'BEEP 523.25, 0.12'],
      ['pg_sound_jump', 'jump sfx', [], () => 'BEEP 620, 0.08'],
      ['pg_sound_coin', 'coin sfx', [], () => 'BEEP 880, 0.06'],
      ['pg_sound_hit', 'hit sfx', [], () => 'BEEP 140, 0.12'],
      ['pg_sound_laser', 'laser sfx', [], () => 'BEEP 1200, 0.04'],
      ['pg_sound_powerup', 'powerup sfx', [], () => 'BEEP 660, 0.07\nBEEP 880, 0.07'],
      ['pg_sound_alarm', 'alarm every %1 frames', [['FRAMES', 30]], v => `IF t % ${v.FRAMES} = 0 THEN\n  BEEP 220, 0.05\nEND IF`],
      ['pg_sound_metronome', 'metronome every %1 frames freq %2', [['FRAMES', 60], ['FREQ', 440]], v => `IF t % ${v.FRAMES} = 0 THEN\n  BEEP ${v.FREQ}, 0.04\nEND IF`],
    ],
  },
  {
    category: 'Flow Shortcuts',
    colour: 120,
    blocks: [
      ['pg_flow_every', 'every %1 frames %2', [['FRAMES', 30]], v => `IF t % ${v.FRAMES} = 0 THEN\n${statementLines(v.block, 'BODY').join('\n')}\nEND IF`, 'BODY'],
      ['pg_flow_when_button', 'when button %1 %2', [['BUTTON', 4]], v => `IF ${buttonCondition(v.BUTTON)} THEN\n${statementLines(v.block, 'BODY').join('\n')}\nEND IF`, 'BODY'],
      ['pg_flow_when_overlap', 'when overlap ax %1 ay %2 bx %3 by %4 %5', [['AX', 'x'], ['AY', 'y'], ['BX', 'tx'], ['BY', 'ty']], v => `IF ${v.AX} < ${v.BX} + 16 AND ${v.AX} + 16 > ${v.BX} AND ${v.AY} < ${v.BY} + 16 AND ${v.AY} + 16 > ${v.BY} THEN\n${statementLines(v.block, 'BODY').join('\n')}\nEND IF`, 'BODY'],
      ['pg_flow_repeat', 'repeat %1 times with %2 %3', [['COUNT', 5], ['I', 'i']], v => `FOR ${fieldValue(v.block, 'I', 'i')} = 0 TO ${v.COUNT} - 1\n${statementLines(v.block, 'BODY').join('\n')}\nNEXT`, 'BODY'],
      ['pg_flow_if_action_once', 'if action once using %1 %2', [['HELD', 'actionHeld']], v => `IF BTN(4) AND NOT ${fieldValue(v.block, 'HELD', 'actionHeld')} THEN\n${statementLines(v.block, 'BODY').join('\n')}\nEND IF\n${fieldValue(v.block, 'HELD', 'actionHeld')} = BTN(4)`, 'BODY'],
    ],
  },
];

extraValueBlockGroups.push(
  {
    category: 'Screen Values',
    colour: 190,
    blocks: [
      ['pg_expr_screen_width', 'screen width', [], '128'],
      ['pg_expr_screen_height', 'screen height', [], '128'],
      ['pg_expr_screen_center_x', 'screen center x', [], '64'],
      ['pg_expr_screen_center_y', 'screen center y', [], '64'],
      ['pg_expr_sprite_width', 'sprite width', [], '16'],
      ['pg_expr_sprite_height', 'sprite height', [], '16'],
      ['pg_expr_play_left', 'playfield left', [], '0'],
      ['pg_expr_play_right', 'playfield right', [], '127'],
      ['pg_expr_play_top', 'playfield top', [], '0'],
      ['pg_expr_play_bottom', 'playfield bottom', [], '127'],
      ['pg_expr_safe_left', 'safe left', [], '8'],
      ['pg_expr_safe_right', 'safe right', [], '119'],
      ['pg_expr_safe_top', 'safe top', [], '8'],
      ['pg_expr_safe_bottom', 'safe bottom', [], '119'],
      ['pg_expr_ground_y', 'default ground y', [], '108'],
      ['pg_expr_tile_px', 'tile %1 to pixels', [['A', 'tile']], 'A * 16'],
      ['pg_expr_px_tile', 'pixels %1 to tile', [['A', 'x']], 'Math.floor(A / 16)'],
      ['pg_expr_grid_center', 'grid %1 center', [['A', 'tile']], 'A * 16 + 8'],
      ['pg_expr_screen_progress_x', 'x %1 progress', [['A', 'x']], 'A / 127'],
      ['pg_expr_screen_progress_y', 'y %1 progress', [['A', 'y']], 'A / 127'],
    ],
  },
  {
    category: 'Game Values 2',
    colour: 75,
    blocks: [
      ['pg_expr_axis_x', 'horizontal axis', [], '(BTN(1) ? 1 : 0) - (BTN(0) ? 1 : 0)'],
      ['pg_expr_axis_y', 'vertical axis', [], '(BTN(3) ? 1 : 0) - (BTN(2) ? 1 : 0)'],
      ['pg_expr_dir4_speed_x', 'dir x speed %1', [['A', 1]], '((BTN(1) ? 1 : 0) - (BTN(0) ? 1 : 0)) * A'],
      ['pg_expr_dir4_speed_y', 'dir y speed %1', [['A', 1]], '((BTN(3) ? 1 : 0) - (BTN(2) ? 1 : 0)) * A'],
      ['pg_expr_flap_velocity', 'flap velocity if action %1 else %2', [['A', -4], ['B', 'dy']], '(BTN(4) ? A : B)'],
      ['pg_expr_health_percent', 'hp %1 over max %2 percent', [['A', 'hp'], ['B', 100]], 'Math.max(0, Math.min(1, A / B))'],
      ['pg_expr_is_dead', 'hp %1 is dead', [['A', 'hp']], '(A <= 0)'],
      ['pg_expr_score_bonus', 'score %1 with multiplier %2', [['A', 'score'], ['B', 2]], 'A * B'],
      ['pg_expr_level_seconds', 'level seconds', [], 'Math.floor(t / 30)'],
      ['pg_expr_countdown_seconds', 'timer %1 seconds left', [['A', 'timer']], 'Math.ceil(A / 30)'],
      ['pg_expr_spawn_left_x', 'spawn left x', [], '-16'],
      ['pg_expr_spawn_right_x', 'spawn right x', [], '144'],
      ['pg_expr_spawn_top_y', 'spawn top y', [], '-16'],
      ['pg_expr_spawn_bottom_y', 'spawn bottom y', [], '144'],
      ['pg_expr_random_side_x', 'random side x', [], '(Math.random() < 0.5 ? -16 : 144)'],
      ['pg_expr_random_side_y', 'random side y', [], '(Math.random() < 0.5 ? -16 : 144)'],
      ['pg_expr_color_cycle', 'color cycle speed %1', [['A', 6]], 'Math.floor(t / A) % 16'],
      ['pg_expr_anim_frame', 'anim frame count %1 speed %2', [['A', 4], ['B', 8]], 'Math.floor(t / B) % A'],
      ['pg_expr_invuln_visible', 'visible with invuln %1', [['A', 'invuln']], '(A <= 0 || Math.floor(t / 4) % 2 === 0)'],
      ['pg_expr_combo_bonus', 'combo %1 bonus', [['A', 'combo']], 'Math.max(1, A) * 10'],
    ],
  },
  {
    category: 'Motion Values',
    colour: 45,
    blocks: [
      ['pg_expr_random_range', 'random float %1 to %2', [['A', 0], ['B', 1]], 'A + Math.random() * (B - A)'],
      ['pg_expr_random_sign', 'random sign', [], '(Math.random() < 0.5 ? -1 : 1)'],
      ['pg_expr_ease_in', 'ease in %1', [['A', 0.5]], 'A * A'],
      ['pg_expr_ease_out', 'ease out %1', [['A', 0.5]], '1 - (1 - A) * (1 - A)'],
      ['pg_expr_smoothstep', 'smoothstep %1', [['A', 0.5]], 'A * A * (3 - 2 * A)'],
      ['pg_expr_inverse_lerp', 'inverse lerp %1 from %2 to %3', [['A', 'x'], ['B', 0], ['C', 127]], '(A - B) / (C - B)'],
      ['pg_expr_map_range', 'map %1 %2-%3 to %4-%5', [['A', 'x'], ['B', 0], ['C', 127], ['D', 0], ['E', 1]], 'D + (A - B) * (E - D) / (C - B)'],
      ['pg_expr_pingpong', 'pingpong %1 length %2', [['A', 't'], ['B', 60]], 'B - Math.abs((A % (B * 2)) - B)'],
      ['pg_expr_pulse01', 'pulse 0..1 speed %1', [['A', 4]], '(Math.sin(time() * A) + 1) / 2'],
      ['pg_expr_shake_x', 'shake x amount %1', [['A', 'shake']], '(Math.random() * 2 - 1) * A'],
    ],
  }
);

extraStatementBlockGroups.push(
  {
    category: 'Drawing Helpers 2',
    colour: 160,
    blocks: [
      ['pg_draw_panel', 'panel x %1 y %2 w %3 h %4', [['X', 8], ['Y', 8], ['W', 80], ['H', 32]], v => `RECTFILL ${v.X}, ${v.Y}, ${v.X} + ${v.W}, ${v.Y} + ${v.H}, 0\nRECTFILL ${v.X} + 1, ${v.Y} + 1, ${v.X} + ${v.W} - 1, ${v.Y} + ${v.H} - 1, 1\nRECTFILL ${v.X}, ${v.Y}, ${v.X} + ${v.W}, ${v.Y}, 7`],
      ['pg_draw_button_label', 'button label %1 x %2 y %3', [['TEXT', '"OK"'], ['X', 48], ['Y', 100]], v => `RECTFILL ${v.X}, ${v.Y}, ${v.X} + 28, ${v.Y} + 10, 5\nJS print(${v.TEXT}, ${v.X} + 5, ${v.Y} + 2, 7)`],
      ['pg_draw_title_bar', 'title bar %1', [['TEXT', '"GAME"']], v => `RECTFILL 0, 0, 127, 9, 0\nJS print(${v.TEXT}, 3, 2, 10)`],
      ['pg_draw_pause_overlay', 'pause overlay', [], () => `RECTFILL 20, 44, 107, 78, 0\nRECTFILL 22, 46, 105, 76, 1\nJS print("PAUSED", 51, 57, 7)`],
      ['pg_draw_game_over', 'game over score %1', [['SCORE', 'score']], v => `RECTFILL 15, 38, 112, 86, 0\nRECTFILL 17, 40, 110, 84, 2\nJS print("GAME OVER", 45, 50, 8); print("SCORE " + ${v.SCORE}, 42, 64, 7)`],
      ['pg_draw_win_overlay', 'win overlay score %1', [['SCORE', 'score']], v => `RECTFILL 15, 38, 112, 86, 0\nRECTFILL 17, 40, 110, 84, 3\nJS print("YOU WIN", 50, 50, 11); print("SCORE " + ${v.SCORE}, 42, 64, 7)`],
      ['pg_draw_minimap_dot', 'minimap dot x %1 y %2 color %3', [['X', 'x'], ['Y', 'y'], ['COLOR', 10]], v => `PSET 112 + Math.floor(${v.X} / 8), 8 + Math.floor(${v.Y} / 8), ${v.COLOR}`],
      ['pg_draw_scanlines', 'scanlines color %1', [['COLOR', 0]], v => `JS for (let yy = 0; yy < 128; yy += 2) rectfill(0, yy, 127, yy, ${v.COLOR})`],
      ['pg_draw_rain', 'rain count %1 color %2', [['COUNT', 24], ['COLOR', 12]], v => `JS for (let i = 0; i < ${v.COUNT}; i++) { const rx = (i * 17 + t * 2) & 127; const ry = (i * 29 + t * 5) & 127; rectfill(rx, ry, rx, ry + 3, ${v.COLOR}); }`],
      ['pg_draw_snow', 'snow count %1 color %2', [['COUNT', 24], ['COLOR', 7]], v => `JS for (let i = 0; i < ${v.COUNT}; i++) pset((i * 23 + Math.floor(t / 2)) & 127, (i * 31 + t) & 127, ${v.COLOR})`],
      ['pg_draw_speed_lines', 'speed lines color %1', [['COLOR', 6]], v => `JS for (let i = 0; i < 10; i++) rectfill((i * 19 - t * 3) & 127, i * 12 + 4, ((i * 19 - t * 3) & 127) + 10, i * 12 + 4, ${v.COLOR})`],
      ['pg_draw_boss_bar', 'boss hp %1 max %2', [['HP', 'bossHp'], ['MAX', 100]], v => `RECTFILL 20, 116, 108, 122, 0\nRECTFILL 22, 118, 22 + (84 * ${v.HP} / ${v.MAX}), 120, 8`],
      ['pg_draw_dialog_box', 'dialog %1', [['TEXT', '"HELLO!"']], v => `RECTFILL 4, 92, 123, 124, 0\nRECTFILL 6, 94, 121, 122, 1\nJS print(${v.TEXT}, 10, 101, 7)`],
      ['pg_draw_reticle_box', 'target box x %1 y %2', [['X', 'x'], ['Y', 'y']], v => `RECTFILL ${v.X} - 8, ${v.Y} - 8, ${v.X} + 8, ${v.Y} - 7, 8\nRECTFILL ${v.X} - 8, ${v.Y} + 8, ${v.X} + 8, ${v.Y} + 9, 8\nRECTFILL ${v.X} - 8, ${v.Y} - 8, ${v.X} - 7, ${v.Y} + 8, 8\nRECTFILL ${v.X} + 8, ${v.Y} - 8, ${v.X} + 9, ${v.Y} + 8, 8`],
      ['pg_draw_toast', 'toast %1 timer %2', [['TEXT', '"READY"'], ['TIMER', 'toast']], v => `IF ${v.TIMER} > 0 THEN\n  RECTFILL 30, 10, 98, 22, 0\n  JS print(${v.TEXT}, 34, 13, 7)\nEND IF`],
    ],
  },
  {
    category: 'Game Helpers 2',
    colour: 75,
    blocks: [
      ['pg_game_flappy_physics', 'flappy y %1 dy %2 gravity %3 flap %4', [['Y', 'y'], ['DY', 'dy'], ['G', 0.28], ['FLAP', -4]], v => `IF BTN(4) THEN\n  ${v.DY} = ${v.FLAP}\nEND IF\n${v.DY} = ${v.DY} + ${v.G}\n${v.Y} = ${v.Y} + ${v.DY}`],
      ['pg_game_pipe_scroll', 'pipe x %1 speed %2 reset at %3', [['X', 'pipeX'], ['SPEED', 1.5], ['RESET', 144]], v => `${v.X} = ${v.X} - ${v.SPEED}\nIF ${v.X} < -20 THEN\n  ${v.X} = ${v.RESET}\nEND IF`],
      ['pg_game_asteroid_wrap', 'asteroid x %1 y %2', [['X', 'x'], ['Y', 'y']], v => `${v.X} = (((${v.X}) % 144) + 144) % 144 - 8\n${v.Y} = (((${v.Y}) % 144) + 144) % 144 - 8`],
      ['pg_game_topdown_accel', 'topdown accel dx %1 dy %2 amount %3', [['DX', 'dx'], ['DY', 'dy'], ['A', 0.2]], v => `IF BTN(0) THEN\n  ${v.DX} = ${v.DX} - ${v.A}\nEND IF\nIF BTN(1) THEN\n  ${v.DX} = ${v.DX} + ${v.A}\nEND IF\nIF BTN(2) THEN\n  ${v.DY} = ${v.DY} - ${v.A}\nEND IF\nIF BTN(3) THEN\n  ${v.DY} = ${v.DY} + ${v.A}\nEND IF`],
      ['pg_game_cap_speed', 'cap velocity %1 %2 max %3', [['DX', 'dx'], ['DY', 'dy'], ['MAX', 3]], v => `JS { const m = Math.hypot(${v.DX}, ${v.DY}); if (m > ${v.MAX}) { ${v.DX} = ${v.DX} / m * ${v.MAX}; ${v.DY} = ${v.DY} / m * ${v.MAX}; } }`],
      ['pg_game_enemy_wander', 'wander x %1 y %2 speed %3', [['X', 'x'], ['Y', 'y'], ['SPEED', 1]], v => `IF t % 30 = 0 THEN\n  dx = (Math.random() * 2 - 1) * ${v.SPEED}\n  dy = (Math.random() * 2 - 1) * ${v.SPEED}\nEND IF\n${v.X} = ${v.X} + dx\n${v.Y} = ${v.Y} + dy`],
      ['pg_game_knockback', 'knockback dx %1 dy %2 from hit %3', [['DX', 'dx'], ['DY', 'dy'], ['HIT', 'hit']], v => `IF ${v.HIT} THEN\n  ${v.DX} = -${v.DX} * 2\n  ${v.DY} = -2\nEND IF`],
      ['pg_game_damage_if_touch', 'damage hp %1 if touching %2', [['HP', 'hp'], ['HIT', 'hit']], v => `IF ${v.HIT} THEN\n  ${v.HP} = ${v.HP} - 1\nEND IF`],
      ['pg_game_respawn_coin', 'respawn coin %1 %2', [['X', 'coinX'], ['Y', 'coinY']], v => `${v.X} = 8 + Math.random() * 112\n${v.Y} = 8 + Math.random() * 96`],
      ['pg_game_screen_bounce_xy', 'bounce xy %1 %2 dx %3 dy %4', [['X', 'x'], ['Y', 'y'], ['DX', 'dx'], ['DY', 'dy']], v => `${v.X} = ${v.X} + ${v.DX}\n${v.Y} = ${v.Y} + ${v.DY}\nIF ${v.X} < 0 OR ${v.X} > 112 THEN\n  ${v.DX} = -${v.DX}\nEND IF\nIF ${v.Y} < 0 OR ${v.Y} > 112 THEN\n  ${v.DY} = -${v.DY}\nEND IF`],
      ['pg_game_checkpoint', 'checkpoint save %1 %2 from %3 %4', [['SX', 'spawnX'], ['SY', 'spawnY'], ['X', 'x'], ['Y', 'y']], v => `${v.SX} = ${v.X}\n${v.SY} = ${v.Y}`],
      ['pg_game_apply_checkpoint', 'checkpoint load %1 %2 to %3 %4', [['SX', 'spawnX'], ['SY', 'spawnY'], ['X', 'x'], ['Y', 'y']], v => `${v.X} = ${v.SX}\n${v.Y} = ${v.SY}`],
      ['pg_game_combo_timeout', 'combo %1 timer %2', [['COMBO', 'combo'], ['TIMER', 'comboTimer']], v => `IF ${v.TIMER} > 0 THEN\n  ${v.TIMER} = ${v.TIMER} - 1\nEND IF\nIF ${v.TIMER} = 0 THEN\n  ${v.COMBO} = 0\nEND IF`],
      ['pg_game_camera_shake_hit', 'shake %1 when hit %2 amount %3', [['SHAKE', 'shake'], ['HIT', 'hit'], ['AMOUNT', 8]], v => `IF ${v.HIT} THEN\n  ${v.SHAKE} = ${v.AMOUNT}\nEND IF\n${v.SHAKE} = Math.max(0, ${v.SHAKE} - 1)`],
      ['pg_game_round_timer_end', 'end flag %1 timer %2', [['FLAG', 'done'], ['TIMER', 'timer']], v => `IF ${v.TIMER} <= 0 THEN\n  ${v.FLAG} = 1\nEND IF`],
    ],
  },
  {
    category: 'Sound Helpers 2',
    colour: 300,
    blocks: [
      ['pg_sound_menu_move', 'menu move sfx', [], () => 'BEEP 520, 0.03'],
      ['pg_sound_menu_select', 'menu select sfx', [], () => 'BEEP 740, 0.05'],
      ['pg_sound_error', 'error sfx', [], () => 'BEEP 90, 0.18'],
      ['pg_sound_enemy_pop', 'enemy pop sfx', [], () => 'BEEP 330, 0.04\nBEEP 220, 0.04'],
      ['pg_sound_checkpoint', 'checkpoint sfx', [], () => 'BEEP 523, 0.04\nBEEP 659, 0.04\nBEEP 784, 0.06'],
      ['pg_sound_countdown_beep', 'countdown beep timer %1', [['TIMER', 'timer']], v => `IF ${v.TIMER} <= 90 AND ${v.TIMER} % 30 = 0 THEN\n  BEEP 660, 0.04\nEND IF`],
      ['pg_sound_low_health', 'low health beep hp %1', [['HP', 'hp']], v => `IF ${v.HP} <= 2 AND t % 45 = 0 THEN\n  BEEP 180, 0.05\nEND IF`],
      ['pg_sound_engine_loop', 'engine tick speed %1', [['SPEED', 'speed']], v => `IF t % 8 = 0 THEN\n  BEEP 80 + ${v.SPEED} * 20, 0.02\nEND IF`],
      ['pg_sound_random_blip', 'random blip chance %1', [['CHANCE', 80]], v => `IF Math.random() < 1 / ${v.CHANCE} THEN\n  BEEP 300 + Math.random() * 500, 0.03\nEND IF`],
      ['pg_sound_victory_fanfare', 'victory fanfare', [], () => 'BEEP 523, 0.06\nBEEP 659, 0.06\nBEEP 784, 0.06\nBEEP 1046, 0.12'],
    ],
  },
  {
    category: 'Flow Shortcuts 2',
    colour: 120,
    blocks: [
      ['pg_flow_when_start_pressed', 'when action pressed %1', [], v => `IF BTN(4) THEN\n${statementLines(v.block, 'BODY').join('\n')}\nEND IF`, 'BODY'],
      ['pg_flow_if_alive', 'if hp %1 alive %2', [['HP', 'hp']], v => `IF ${v.HP} > 0 THEN\n${statementLines(v.block, 'BODY').join('\n')}\nEND IF`, 'BODY'],
      ['pg_flow_if_dead', 'if hp %1 dead %2', [['HP', 'hp']], v => `IF ${v.HP} <= 0 THEN\n${statementLines(v.block, 'BODY').join('\n')}\nEND IF`, 'BODY'],
      ['pg_flow_once_flag', 'once flag %1 %2', [['FLAG', 'didThing']], v => `IF NOT ${v.FLAG} THEN\n${statementLines(v.block, 'BODY').join('\n')}\n  ${v.FLAG} = 1\nEND IF`, 'BODY'],
      ['pg_flow_when_timer_done', 'when timer %1 done %2', [['TIMER', 'timer']], v => `IF ${v.TIMER} <= 0 THEN\n${statementLines(v.block, 'BODY').join('\n')}\nEND IF`, 'BODY'],
      ['pg_flow_when_chance', 'chance 1 in %1 %2', [['CHANCE', 60]], v => `IF Math.random() < 1 / ${v.CHANCE} THEN\n${statementLines(v.block, 'BODY').join('\n')}\nEND IF`, 'BODY'],
      ['pg_flow_if_on_screen', 'if sprite x %1 y %2 on screen %3', [['X', 'x'], ['Y', 'y']], v => `IF ${v.X} > -16 AND ${v.X} < 128 AND ${v.Y} > -16 AND ${v.Y} < 128 THEN\n${statementLines(v.block, 'BODY').join('\n')}\nEND IF`, 'BODY'],
      ['pg_flow_if_off_screen', 'if sprite x %1 y %2 off screen %3', [['X', 'x'], ['Y', 'y']], v => `IF ${v.X} <= -16 OR ${v.X} >= 128 OR ${v.Y} <= -16 OR ${v.Y} >= 128 THEN\n${statementLines(v.block, 'BODY').join('\n')}\nEND IF`, 'BODY'],
      ['pg_flow_for_tiles_x', 'for tile x %1 count %2 %3', [['I', 'tileX'], ['COUNT', 8]], v => `FOR ${v.I} = 0 TO ${v.COUNT} - 1\n${statementLines(v.block, 'BODY').join('\n')}\nNEXT`, 'BODY'],
      ['pg_flow_state_equals', 'if state %1 equals %2 %3', [['STATE', 'state'], ['VALUE', 1]], v => `IF ${v.STATE} = ${v.VALUE} THEN\n${statementLines(v.block, 'BODY').join('\n')}\nEND IF`, 'BODY'],
    ],
  }
);

function fieldValue(block, name, fallback = '') {
  return block.getFieldValue(name) || fallback;
}

function blockArgValue(block, name, fallback) {
  return inputText(block, name, typeof fallback === 'string' ? fallback : String(fallback));
}

function buttonCondition(value) {
  const text = String(value || 0).trim();
  return /^BTN\s*\(/i.test(text) ? text : `BTN(${text})`;
}

function compileFormula(formula, values) {
  return formula.replace(/\b([A-H])\b/g, name => values[name] ?? name);
}

const extraValueBlocks = extraValueBlockGroups.flatMap(group => group.blocks.map(([type, message0, args, formula]) => ({ type, message0, args, formula, colour: group.colour, category: group.category })));
const statementBlockLimits = new Map([
  ['Drawing Helpers', 16],
  ['Game Helpers', 24],
  ['Sound Helpers', 7],
  ['Flow Shortcuts', 3],
]);
const statementBlockCounts = new Map();
const extraStatementBlocks = extraStatementBlockGroups.flatMap(group => group.blocks.map(([type, message0, args, generator, statementInput]) => ({ type, message0, args, generator, statementInput, colour: group.colour, category: group.category }))).filter(spec => {
  const count = statementBlockCounts.get(spec.category) || 0;
  const limit = statementBlockLimits.get(spec.category) || Infinity;
  if (count >= limit) return false;
  statementBlockCounts.set(spec.category, count + 1);
  return true;
});
const extraValueGenerators = Object.fromEntries(extraValueBlocks.map(spec => [spec.type, block => {
  const values = {};
  spec.args.forEach(([name, fallback]) => { values[name] = blockArgValue(block, name, fallback); });
  return compileFormula(spec.formula, values);
}]));
const extraStatementGenerators = Object.fromEntries(extraStatementBlocks.map(spec => [spec.type, block => {
  const values = { block };
  spec.args.forEach(([name, fallback]) => { values[name] = blockArgValue(block, name, fallback); });
  return spec.generator(values);
}]));

function loadScript(src) {
  return new Promise((resolve, reject) => {
    const existing = [...document.scripts].find(script => script.src === src);
    if (existing) {
      existing.addEventListener('load', resolve, { once: true });
      existing.addEventListener('error', reject, { once: true });
      if (window.Blockly) resolve();
      return;
    }
    const script = document.createElement('script');
    script.src = src;
    script.async = true;
    script.addEventListener('load', resolve, { once: true });
    script.addEventListener('error', () => reject(new Error(`Could not load ${src}`)), { once: true });
    document.head.appendChild(script);
  });
}

function inputText(block, name, fallback = '') {
  const target = block.getInputTargetBlock(name);
  return target ? valueBlockToBasic(target) : fallback;
}

function statementLines(block, name, depth = 1) {
  const first = block.getInputTargetBlock(name);
  const lines = [];
  for (let child = first; child; child = child.getNextBlock()) {
    const text = statementBlockToBasic(child);
    if (!text.trim()) continue;
    for (const line of text.split('\n')) lines.push(`${'  '.repeat(depth)}${line}`);
  }
  return lines;
}

function valueBlockToBasic(block) {
  if (!block) return '0';
  if (extraValueGenerators[block.type]) return extraValueGenerators[block.type](block);
  switch (block.type) {
    case 'pg_number': return String(Number(block.getFieldValue('VALUE') || 0));
    case 'pg_text': return JSON.stringify(block.getFieldValue('VALUE') || '');
    case 'pg_variable_value': return block.getFieldValue('NAME') || 'x';
    case 'pg_raw_expr': return block.getFieldValue('VALUE') || '0';
    case 'pg_threads': return 'THREADS()';
    case 'pg_btn': return `BTN(${block.getFieldValue('BUTTON') || 0})`;
    case 'pg_binary': return `${inputText(block, 'A', '0')} ${block.getFieldValue('OP') || '+'} ${inputText(block, 'B', '0')}`;
    case 'pg_compare': return `${inputText(block, 'A', '0')} ${block.getFieldValue('OP') || '='} ${inputText(block, 'B', '0')}`;
    default: return block.getFieldValue('VALUE') || '0';
  }
}

function statementBlockToBasic(block) {
  if (extraStatementGenerators[block.type]) return extraStatementGenerators[block.type](block);
  switch (block.type) {
    case 'pg_btn':
      return '';
    case 'pg_section':
      return [`${block.getFieldValue('NAME')}:`, ...statementLines(block, 'BODY')].join('\n');
    case 'pg_local_section':
      return [`LOCAL ${block.getFieldValue('NAME')}:`, ...statementLines(block, 'BODY')].join('\n');
    case 'pg_import':
      return `IMPORT ${JSON.stringify(block.getFieldValue('PATH') || 'lib/code.bas')}`;
    case 'pg_dim':
      return `DIM ${block.getFieldValue('NAME') || 'v'} = ${inputText(block, 'VALUE', '0')}`;
    case 'pg_set':
      return `${block.getFieldValue('NAME') || 'v'} = ${inputText(block, 'VALUE', '0')}`;
    case 'pg_print':
      return `PRINT ${inputText(block, 'TEXT', '""')}`;
    case 'pg_cls':
      return `CLS ${inputText(block, 'COLOR', '0')}`;
    case 'pg_pset':
      return `PSET ${inputText(block, 'X', '0')}, ${inputText(block, 'Y', '0')}, ${inputText(block, 'COLOR', '7')}`;
    case 'pg_rectfill':
      return `RECTFILL ${inputText(block, 'X0', '0')}, ${inputText(block, 'Y0', '0')}, ${inputText(block, 'X1', '127')}, ${inputText(block, 'Y1', '127')}, ${inputText(block, 'COLOR', '3')}`;
    case 'pg_spr':
      return `SPR ${inputText(block, 'SPRITE', '1')}, ${inputText(block, 'X', 'x')}, ${inputText(block, 'Y', 'y')}`;
    case 'pg_beep':
      return `BEEP ${inputText(block, 'FREQ', '440')}, ${inputText(block, 'DUR', '0.1')}`;
    case 'pg_if':
      return [`IF ${inputText(block, 'COND', '1')} THEN`, ...statementLines(block, 'BODY'), 'END IF'].join('\n');
    case 'pg_for':
      return [`FOR ${block.getFieldValue('NAME') || 'i'} = ${inputText(block, 'START', '0')} TO ${inputText(block, 'END', '10')}`, ...statementLines(block, 'BODY'), 'NEXT'].join('\n');
    case 'pg_js':
      return `JS ${block.getFieldValue('CODE') || 'trace("js")'}`;
    case 'pg_raw_line':
      return block.getFieldValue('CODE') || "'";
    case 'pg_bounce_x': {
      const x = block.getFieldValue('X') || 'x';
      const dx = block.getFieldValue('DX') || 'dx';
      const min = inputText(block, 'MIN', '0');
      const max = inputText(block, 'MAX', '112');
      return `${x} = ${x} + ${dx}\nIF ${x} > ${max} THEN\n  ${dx} = -1\nEND IF\nIF ${x} < ${min} THEN\n  ${dx} = 1\nEND IF`;
    }
    case 'pg_player_arrows': {
      const x = block.getFieldValue('X') || 'x';
      const y = block.getFieldValue('Y') || 'y';
      const s = inputText(block, 'SPEED', '1');
      return `IF BTN(0) THEN\n  ${x} = ${x} - ${s}\nEND IF\nIF BTN(1) THEN\n  ${x} = ${x} + ${s}\nEND IF\nIF BTN(2) THEN\n  ${y} = ${y} - ${s}\nEND IF\nIF BTN(3) THEN\n  ${y} = ${y} + ${s}\nEND IF`;
    }
    case 'pg_clamp': {
      const v = block.getFieldValue('NAME') || 'x';
      const min = inputText(block, 'MIN', '0');
      const max = inputText(block, 'MAX', '112');
      return `IF ${v} < ${min} THEN\n  ${v} = ${min}\nEND IF\nIF ${v} > ${max} THEN\n  ${v} = ${max}\nEND IF`;
    }
    case 'pg_screen_setup':
      return `CLS ${inputText(block, 'BG', '1')}\nRECTFILL 0, ${inputText(block, 'FLOOR', '108')}, 127, 127, ${inputText(block, 'GROUND', '3')}`;
    default:
      return `' unsupported block ${block.type}`;
  }
}

function workspaceToPgBasic() {
  if (!blocklyWorkspace) return '';
  return blocklyWorkspace.getTopBlocks(true).map(block => {
    const chunks = [];
    for (let current = block; current; current = current.getNextBlock()) chunks.push(statementBlockToBasic(current));
    return chunks.join('\n');
  }).filter(Boolean).join('\n\n') + '\n';
}

function updateBlocklyOutput() {
  $('#blockly-output').textContent = blocklyWorkspace ? workspaceToPgBasic() : 'Activate Blockly to build PG BASIC visually.';
}

function definePgBasicBlocks() {
  if (blocklyBlocksDefined) return;
  blocklyBlocksDefined = true;
  const extraBlockDefs = [
    ...extraValueBlocks.map(spec => ({
      type: spec.type,
      message0: spec.message0,
      args0: spec.args.map(([name]) => ({ type: 'input_value', name })),
      output: null,
      colour: spec.colour,
    })),
    ...extraStatementBlocks.map(spec => ({
      type: spec.type,
      message0: spec.message0,
      args0: [
        ...spec.args.map(([name]) => ({ type: 'input_value', name })),
        ...(spec.statementInput ? [{ type: 'input_statement', name: spec.statementInput }] : []),
      ],
      previousStatement: null,
      nextStatement: null,
      colour: spec.colour,
    })),
  ];
  Blockly.defineBlocksWithJsonArray([
    { type: 'pg_section', message0: 'section %1 %2', args0: [{ type: 'field_dropdown', name: 'NAME', options: [['INIT', 'INIT'], ['UPDATE', 'UPDATE'], ['DRAW', 'DRAW']] }, { type: 'input_statement', name: 'BODY' }], previousStatement: null, nextStatement: null, colour: 210 },
    { type: 'pg_local_section', message0: 'object section %1 %2', args0: [{ type: 'field_dropdown', name: 'NAME', options: [['LOCAL INIT', 'INIT'], ['LOCAL UPDATE', 'UPDATE'], ['LOCAL DRAW', 'DRAW']] }, { type: 'input_statement', name: 'BODY' }], previousStatement: null, nextStatement: null, colour: 215 },
    { type: 'pg_import', message0: 'import file %1', args0: [{ type: 'field_input', name: 'PATH', text: 'lib/movement.bas' }], previousStatement: null, nextStatement: null, colour: 260 },
    { type: 'pg_dim', message0: 'dim %1 = %2', args0: [{ type: 'field_input', name: 'NAME', text: 'x' }, { type: 'input_value', name: 'VALUE' }], previousStatement: null, nextStatement: null, colour: 330 },
    { type: 'pg_set', message0: 'set %1 = %2', args0: [{ type: 'field_input', name: 'NAME', text: 'x' }, { type: 'input_value', name: 'VALUE' }], previousStatement: null, nextStatement: null, colour: 330 },
    { type: 'pg_number', message0: 'number %1', args0: [{ type: 'field_number', name: 'VALUE', value: 0 }], output: null, colour: 45 },
    { type: 'pg_text', message0: 'text %1', args0: [{ type: 'field_input', name: 'VALUE', text: 'HELLO' }], output: null, colour: 45 },
    { type: 'pg_variable_value', message0: 'value %1', args0: [{ type: 'field_input', name: 'NAME', text: 'x' }], output: null, colour: 330 },
    { type: 'pg_raw_expr', message0: 'expression %1', args0: [{ type: 'field_input', name: 'VALUE', text: 'time()' }], output: null, colour: 20 },
    { type: 'pg_binary', message0: '%1 %2 %3', args0: [{ type: 'input_value', name: 'A' }, { type: 'field_dropdown', name: 'OP', options: [['+', '+'], ['-', '-'], ['*', '*'], ['/', '/'], ['AND', 'AND'], ['OR', 'OR']] }, { type: 'input_value', name: 'B' }], output: null, colour: 45 },
    { type: 'pg_compare', message0: '%1 %2 %3', args0: [{ type: 'input_value', name: 'A' }, { type: 'field_dropdown', name: 'OP', options: [['=', '='], ['<>', '<>'], ['<', '<'], ['>', '>'], ['<=', '<='], ['>=', '>=']] }, { type: 'input_value', name: 'B' }], output: null, colour: 120 },
    { type: 'pg_if', message0: 'if %1 then %2', args0: [{ type: 'input_value', name: 'COND' }, { type: 'input_statement', name: 'BODY' }], previousStatement: null, nextStatement: null, colour: 120 },
    { type: 'pg_for', message0: 'for %1 from %2 to %3 %4', args0: [{ type: 'field_input', name: 'NAME', text: 'i' }, { type: 'input_value', name: 'START' }, { type: 'input_value', name: 'END' }, { type: 'input_statement', name: 'BODY' }], previousStatement: null, nextStatement: null, colour: 120 },
    { type: 'pg_cls', message0: 'clear color %1', args0: [{ type: 'input_value', name: 'COLOR' }], previousStatement: null, nextStatement: null, colour: 160 },
    { type: 'pg_print', message0: 'print %1', args0: [{ type: 'input_value', name: 'TEXT' }], previousStatement: null, nextStatement: null, colour: 160 },
    { type: 'pg_pset', message0: 'pixel x %1 y %2 color %3', args0: [{ type: 'input_value', name: 'X' }, { type: 'input_value', name: 'Y' }, { type: 'input_value', name: 'COLOR' }], previousStatement: null, nextStatement: null, colour: 160 },
    { type: 'pg_rectfill', message0: 'filled rect x0 %1 y0 %2 x1 %3 y1 %4 color %5', args0: [{ type: 'input_value', name: 'X0' }, { type: 'input_value', name: 'Y0' }, { type: 'input_value', name: 'X1' }, { type: 'input_value', name: 'Y1' }, { type: 'input_value', name: 'COLOR' }], previousStatement: null, nextStatement: null, colour: 160 },
    { type: 'pg_spr', message0: 'sprite %1 at x %2 y %3', args0: [{ type: 'input_value', name: 'SPRITE' }, { type: 'input_value', name: 'X' }, { type: 'input_value', name: 'Y' }], previousStatement: null, nextStatement: null, colour: 200 },
    { type: 'pg_beep', message0: 'beep freq %1 duration %2', args0: [{ type: 'input_value', name: 'FREQ' }, { type: 'input_value', name: 'DUR' }], previousStatement: null, nextStatement: null, colour: 300 },
    { type: 'pg_btn', message0: 'button %1', args0: [{ type: 'field_dropdown', name: 'BUTTON', options: [['left', '0'], ['right', '1'], ['up', '2'], ['down', '3'], ['jump/action', '4']] }], output: null, colour: 30 },
    { type: 'pg_threads', message0: 'thread count', output: null, colour: 30 },
    { type: 'pg_bounce_x', message0: 'bounce %1 by %2 between %3 and %4', args0: [{ type: 'field_input', name: 'X', text: 'x' }, { type: 'field_input', name: 'DX', text: 'dx' }, { type: 'input_value', name: 'MIN' }, { type: 'input_value', name: 'MAX' }], previousStatement: null, nextStatement: null, colour: 75 },
    { type: 'pg_player_arrows', message0: 'arrow move x %1 y %2 speed %3', args0: [{ type: 'field_input', name: 'X', text: 'x' }, { type: 'field_input', name: 'Y', text: 'y' }, { type: 'input_value', name: 'SPEED' }], previousStatement: null, nextStatement: null, colour: 75 },
    { type: 'pg_clamp', message0: 'clamp %1 between %2 and %3', args0: [{ type: 'field_input', name: 'NAME', text: 'x' }, { type: 'input_value', name: 'MIN' }, { type: 'input_value', name: 'MAX' }], previousStatement: null, nextStatement: null, colour: 75 },
    { type: 'pg_screen_setup', message0: 'screen bg %1 floor y %2 ground %3', args0: [{ type: 'input_value', name: 'BG' }, { type: 'input_value', name: 'FLOOR' }, { type: 'input_value', name: 'GROUND' }], previousStatement: null, nextStatement: null, colour: 75 },
    { type: 'pg_js', message0: 'raw JS line %1', args0: [{ type: 'field_input', name: 'CODE', text: 'trace("debug");' }], previousStatement: null, nextStatement: null, colour: 20 },
    { type: 'pg_raw_line', message0: 'raw PG BASIC %1', args0: [{ type: 'field_input', name: 'CODE', text: 'REM raw line' }], previousStatement: null, nextStatement: null, colour: 20 },
    ...extraBlockDefs,
  ]);
}

function blockXml(type, values = '') {
  return `<block type="${type}">${values}</block>`;
}

function shadowNumber(name, value) {
  return `<value name="${name}"><shadow type="pg_number"><field name="VALUE">${value}</field></shadow></value>`;
}

function shadowText(name, value) {
  return `<value name="${name}"><shadow type="pg_text"><field name="VALUE">${value}</field></shadow></value>`;
}

function shadowExpr(name, value) {
  const escaped = String(value).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
  return `<value name="${name}"><shadow type="pg_raw_expr"><field name="VALUE">${escaped}</field></shadow></value>`;
}

function defaultShadow(name, value) {
  return typeof value === 'number' ? shadowNumber(name, value) : shadowExpr(name, value);
}

function blockXmlForSpec(spec) {
  return blockXml(spec.type, spec.args.map(([name, value]) => defaultShadow(name, value)).join(''));
}

function categoryXml(name, colour, blocks) {
  return `<category name="${name}" colour="${colour}">
      ${blocks.map(blockXmlForSpec).join('\n      ')}
    </category>`;
}

function makeBlocklyToolbox() {
  return `<xml>
    <category name="Flow" colour="120">
      ${blockXml('pg_section')}
      ${blockXml('pg_local_section')}
      ${blockXml('pg_if')}
      ${blockXml('pg_for')}
    </category>
    <category name="Variables" colour="330">
      ${blockXml('pg_dim', shadowNumber('VALUE', 0))}
      ${blockXml('pg_set', shadowNumber('VALUE', 0))}
      ${blockXml('pg_variable_value')}
      ${blockXml('pg_number')}
      ${blockXml('pg_text')}
      ${blockXml('pg_binary', `${shadowNumber('A', 0)}${shadowNumber('B', 1)}`)}
      ${blockXml('pg_compare', `${shadowNumber('A', 0)}${shadowNumber('B', 1)}`)}
    </category>
    <category name="Drawing" colour="160">
      ${blockXml('pg_cls', shadowNumber('COLOR', 0))}
      ${blockXml('pg_print', shadowText('TEXT', 'HELLO'))}
      ${blockXml('pg_pset', `${shadowNumber('X', 0)}${shadowNumber('Y', 0)}${shadowNumber('COLOR', 7)}`)}
      ${blockXml('pg_rectfill', `${shadowNumber('X0', 0)}${shadowNumber('Y0', 0)}${shadowNumber('X1', 127)}${shadowNumber('Y1', 127)}${shadowNumber('COLOR', 3)}`)}
    </category>
    <category name="Sprites And Scene" colour="200">
      ${blockXml('pg_spr', `${shadowNumber('SPRITE', 1)}${shadowNumber('X', 48)}${shadowNumber('Y', 48)}`)}
    </category>
    <category name="Sound" colour="300">
      ${blockXml('pg_beep', `${shadowNumber('FREQ', 440)}${shadowNumber('DUR', 0.1)}`)}
    </category>
    <category name="Input And Runtime" colour="30">
      ${blockXml('pg_btn')}
      ${blockXml('pg_threads')}
      ${blockXml('pg_raw_expr')}
    </category>
    <category name="Files And Imports" colour="260">
      ${blockXml('pg_import')}
    </category>
    <category name="Helpers" colour="75">
      ${blockXml('pg_bounce_x', `${shadowNumber('MIN', 16)}${shadowNumber('MAX', 112)}`)}
      ${blockXml('pg_player_arrows', shadowNumber('SPEED', 1))}
      ${blockXml('pg_clamp', `${shadowNumber('MIN', 0)}${shadowNumber('MAX', 112)}`)}
      ${blockXml('pg_screen_setup', `${shadowNumber('BG', 1)}${shadowNumber('FLOOR', 108)}${shadowNumber('GROUND', 3)}`)}
    </category>
    ${extraValueBlockGroups.map(group => categoryXml(group.category, group.colour, extraValueBlocks.filter(block => block.category === group.category))).join('\n    ')}
    ${extraStatementBlockGroups.map(group => categoryXml(group.category, group.colour, extraStatementBlocks.filter(block => block.category === group.category))).join('\n    ')}
    <category name="Raw" colour="20">
      ${blockXml('pg_raw_line')}
      ${blockXml('pg_js')}
    </category>
  </xml>`;
}

function seedBlocklyWorkspace() {
  const xml = Blockly.utils.xml.textToDom(`<xml>
    <block type="pg_section" x="20" y="20">
      <field name="NAME">INIT</field>
      <statement name="BODY">
        <block type="pg_dim">
          <field name="NAME">x</field>
          <value name="VALUE"><shadow type="pg_number"><field name="VALUE">48</field></shadow></value>
          <next><block type="pg_dim">
            <field name="NAME">y</field>
            <value name="VALUE"><shadow type="pg_number"><field name="VALUE">48</field></shadow></value>
            <next><block type="pg_dim">
              <field name="NAME">dx</field>
              <value name="VALUE"><shadow type="pg_number"><field name="VALUE">1</field></shadow></value>
            </block></next>
          </block></next>
        </block>
      </statement>
      <next><block type="pg_section">
        <field name="NAME">UPDATE</field>
        <statement name="BODY">
          <block type="pg_bounce_x">
            <field name="X">x</field>
            <field name="DX">dx</field>
            <value name="MIN"><shadow type="pg_number"><field name="VALUE">16</field></shadow></value>
            <value name="MAX"><shadow type="pg_number"><field name="VALUE">96</field></shadow></value>
          </block>
        </statement>
        <next><block type="pg_section">
          <field name="NAME">DRAW</field>
          <statement name="BODY">
            <block type="pg_screen_setup">
              <value name="BG"><shadow type="pg_number"><field name="VALUE">1</field></shadow></value>
              <value name="FLOOR"><shadow type="pg_number"><field name="VALUE">108</field></shadow></value>
              <value name="GROUND"><shadow type="pg_number"><field name="VALUE">3</field></shadow></value>
              <next><block type="pg_spr">
                <value name="SPRITE"><shadow type="pg_number"><field name="VALUE">1</field></shadow></value>
                <value name="X"><shadow type="pg_variable_value"><field name="NAME">x</field></shadow></value>
                <value name="Y"><shadow type="pg_variable_value"><field name="NAME">y</field></shadow></value>
              </block></next>
            </block>
          </statement>
        </block></next>
      </block></next>
    </block>
  </xml>`);
  Blockly.Xml.domToWorkspace(xml, blocklyWorkspace);
}

async function activateBlockly() {
  if (!blocklyLoading) {
    blocklyLoading = loadScript('https://cdn.jsdelivr.net/npm/blockly/blockly.min.js');
  }
  await blocklyLoading;
  definePgBasicBlocks();
  if (!blocklyWorkspace) {
    blocklyWorkspace = Blockly.inject('blockly-area', {
      toolbox: makeBlocklyToolbox(),
      trashcan: true,
      scrollbars: true,
      renderer: 'zelos',
    });
    seedBlocklyWorkspace();
    blocklyWorkspace.addChangeListener(updateBlocklyOutput);
  }
  Blockly.svgResize(blocklyWorkspace);
  updateBlocklyOutput();
  log('Blockly PG BASIC plugin active');
}

function insertBlocklyBasic() {
  const text = workspaceToPgBasic();
  if (!text.trim()) return;
  if ($('#block-target').value === 'object') {
    const obj = currentObject();
    if (!obj) {
      log('No scene object selected for block insert');
      return;
    }
    $('#object-code').value = `${$('#object-code').value.trimEnd()}\n\n${text}`.trimStart();
    updateSelectedObject();
    log(`inserted block PG BASIC into ${obj.name}`);
    return;
  }
  saveCurrentBas();
  $('#basic').value = `${$('#basic').value.trimEnd()}\n\n${text}`.trimStart();
  basFiles.set(currentBasPath, $('#basic').value);
  log(`inserted block PG BASIC into ${currentBasPath}`);
}

function initBlocklyPlugin() {
  updateBlocklyOutput();
  $('#activate-blockly').addEventListener('click', () => {
    activateBlockly().catch(err => log(`Blockly plugin failed: ${err.message}`));
  });
  $('#insert-blocks').addEventListener('click', () => {
    if (!blocklyWorkspace) {
      log('Activate Blockly before inserting blocks');
      return;
    }
    insertBlocklyBasic();
  });
}

function seedBasic() {
  basFiles.clear();
  basFiles.set('main.bas', `IMPORT "lib/movement.bas"

INIT:
DIM x = 48
DIM y = 48
DIM dx = 1
BEEP 440, 0.08

UPDATE:
x = x + dx
IF x > 96 THEN
  dx = -1
END IF
IF x < 16 THEN
  dx = 1
END IF

DRAW:
CLS 1
RECTFILL 0, 108, 127, 127, 3
SPR 1, x, y
PRINT "PG BASIC CART"`);
  basFiles.set('lib/movement.bas', `' imported by main.bas
REM Keep helper variables and movement routines here.
`);
  selectBasFile('main.bas');
}

function initTabs() {
  document.querySelectorAll('.tab').forEach(button => {
    button.addEventListener('click', () => {
      document.querySelectorAll('.tab').forEach(tab => tab.classList.remove('active'));
      document.querySelectorAll('.tool').forEach(tool => tool.classList.remove('active'));
      button.classList.add('active');
      $(`#tool-${button.dataset.tab}`).classList.add('active');
      if (button.dataset.tab === 'scene') renderSceneEditor();
      if (button.dataset.tab === 'blocks' && blocklyWorkspace) Blockly.svgResize(blocklyWorkspace);
    });
  });
}

function initSceneEditor() {
  $('#add-object').addEventListener('click', () => addObject());
  $('#delete-object').addEventListener('click', deleteObject);
  sceneCanvas.addEventListener('pointerdown', handleScenePointer);
  sceneCanvas.addEventListener('pointermove', event => { if (event.buttons) handleScenePointer(event); });
  ['#object-name', '#object-x', '#object-y', '#object-sprite', '#object-code'].forEach(selector => {
    $(selector).addEventListener('input', updateSelectedObject);
  });
  addObject(64, 64);
}

function initBasFiles() {
  $('#new-bas').addEventListener('click', newBasFile);
  $('#delete-bas').addEventListener('click', deleteBasFile);
  $('#bas-path').addEventListener('change', renameCurrentBas);
  $('#basic').addEventListener('input', () => {
    basFiles.set(currentBasPath, $('#basic').value);
  });
}

function initInput() {
  window.addEventListener('keydown', event => keysDown.add(event.key.toLowerCase()));
  window.addEventListener('keyup', event => keysDown.delete(event.key.toLowerCase()));
  window.addEventListener('blur', () => keysDown.clear());
}

initTabs();
initInput();
initSprites();
initArt();
initSceneEditor();
seedBasic();
initBasFiles();
initBlocklyPlugin();
$('#compile').addEventListener('click', compileProject);
$('#run').addEventListener('click', runProject);
$('#export').addEventListener('click', exportImage);
$('#play-sound').addEventListener('click', () => beep());
compileProject();
})();
