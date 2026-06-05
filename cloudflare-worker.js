const CORS_HEADERS = {
  'Access-Control-Allow-Origin': '*',
  'Access-Control-Allow-Methods': 'GET,POST,OPTIONS',
  'Access-Control-Allow-Headers': 'Content-Type,api-key',
};

const COLLECTIONS = new Set(['images', 'comments']);

export default {
  async fetch(request, env) {
    if (request.method === 'OPTIONS') {
      return json({}, 204);
    }

    const url = new URL(request.url);
    const match = url.pathname.match(/^\/action\/(find|findOne|insertOne)$/);
    if (!match) {
      return json({ error: 'Use /action/find, /action/findOne, or /action/insertOne.' }, 404);
    }

    if (!env.GALLERY) {
      return json({ error: 'Missing KV binding named GALLERY.' }, 500);
    }

    let body;
    try {
      body = await request.json();
    } catch {
      return json({ error: 'Request body must be JSON.' }, 400);
    }

    const action = match[1];
    const collection = String(body.collection || '');
    if (!COLLECTIONS.has(collection)) {
      return json({ error: 'Unknown collection.' }, 400);
    }

    if (env.API_KEY && request.headers.get('api-key') !== env.API_KEY) {
      return json({ error: 'Bad API key.' }, 401);
    }

    const docs = await readCollection(env, collection);

    if (action === 'insertOne') {
      if (request.method !== 'POST') return json({ error: 'insertOne requires POST.' }, 405);
      const document = sanitizeDocument(body.document || {});
      document._id = crypto.randomUUID();
      document.createdAt = document.createdAt || new Date().toISOString();
      docs.push(document);
      await writeCollection(env, collection, docs);
      return json({ insertedId: document._id });
    }

    const filtered = docs.filter(doc => matchesFilter(doc, body.filter || {}));
    sortDocs(filtered, body.sort || {});

    if (action === 'findOne') {
      return json({ document: filtered[0] || null });
    }

    const limit = Math.max(0, Math.min(100, Number(body.limit || 50)));
    return json({ documents: filtered.slice(0, limit) });
  },
};

async function readCollection(env, name) {
  return (await env.GALLERY.get(name, { type: 'json' })) || [];
}

async function writeCollection(env, name, docs) {
  await env.GALLERY.put(name, JSON.stringify(docs));
}

function sanitizeDocument(value) {
  return JSON.parse(JSON.stringify(value));
}

function matchesFilter(doc, filter) {
  return Object.entries(filter).every(([key, value]) => doc[key] === value);
}

function sortDocs(docs, sort) {
  const entries = Object.entries(sort);
  if (!entries.length) return;
  docs.sort((a, b) => {
    for (const [key, dir] of entries) {
      const av = a[key] || '';
      const bv = b[key] || '';
      if (av < bv) return dir < 0 ? 1 : -1;
      if (av > bv) return dir < 0 ? -1 : 1;
    }
    return 0;
  });
}

function json(data, status = 200) {
  return new Response(JSON.stringify(data), {
    status,
    headers: {
      ...CORS_HEADERS,
      'Content-Type': 'application/json',
    },
  });
}
