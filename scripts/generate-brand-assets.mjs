import fs from "node:fs/promises";
import path from "node:path";
import sharp from "sharp";

const projectRoot = path.resolve(import.meta.dirname, "..");
const publicDir = path.join(projectRoot, "public");
const brandDir = path.join(publicDir, "brand");
const artDir = path.join(brandDir, "art");
const iconsDir = path.join(publicDir, "icons");
const masterPath = path.join(brandDir, "knitting-mascot.png");

const colors = {
  ink: "#2F1F12",
  orange: "#FF7A1F",
  white: "#FFF8E9",
  cream: "#EED9B7",
  peach: "#FCEAD5",
};

await Promise.all([
  fs.mkdir(brandDir, { recursive: true }),
  fs.mkdir(artDir, { recursive: true }),
  fs.mkdir(iconsDir, { recursive: true }),
]);

const chromaSource = process.argv.find((arg) => arg.startsWith("--chroma="))
  ?.slice("--chroma=".length);

if (chromaSource) {
  await extractChromaMaster(path.resolve(chromaSource), masterPath);
}

const artChromaSources = [
  ["--art-knitting=", "knitting-lamb.webp", 760],
  ["--art-laptop=", "laptop-lamb.webp", 900],
  ["--art-sleeping=", "sleeping-lamb.webp", 900],
];

for (const [argumentPrefix, filename, maxSize] of artChromaSources) {
  const source = process.argv.find((arg) => arg.startsWith(argumentPrefix))
    ?.slice(argumentPrefix.length);
  if (source) {
    await extractChromaArt(path.resolve(source), path.join(artDir, filename), maxSize);
  }
}

await fs.access(masterPath);

const master = sharp(masterPath);
const face = await master
  .clone()
  .extract({ left: 0, top: 0, width: 1024, height: 760 })
  .png()
  .toBuffer();

await Promise.all([
  makeAppIcon(16, path.join(publicDir, "favicon-16x16.png"), face),
  makeAppIcon(32, path.join(publicDir, "favicon-32x32.png"), face),
  makeAppIcon(48, path.join(publicDir, "favicon-48x48.png"), face),
  makeAppIcon(180, path.join(publicDir, "apple-touch-icon.png"), face),
  makeAppIcon(150, path.join(publicDir, "mstile-150x150.png"), face),
  makeAppIcon(192, path.join(iconsDir, "icon-192.png"), face),
  makeAppIcon(512, path.join(iconsDir, "icon-512.png"), face),
  makeMaskableIcon(192, path.join(iconsDir, "maskable-192.png")),
  makeMaskableIcon(512, path.join(iconsDir, "maskable-512.png")),
  makeAvatar(),
  makeLockup(),
  makeOpenGraphImage(),
  makeSocialSquare(),
]);

await writeIco([
  path.join(publicDir, "favicon-16x16.png"),
  path.join(publicDir, "favicon-32x32.png"),
  path.join(publicDir, "favicon-48x48.png"),
], path.join(publicDir, "favicon.ico"));

console.log("Generated Knitting brand assets in public/brand, public/icons, and public/.");

async function extractChromaMaster(input, output) {
  const { data, info } = await sharp(input)
    .removeAlpha()
    .raw()
    .toBuffer({ resolveWithObject: true });

  let keyR = 0;
  let keyG = 0;
  let keyB = 0;
  let keyCount = 0;

  for (let i = 0; i < data.length; i += 3) {
    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];
    if (g - Math.max(r, b) > 150) {
      keyR += r;
      keyG += g;
      keyB += b;
      keyCount += 1;
    }
  }

  keyR /= keyCount;
  keyG /= keyCount;
  keyB /= keyCount;
  const keyDominance = keyG - Math.max(keyR, keyB);
  const rgba = Buffer.alloc(info.width * info.height * 4);

  for (let src = 0, dest = 0; src < data.length; src += 3, dest += 4) {
    const r = data[src];
    const g = data[src + 1];
    const b = data[src + 2];
    const dominance = Math.max(0, g - Math.max(r, b));
    let alpha = Math.max(0, Math.min(1, 1 - dominance / keyDominance));

    if (alpha < 0.13) alpha = 0;
    if (alpha > 0.97) alpha = 1;

    if (alpha === 0) {
      rgba[dest] = 0;
      rgba[dest + 1] = 0;
      rgba[dest + 2] = 0;
      rgba[dest + 3] = 0;
      continue;
    }

    // Undo the green contribution in antialiased edge pixels.
    rgba[dest] = clampByte((r - (1 - alpha) * keyR) / alpha);
    rgba[dest + 1] = clampByte((g - (1 - alpha) * keyG) / alpha);
    rgba[dest + 2] = clampByte((b - (1 - alpha) * keyB) / alpha);
    rgba[dest + 3] = clampByte(alpha * 255);
  }

  const trimmed = await sharp(rgba, {
    raw: { width: info.width, height: info.height, channels: 4 },
  })
    .trim({ background: { r: 0, g: 0, b: 0, alpha: 0 }, threshold: 8 })
    .resize(928, 928, { fit: "inside", withoutEnlargement: false })
    .png()
    .toBuffer();

  const metadata = await sharp(trimmed).metadata();
  const left = Math.floor((1024 - metadata.width) / 2);
  const top = Math.floor((1024 - metadata.height) / 2);

  await sharp({
    create: {
      width: 1024,
      height: 1024,
      channels: 4,
      background: { r: 0, g: 0, b: 0, alpha: 0 },
    },
  })
    .composite([{ input: trimmed, left, top }])
    .png({ compressionLevel: 9 })
    .toFile(output);
}

async function extractChromaArt(input, output, maxSize) {
  const { data, info } = await sharp(input)
    .removeAlpha()
    .raw()
    .toBuffer({ resolveWithObject: true });

  let keyR = 0;
  let keyG = 0;
  let keyB = 0;
  let keyCount = 0;

  for (let i = 0; i < data.length; i += 3) {
    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];
    if (g - Math.max(r, b) > 150) {
      keyR += r;
      keyG += g;
      keyB += b;
      keyCount += 1;
    }
  }

  keyR /= keyCount;
  keyG /= keyCount;
  keyB /= keyCount;
  const keyDominance = keyG - Math.max(keyR, keyB);
  const rgba = Buffer.alloc(info.width * info.height * 4);

  for (let src = 0, dest = 0; src < data.length; src += 3, dest += 4) {
    const r = data[src];
    const g = data[src + 1];
    const b = data[src + 2];
    const dominance = Math.max(0, g - Math.max(r, b));
    let alpha = Math.max(0, Math.min(1, 1 - dominance / keyDominance));

    if (alpha < 0.13) alpha = 0;
    if (alpha > 0.97) alpha = 1;

    if (alpha === 0) {
      rgba[dest] = 0;
      rgba[dest + 1] = 0;
      rgba[dest + 2] = 0;
      rgba[dest + 3] = 0;
      continue;
    }

    rgba[dest] = clampByte((r - (1 - alpha) * keyR) / alpha);
    rgba[dest + 1] = clampByte((g - (1 - alpha) * keyG) / alpha);
    rgba[dest + 2] = clampByte((b - (1 - alpha) * keyB) / alpha);
    rgba[dest + 3] = clampByte(alpha * 255);
  }

  await sharp(rgba, {
    raw: { width: info.width, height: info.height, channels: 4 },
  })
    .trim({ background: { r: 0, g: 0, b: 0, alpha: 0 }, threshold: 8 })
    .resize(maxSize, maxSize, { fit: "inside", withoutEnlargement: true })
    .webp({ quality: 88, alphaQuality: 96, smartSubsample: true })
    .toFile(output);
}

async function makeAppIcon(size, output, mascot) {
  const radius = Math.max(3, Math.round(size * 0.22));
  const inset = Math.max(1, Math.round(size * 0.055));
  const mascotWidth = Math.round(size * 0.92);
  const mascotTop = Math.round(size * 0.08);
  const background = Buffer.from(`
    <svg width="${size}" height="${size}" xmlns="http://www.w3.org/2000/svg">
      <rect width="${size}" height="${size}" rx="${radius}" fill="${colors.orange}"/>
      <circle cx="${size / 2}" cy="${size * 0.47}" r="${size * 0.43}" fill="${colors.white}"/>
      <rect x="${inset}" y="${inset}" width="${size - inset * 2}" height="${size - inset * 2}" rx="${radius - inset}" fill="none" stroke="${colors.ink}" stroke-opacity=".16" stroke-width="${Math.max(1, size * 0.015)}"/>
    </svg>
  `);
  const foreground = await sharp(mascot)
    .resize({ width: mascotWidth, fit: "inside" })
    .png()
    .toBuffer();
  const meta = await sharp(foreground).metadata();

  await sharp(background)
    .composite([{
      input: foreground,
      left: Math.round((size - meta.width) / 2),
      top: Math.min(mascotTop, size - meta.height),
    }])
    .png({ compressionLevel: 9 })
    .toFile(output);
}

async function makeMaskableIcon(size, output) {
  const foreground = await master
    .clone()
    .resize({ width: Math.round(size * 0.66), height: Math.round(size * 0.66), fit: "contain" })
    .png()
    .toBuffer();
  const meta = await sharp(foreground).metadata();
  const background = Buffer.from(`
    <svg width="${size}" height="${size}" xmlns="http://www.w3.org/2000/svg">
      <rect width="${size}" height="${size}" fill="${colors.orange}"/>
      <circle cx="${size / 2}" cy="${size / 2}" r="${size * 0.38}" fill="${colors.white}"/>
    </svg>
  `);

  await sharp(background)
    .composite([{
      input: foreground,
      left: Math.round((size - meta.width) / 2),
      top: Math.round((size - meta.height) / 2),
    }])
    .png({ compressionLevel: 9 })
    .toFile(output);
}

async function makeAvatar() {
  const size = 512;
  const mascot = await master
    .clone()
    .resize({ width: 420, height: 420, fit: "contain" })
    .png()
    .toBuffer();
  const background = Buffer.from(`
    <svg width="${size}" height="${size}" xmlns="http://www.w3.org/2000/svg">
      <circle cx="256" cy="256" r="250" fill="${colors.white}" stroke="${colors.ink}" stroke-width="12"/>
    </svg>
  `);

  await sharp(background)
    .composite([{ input: mascot, left: 46, top: 48 }])
    .png({ compressionLevel: 9 })
    .toFile(path.join(brandDir, "knitting-avatar.png"));
}

async function makeLockup() {
  const width = 1400;
  const height = 400;
  const mascot = await master
    .clone()
    .resize({ width: 340, height: 340, fit: "contain" })
    .png()
    .toBuffer();
  const typography = Buffer.from(`
    <svg width="${width}" height="${height}" xmlns="http://www.w3.org/2000/svg">
      <text x="410" y="205" fill="${colors.ink}" font-family="Noto Sans, sans-serif" font-size="142" font-weight="800" letter-spacing="-5">Knitting</text>
      <text x="418" y="282" fill="${colors.orange}" font-family="Noto Sans, sans-serif" font-size="37" font-weight="700" letter-spacing="2">MULTI-THREADING RUNTIME FOR JAVASCRIPT</text>
    </svg>
  `);

  await sharp({
    create: {
      width,
      height,
      channels: 4,
      background: { r: 0, g: 0, b: 0, alpha: 0 },
    },
  })
    .composite([
      { input: mascot, left: 30, top: 30 },
      { input: typography, left: 0, top: 0 },
    ])
    .png({ compressionLevel: 9 })
    .toFile(path.join(brandDir, "knitting-lockup.png"));
}

async function makeOpenGraphImage() {
  const width = 1200;
  const height = 630;
  const mascot = await master
    .clone()
    .resize({ width: 410, height: 410, fit: "contain" })
    .png()
    .toBuffer();
  const background = Buffer.from(`
    <svg width="${width}" height="${height}" xmlns="http://www.w3.org/2000/svg">
      <defs>
        <radialGradient id="warm" cx="24%" cy="50%" r="72%">
          <stop offset="0" stop-color="#71401F"/>
          <stop offset=".5" stop-color="${colors.ink}"/>
          <stop offset="1" stop-color="#140C07"/>
        </radialGradient>
      </defs>
      <rect width="${width}" height="${height}" fill="url(#warm)"/>
      <circle cx="275" cy="315" r="224" fill="${colors.white}" stroke="${colors.cream}" stroke-width="10"/>
      <circle cx="275" cy="315" r="246" fill="none" stroke="${colors.orange}" stroke-opacity=".28" stroke-width="2"/>
      <text x="555" y="265" fill="${colors.white}" font-family="Noto Sans, sans-serif" font-size="112" font-weight="800" letter-spacing="-4">Knitting</text>
      <text x="563" y="334" fill="${colors.orange}" font-family="Noto Sans, sans-serif" font-size="32" font-weight="700">MULTI-THREADING RUNTIME</text>
      <text x="563" y="383" fill="${colors.peach}" font-family="Noto Sans, sans-serif" font-size="31">Move JavaScript off the main thread.</text>
      <text x="563" y="472" fill="${colors.cream}" font-family="Noto Sans, sans-serif" font-size="22" font-weight="700" letter-spacing="4">NODE.JS  •  DENO  •  BUN</text>
    </svg>
  `);

  await sharp(background)
    .composite([{ input: mascot, left: 70, top: 110 }])
    .png({ compressionLevel: 9, palette: true })
    .toFile(path.join(brandDir, "og-image.png"));
}

async function makeSocialSquare() {
  const size = 1200;
  const mascot = await master
    .clone()
    .resize({ width: 700, height: 700, fit: "contain" })
    .png()
    .toBuffer();
  const background = Buffer.from(`
    <svg width="${size}" height="${size}" xmlns="http://www.w3.org/2000/svg">
      <defs>
        <radialGradient id="warm" cx="50%" cy="38%" r="76%">
          <stop offset="0" stop-color="#70401F"/>
          <stop offset=".58" stop-color="${colors.ink}"/>
          <stop offset="1" stop-color="#140C07"/>
        </radialGradient>
      </defs>
      <rect width="${size}" height="${size}" fill="url(#warm)"/>
      <circle cx="600" cy="470" r="390" fill="${colors.white}" stroke="${colors.orange}" stroke-width="16"/>
      <text x="600" y="1015" text-anchor="middle" fill="${colors.white}" font-family="Noto Sans, sans-serif" font-size="118" font-weight="800" letter-spacing="-3">Knitting</text>
      <text x="600" y="1082" text-anchor="middle" fill="${colors.orange}" font-family="Noto Sans, sans-serif" font-size="29" font-weight="700" letter-spacing="3">MULTI-THREADING RUNTIME</text>
    </svg>
  `);

  await sharp(background)
    .composite([{ input: mascot, left: 250, top: 120 }])
    .png({ compressionLevel: 9, palette: true })
    .toFile(path.join(brandDir, "social-square.png"));
}

async function writeIco(imagePaths, output) {
  const images = await Promise.all(imagePaths.map((imagePath) => fs.readFile(imagePath)));
  const header = Buffer.alloc(6);
  header.writeUInt16LE(0, 0);
  header.writeUInt16LE(1, 2);
  header.writeUInt16LE(images.length, 4);

  const entries = Buffer.alloc(images.length * 16);
  let offset = header.length + entries.length;

  images.forEach((image, index) => {
    const size = Number(path.basename(imagePaths[index]).match(/favicon-(\d+)x/)?.[1]);
    const entry = index * 16;
    entries.writeUInt8(size === 256 ? 0 : size, entry);
    entries.writeUInt8(size === 256 ? 0 : size, entry + 1);
    entries.writeUInt8(0, entry + 2);
    entries.writeUInt8(0, entry + 3);
    entries.writeUInt16LE(1, entry + 4);
    entries.writeUInt16LE(32, entry + 6);
    entries.writeUInt32LE(image.length, entry + 8);
    entries.writeUInt32LE(offset, entry + 12);
    offset += image.length;
  });

  await fs.writeFile(output, Buffer.concat([header, entries, ...images]));
}

function clampByte(value) {
  return Math.max(0, Math.min(255, Math.round(value)));
}
