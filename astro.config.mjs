// @ts-check
import { fileURLToPath } from "node:url";
import { defineConfig } from "astro/config";
import starlight from "@astrojs/starlight";
import remarkMath from "remark-math";
import rehypeKatex from "rehype-katex";

const githubOwner = process.env.GITHUB_REPOSITORY_OWNER;
const githubRepo = process.env.GITHUB_REPOSITORY?.split("/")[1];
const githubPagesUrl = githubOwner
  ? `https://${githubOwner}.github.io/`
  : undefined;
const explicitSiteCandidates = [
  process.env.SITE_URL,
  process.env.URL,
  process.env.DEPLOY_PRIME_URL,
  process.env.CF_PAGES_URL,
  process.env.VERCEL_PROJECT_PRODUCTION_URL,
  process.env.VERCEL_URL,
];
const hasExplicitSite = explicitSiteCandidates.some((value) =>
  String(value || "").trim().length > 0
);

const siteUrlCandidates = [...explicitSiteCandidates, githubPagesUrl];

function normalizeBase(value) {
  const trimmed = String(value || "").trim();
  if (!trimmed) return undefined;
  const collapsed = trimmed.replace(/^\/+|\/+$/g, "");
  if (!collapsed) return undefined;
  return `/${collapsed}`;
}

function normalizeSiteUrl(value) {
  const trimmed = String(value || "").trim();
  if (!trimmed) return undefined;

  const withProtocol = /^https?:\/\//i.test(trimmed)
    ? trimmed
    : `https://${trimmed}`;
  try {
    return new URL(withProtocol).toString();
  } catch {
    return undefined;
  }
}

function resolveSiteUrl() {
  for (const candidate of siteUrlCandidates) {
    const normalized = normalizeSiteUrl(candidate);
    if (normalized) return normalized;
  }
  return undefined;
}

const site = resolveSiteUrl();
const inferredGithubBase = !hasExplicitSite &&
    githubOwner &&
    githubRepo &&
    githubRepo.toLowerCase() !== `${githubOwner.toLowerCase()}.github.io`
  ? `/${githubRepo}`
  : undefined;
const base = normalizeBase(
  process.env.SITE_BASE || process.env.BASE_PATH || inferredGithubBase,
);
const assetPath = (asset) => {
  const normalized = String(asset).replace(/^\/+/, "");
  return base ? `${base}/${normalized}` : `/${normalized}`;
};
const socialImagePath = assetPath("brand/og-image-worker-runtime-gradient.png");
const socialImage = site
  ? new URL(socialImagePath, site).toString()
  : socialImagePath;
const brandArtVariables = `:root {
  --knitting-art-avatar: url("${assetPath("brand/knitting-avatar.png")}");
  --knitting-art-knitting: url("${assetPath("brand/art/knitting-lamb.webp")}");
  --knitting-art-laptop: url("${assetPath("brand/art/laptop-lamb.webp")}");
  --knitting-art-mascot: url("${assetPath("brand/knitting-mascot.png")}");
  --knitting-art-sleeping: url("${assetPath("brand/art/sleeping-lamb.webp")}");
}`;
const crossOriginIsolationHeaders = {
  "Cross-Origin-Opener-Policy": "same-origin",
  "Cross-Origin-Embedder-Policy": "require-corp",
};

// https://astro.build/config
export default defineConfig({
  // The browser page used to live at the site root; keep the old URL working.
  redirects: {
    "/browser": "/guides/browser/",
    "/guides": "/start/quick-start/",
  },
  ...(site ? { site } : {}),
  ...(base ? { base } : {}),
  server: {
    headers: crossOriginIsolationHeaders,
  },
  markdown: {
    remarkPlugins: [remarkMath],
    rehypePlugins: [rehypeKatex],
  },
  vite: {
    resolve: {
      alias: [{ find: /^knitting$/, replacement: "@vixeny/knitting" }],
    },
    // The knitting 0.1.70 tarball was packed with a stale `src/worker/loop.js`:
    // it dynamically imports "../debug/handle.ts", but only `handle.js` ships.
    // (A current `tsc -p tsconfig.npm.json` emits ".js" there, so a rebuild of
    // the package fixes it at the source.) Vite's dependency scanner follows the
    // `knitting` imports in our src/assets/code/ samples -- which we only ever
    // read as `?raw` text -- and cannot resolve the specifier. Vite's own
    // aliases do not reach esbuild's resolver, so redirect it here instead.
    // Remove once knitting is republished from a clean build.
    optimizeDeps: {
      esbuildOptions: {
        plugins: [
          {
            name: "knitting-debug-handle",
            setup(build) {
              build.onResolve(
                { filter: /^\.\.\/debug\/handle\.ts$/ },
                () => ({
                  path: fileURLToPath(
                    new URL(
                      "./node_modules/@vixeny/knitting/src/debug/handle.js",
                      import.meta.url,
                    ),
                  ),
                }),
              );
            },
          },
        ],
      },
    },
  },
  integrations: [
    starlight({
      title: "Knitting",
      description:
        "A zero-dependency concurrency runtime for Node.js, Deno, and Bun. Run typed JavaScript tasks on threads or isolated processes without blocking the main thread.",
      favicon: assetPath("brand/knitting-avatar.png"),
      head: [
        {
          tag: "style",
          content: brandArtVariables,
        },
        {
          tag: "meta",
          attrs: {
            property: "og:site_name",
            content: "Knitting",
          },
        },
        {
          tag: "meta",
          attrs: {
            property: "og:image",
            content: socialImage,
          },
        },
        {
          tag: "meta",
          attrs: {
            property: "og:image:alt",
            content: "The Knitting sheep mascot beside the Knitting wordmark, with Node.js, Deno, and Bun listed below",
          },
        },
        {
          tag: "meta",
          attrs: {
            property: "og:image:type",
            content: "image/png",
          },
        },
        {
          tag: "meta",
          attrs: {
            property: "og:image:width",
            content: "1200",
          },
        },
        {
          tag: "meta",
          attrs: {
            property: "og:image:height",
            content: "630",
          },
        },
        {
          tag: "meta",
          attrs: {
            name: "twitter:card",
            content: "summary_large_image",
          },
        },
        {
          tag: "meta",
          attrs: {
            name: "twitter:image",
            content: socialImage,
          },
        },
        {
          tag: "meta",
          attrs: {
            name: "twitter:image:alt",
            content: "The Knitting sheep mascot beside the Knitting wordmark, with Node.js, Deno, and Bun listed below",
          },
        },
        {
          tag: "meta",
          attrs: {
            name: "theme-color",
            content: "#160C08",
          },
        },
        {
          tag: "link",
          attrs: {
            rel: "icon",
            href: assetPath("brand/knitting-avatar.png"),
            type: "image/png",
            sizes: "512x512",
          },
        },
        {
          tag: "link",
          attrs: {
            rel: "apple-touch-icon",
            href: assetPath("brand/knitting-avatar.png"),
            sizes: "512x512",
          },
        },
        {
          tag: "link",
          attrs: {
            rel: "manifest",
            href: assetPath("site.webmanifest"),
          },
        },
        {
          tag: "meta",
          attrs: {
            name: "msapplication-TileColor",
            content: "#FF7A1F",
          },
        },
      ],
      customCss: [
        "./src/styles/layers.css",
        "./src/styles/katex.css",
        "./src/styles/headings.css",
        "./src/styles/home-cards.css",
        "./src/styles/brand-art.css",
      ],
      social: [{
        icon: "github",
        label: "GitHub",
        href: "https://github.com/mimiMonads/knitting",
      }],
      components: {
        SocialIcons: "./src/components/SocialIcons.astro",
      },
      sidebar: [
        {
          label: "Getting Started",
          autogenerate: {
            directory: "start",
          },
        },
        {
          label: "Guides",
          autogenerate: { directory: "guides" },
        },
        {
          label: "Examples",
          collapsed: true,
          autogenerate: { directory: "examples" },
        },
        {
          label: "Benchmarks",
          collapsed: true,
          autogenerate: { directory: "benchmarks" },
        },
        {
          label: "Extras",
          collapsed: true,
          autogenerate: { directory: "extras" },
        },
      ],
    }),
  ],
});
