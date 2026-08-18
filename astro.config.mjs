// @ts-check
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
const socialImagePath = assetPath("brand/og-image.png");
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
  },
  integrations: [
    starlight({
      title: "Knitting",
      description:
        "A zero-dependency worker pool for running CPU-heavy JavaScript off the main thread in Node.js, Deno, and Bun.",
      favicon: "/favicon.ico",
      head: [
        {
          tag: "style",
          content: brandArtVariables,
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
            content: "Knitting's sheep mascot beside a JavaScript worker-pool illustration",
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
            content: "Knitting's sheep mascot beside a JavaScript worker-pool illustration",
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
            href: assetPath("favicon-32x32.png"),
            type: "image/png",
            sizes: "32x32",
          },
        },
        {
          tag: "link",
          attrs: {
            rel: "icon",
            href: assetPath("favicon-16x16.png"),
            type: "image/png",
            sizes: "16x16",
          },
        },
        {
          tag: "link",
          attrs: {
            rel: "apple-touch-icon",
            href: assetPath("apple-touch-icon.png"),
            sizes: "180x180",
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
        {
          tag: "meta",
          attrs: {
            name: "msapplication-TileImage",
            content: assetPath("mstile-150x150.png"),
          },
        },
      ],
      customCss: [
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
