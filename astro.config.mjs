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
const socialImagePath = base ? `${base}/logo.png` : "/logo.png";
const socialImage = site
  ? new URL(socialImagePath, site).toString()
  : socialImagePath;

// https://astro.build/config
export default defineConfig({
  ...(site ? { site } : {}),
  ...(base ? { base } : {}),
  markdown: {
    remarkPlugins: [remarkMath],
    rehypePlugins: [rehypeKatex],
  },
  integrations: [
    starlight({
      title: "Knitting",
      description:
        "Knitting is a shared-memory IPC library for Node.js, Deno, and Bun, designed for low-latency worker task execution and high-throughput parallel JavaScript.",
      favicon: "/light_logo.svg",
      head: [
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
            content: "Knitting logo",
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
            content: "Knitting logo",
          },
        },
        {
          tag: "link",
          attrs: {
            rel: "icon",
            href: "/logo.svg",
            type: "image/svg+xml",
            media: "(prefers-color-scheme: dark)",
          },
        },
        {
          tag: "link",
          attrs: {
            rel: "icon",
            href: "/light_logo.svg",
            type: "image/svg+xml",
            media: "(prefers-color-scheme: light)",
          },
        },
      ],
      customCss: ["./src/styles/katex.css", "./src/styles/headings.css"],
      social: [{
        icon: "github",
        label: "GitHub",
        href: "https://github.com/mimiMonads/knitting",
      }],
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
