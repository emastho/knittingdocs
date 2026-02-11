// @ts-check
import { defineConfig } from "astro/config";
import starlight from "@astrojs/starlight";
import remarkMath from "remark-math";
import rehypeKatex from "rehype-katex";

// https://astro.build/config
export default defineConfig({
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
            content: "/light_logo.svg",
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
            content: "/light_logo.svg",
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
      customCss: ["./src/styles/katex.css"],
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
      ],
    }),
  ],
});
