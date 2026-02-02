// @ts-check
import { defineConfig } from "astro/config";
import starlight from "@astrojs/starlight";

// https://astro.build/config
export default defineConfig({
  integrations: [
    starlight({
      title: "Knitting",
      social: [{
        icon: "github",
        label: "GitHub",
        href: "https://github.com/mimiMonads/knitting",
      }],
      sidebar: [
        {
          label: "Getting Started",
          autogenerate: {
            directory: "start"
          }
        },
        {
          label: "Guides",
          autogenerate: { directory: "guides"}
        },
        {
          label: "Examples",
          collapsed: true,
          autogenerate: { directory: "examples" },
        },
        { label: "Benchmarks",  
          collapsed: true,
          slug: "benchmarks" , autogenerate: { directory: "benchmarks"} },
 
      ],
    }),
  ],
});
