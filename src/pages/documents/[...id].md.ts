import type { APIRoute, GetStaticPaths } from "astro";
import { cleanBody, COMPATIBILITY, docUrl, loadDocs, rawBodyFor } from "../../lib/llms";

export const prerender = true;

export const getStaticPaths: GetStaticPaths = async () =>
  (await loadDocs()).map((doc) => ({
    params: { id: doc.id.toLowerCase() },
    props: { id: doc.id, title: doc.data.title, description: doc.data.description },
  }));

export const GET: APIRoute = ({ props, site }) => new Response([
  `# ${props.title}`, "", `URL: ${docUrl(props.id, site)}`, "",
  COMPATIBILITY, "", props.description ?? "", "",
  cleanBody(rawBodyFor(props.id)), "",
].join("\n"), { headers: { "content-type": "text/markdown; charset=utf-8" } });
