// @ts-check
import { defineConfig } from 'astro/config';
import starlight from '@astrojs/starlight';

// https://astro.build/config
export default defineConfig({
	integrations: [
		starlight({
			title: 'Knitting',
			social: [{ icon: 'github', label: 'GitHub', href: 'https://github.com/mimiMonads/knitting' }],
			sidebar: [
				{
					label: 'Getting Started',
					items: [
						{ label: 'Overview', slug: 'guides/overview' },
						{ label: 'Installation', slug: 'guides/installation' },
						{ label: 'Quick Start', slug: 'guides/quick-start' },
					],
				},
				{
					label: 'Guides',
					items: [
						{ label: 'Defining Tasks', slug: 'guides/defining-tasks' },
						{ label: 'Creating Pools', slug: 'guides/creating-pools' },
						{ label: 'Batching and send()', slug: 'guides/batching' },
						{ label: 'Balancing Strategies', slug: 'guides/balancing' },
						{ label: 'Inliner Lane', slug: 'guides/inliner' },
						{ label: 'Task Timeouts', slug: 'guides/timeouts' },
						{ label: 'Runtime Tuning', slug: 'guides/runtime-tuning' },
						{ label: 'Custom Worker Entry', slug: 'guides/custom-workers' },
						{ label: 'Debugging', slug: 'guides/debugging' },
					],
				},
				{
					label: 'Reference',
					items: [
						{ label: 'API', slug: 'reference/api' },
						{ label: 'createPool Options', slug: 'reference/create-pool-options' },
						{ label: 'Task Timeouts', slug: 'reference/task-timeouts' },
						{ label: 'Supported Payloads', slug: 'reference/payloads' },
						{ label: 'Worker Entry', slug: 'reference/worker-entry' },
					],
				},
				{
					label: 'Examples',
					autogenerate: { directory: 'examples' },
				},
				{ label: 'Benchmarks', slug: 'benchmarks' },
				{ label: 'License', slug: 'license' },
			],
		}),
	],
});
