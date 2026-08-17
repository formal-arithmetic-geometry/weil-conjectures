# weil-conjectures

A Lean 4 formalization project for the **Weil conjectures**: rationality of
the zeta function, the functional equation, and the Riemann hypothesis for
smooth, proper, geometrically integral varieties over finite fields. The
target statements live in `WeilConjectures/Statement.lean`
(`AlgebraicGeometry.Scheme.weil_conjectures` and
`AlgebraicGeometry.Scheme.zetaSeries_rational`), formulated purely
arithmetically in terms of integer polynomials and their complex roots.

## Blueprint

A browsable blueprint (chapters, statement/proof dependencies, dependency
graph, progress summary) is written in LaTeX under `blueprint/src/` and
built with [leanblueprint](https://github.com/PatrickMassot/leanblueprint).

The content lives in `blueprint/src/content.tex` and is currently empty.

Building locally requires a TeX distribution, Graphviz and
`pip install leanblueprint`; then, from the repository root:

```bash
leanblueprint web   # writes the site to blueprint/web/
leanblueprint pdf   # writes blueprint/print/print.pdf
```

No workflow builds or publishes the blueprint: it is a local-only build.

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.

No GitHub Pages configuration is needed: no workflow publishes a site, so
the **Pages** settings can be left disabled.

After following the steps above, you can remove this section from the README file.
