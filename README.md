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
graph, progress summary) is generated with
[VersoBlueprint](https://github.com/leanprover/verso-blueprint) from the
sources in `blueprint/` and deployed to GitHub Pages:

> https://jjdishere.github.io/weil_conj/blueprint/

The blueprint is a self-contained Lake package nested in `blueprint/`; it
depends on the parent project via a path dependency and does not affect the
main project's build or dependency graph.

To build it locally:

```bash
cd blueprint
lake exe cache get   # Mathlib build cache
lake exe vbp build   # writes the site to _out/site/html-multi/
```

or run the CI entry point `blueprint/scripts/ci-pages.sh`. The GitHub
workflow `.github/workflows/blueprint.yml` builds the site, deploys it to
the `gh-pages` branch under `/blueprint`, and publishes previews for pull
requests that touch the blueprint or the Lean sources under
`/preview/<pr>/blueprint`.

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "Deploy from a branch", and choose
  the branch `gh-pages` with folder `/ (root)`. (The blueprint workflow
  publishes the site to that branch; the previously suggested "GitHub
  Actions" source is not used by this repository's workflows.)

After following the steps above, you can remove this section from the README file.
