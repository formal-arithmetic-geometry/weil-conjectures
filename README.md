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

`blueprint/src/content.tex` selects which version to build; it currently
inputs `version/detailed.tex`, the worked-out Nagata compactification and
proper base change chapters. Statements there carry `def:`, `lemma:`,
`prop:`, `thm:` and `cor:` labels, and those are the labels that the
per-declaration `(blueprint: ...)` tags in the Lean sources cite. `lake exe
checkdecls` checks the references pointing the other way, from `\lean{...}`
in `blueprint/src` to Lean declarations.

A separate sketch blueprint lives in its own repository,
`formal-arithmetic-geometry/weil-conjectures-blueprint`, whose top-level
blocks are named `sec-six-functors`, `sec-zeta-weil`, `sec-abelian-varieties`
and so on. Those `sec-*` names are *not* labels of `blueprint/src`: nothing
in the Lean sources refers to them and `checkdecls` does not see them, so
they should not appear in `(blueprint: ...)` tags.

Building locally requires a TeX distribution, Graphviz and
`pip install leanblueprint`; then, from the repository root:

```bash
leanblueprint web   # writes the site to blueprint/web/
leanblueprint pdf   # writes blueprint/print/print.pdf
```

No workflow builds or publishes the blueprint: it is a local-only build.

## Where the mathematics lives

Before stating a result, check whether this repository already proves it:

* the zeta function `Z(X, t)` is `AlgebraicGeometry.Scheme.Hom.zetaSeries`,
  defined in `Comparator/Weil/Definitions.lean`, with its theory in
  `WeilConjectures/ZetaSeries.lean`;
* the two headline statements are
  `AlgebraicGeometry.Scheme.zetaSeries_rational` and
  `AlgebraicGeometry.Scheme.weil_conjectures` in
  `WeilConjectures/Statement.lean`;
* Nagata compactification is `AlgebraicGeometry.NagataCompactification` in
  `WeilConjectures/Compactification/NagataCompactification.lean`, built on
  the rest of `WeilConjectures/Compactification/`;
* the six operations on the étale and pro-étale derived categories are
  constructed in `WeilConjectures/SixFunctors/`.

New declarations are named and namespaced as if they were headed for Mathlib
(`AlgebraicGeometry.*`, `CategoryTheory.*`, ...) and go into the topic tree
they belong to, not into a tree named after a document's sectioning. A file
under `WeilConjectures/Mathlib/` must mirror a file that already exists in
Mathlib.

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.

No GitHub Pages configuration is needed: no workflow publishes a site, so
the **Pages** settings can be left disabled.

After following the steps above, you can remove this section from the README file.
