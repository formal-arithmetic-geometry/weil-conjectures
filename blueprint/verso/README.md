# Verso Blueprint — Nagata compactification

A [Verso Blueprint](https://github.com/leanprover/verso-blueprint) for the formalization of
Nagata's compactification theorem in this repository.

The node set and the node labels follow `blueprint/progress/current-progress.tex`, so the
two documents can be read side by side. Every node carries, in its `(lean := "...")` option,
the names of the declarations **of this project** which realise it — no Mathlib declarations
are listed, so the progress summary reports on work done here. Facts imported from the
ambient library (existence and universal property of scheme-theoretic images, Zariski's Main
Theorem) are stated in prose in the last chapter and are deliberately *not* Blueprint nodes.

## Layout

```
blueprint/verso/
  lakefile.lean                       package definition
  lean-toolchain                      pinned to the toolchain of the main project
  NagataBlueprint.lean                top-level document: chapters + graph + summary
  NagataBlueprintMain.lean            site generator entry point
  NagataBlueprint/
    Prelude.lean                      imports of WeilConjectures + KaTeX macro prelude
    Chapters/
      Compactifications.lean          the notion, immersions, closed subschemes, base change
      ProjectiveSpace.lean            relative projective space, the quasi-affine base case
      IdealSheaves.lean               finite-type quasi-coherent ideal sheaves
      Blowups.lean                    the blow-up, admissible centres, density, boundaries
      StrictTransforms.lean           strict transforms; Tag 080E
      Conrad.lean                     elimination of indeterminacy after Deligne and Conrad; Tag 081S
      Modifications.lean              Tags 0F3Y, 0F3X, 0F3Z, 0F3W; boundary preparation
      TwoOpen.lean                    prepared sides, comparison space, the two-open theorem
      Noetherian.lean                 induction over a dense affine cover
      Approximation.lean              Noetherian approximation and finite-presentation descent
      Nagata.lean                     the final theorem, scope, and imported inputs
```

## Building

```bash
cd blueprint/verso
lake update           # first time only: fetches verso-blueprint and its dependencies
lake exe vbp discover
lake exe vbp build    # writes the site to _out/site
lake exe vbp query labels
```

`lake exe vbp build` is the correctness boundary for edits to the chapter sources.

## A note on the packaging

This directory is a Lake package of its own and requires the project by path
(`require «weil-conjectures» from ".."/".."`). That keeps Verso out of the main
`lakefile.toml`, but Lake will resolve the transitive dependencies (Mathlib, proetale, …)
into `blueprint/verso/.lake/packages`, i.e. a second checkout, and the first build needs its
own `lake exe cache get` for Mathlib.

If that duplication is unwelcome, the alternative is to drop this `lakefile.lean` and wire
the same sources into the root `lakefile.toml` instead, which shares the existing `.lake`
directory and the already-built `WeilConjectures` olean files:

```toml
[[require]]
name = "VersoBlueprint"
git = "https://github.com/leanprover/verso-blueprint"
rev = "v4.33.0"

[[lean_lib]]
name = "NagataBlueprint"
srcDir = "blueprint/verso"
roots = ["NagataBlueprint"]

[[lean_exe]]
name = "nagata-blueprint"
srcDir = "blueprint/verso"
root = "NagataBlueprintMain"
supportInterpreter = true
```

Leave `NagataBlueprint` out of `defaultTargets` so that ordinary builds of the project are
unaffected. Note that the root package would then also need
`leanOptions.experimental.module = true` if it is not already implied by the toolchain.

## Editing conventions

* Labels are stable identifiers; they drive graph nodes, summary rows, cross references and
  the exported metadata. Do not rename them casually.
* `{uses "label"}[]` and `(uses := "label")` create dependency edges; `{bpref "label"}[]`
  links without creating an edge.
* Statement dependencies go on the statement block, proof dependencies on the `:::proof`
  block.
* When a declaration is renamed in `WeilConjectures`, update the corresponding
  `(lean := "...")` entry; `lake exe vbp build` reports names that no longer resolve.
