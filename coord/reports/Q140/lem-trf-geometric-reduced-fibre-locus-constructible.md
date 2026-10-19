## Worker report

The module `Sheaf.TraceFormula.GeometricReducedFibreLocusConstructible` states
`AlgebraicGeometry.geometricReduced_fibre_locus_constructible`; its proof is `sorry` and
no mathematical result is proved.  The predicate is the constructibility of
`{t : T | IsReduced (Limits.pullback f
 (Scheme.fromSpecAlgebraicClosureResidueField T t))}`.  The latter is the chosen
algebraic-closure geometric fibre from Mathlib/WeilConjectures' canonical construction.

The source is Stacks Project `literature/stacks-project/more-morphisms.tex`, Tag 0579
(`lemma-geometrically-reduced-constructible`), with Topology Tag 053W for the qcqs
local-to-global step and varieties Tags 035X and 020I for the algebraic-closure test.
The blueprint is `lem-trf-geometric-reduced-fibre-locus-constructible`.

The Lean statement renders each part of the node as follows:

* `f : X ⟶ T`, with `X T : Scheme.{u}`, renders the morphism of schemes
  ([def-pc-scheme]).
* `[QuasiCompact f]` renders that `f` is quasi-compact.
* `[LocallyOfFinitePresentation f]` renders that `f` is locally of finite presentation.
* `[CompactSpace T] [QuasiSeparatedSpace T]` render that the base `T` is quasi-compact and
  quasi-separated, using Mathlib's scheme/topological equivalence for these properties.
* The set predicate uses `Scheme.fromSpecAlgebraicClosureResidueField T t` and the categorical
  pullback, so it is exactly the geometric fibre over the chosen algebraic closure of
  `T.residueField t` ([def-weil-geometric-fibre]).
* `IsReduced` is Mathlib's scheme reducedness class ([def-pc-reduced-scheme]), equivalent to
  every local ring having no nonzero nilpotents.  Therefore the conclusion
  `Topology.IsConstructible ...` is precisely constructibility in
  [def-weil-constructible-subset].  Empty fibres satisfy this predicate vacuously, and no
  flatness or Noetherian hypothesis is present.

Dependency declarations used:

* `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
* `def-sbc-locally-finite-presentation`: `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  declaration `AlgebraicGeometry.LocallyOfFinitePresentation`.
* `def-weil-pbc-scheme-conventions`: convention node; its relevant scheme properties are the
  Mathlib declarations `AlgebraicGeometry.QuasiCompact`, `AlgebraicGeometry.QuasiSeparated`,
  `Topology.CompactSpace`, and `Topology.QuasiSeparatedSpace`.
* `def-weil-geometric-fibre`: Mathlib `CategoryTheory.Limits.pullback` together with
  `WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField` declaration
  `AlgebraicGeometry.Scheme.fromSpecAlgebraicClosureResidueField`.
* `def-weil-constructible-subset`: Mathlib `Topology.IsConstructible`.
* `def-pc-reduced-scheme`: Mathlib `AlgebraicGeometry.IsReduced`.

Edge cases checked: `X` may be empty; a geometric fibre may be empty and then reduced
vacuously; no flatness, Noetherian, characteristic, or nonemptiness assumption is introduced;
the universe of the scheme and its algebraic closure is the single explicit `u` used by the
Mathlib geometric-fibre construction.

Searches made:

* `msearch.py Q140 lem-trf-geometric-reduced-fibre-locus-constructible grep "geometrically
  reduced fibre locus" AlgebraicGeometry`: zero hits.
* Existing sandbox search log (`searches.jsonl`): the same grep query, zero hits.
* Direct `rg` over `WeilConjectures/` and project `lean/Sheaf/` for geometric-reduced,
  reduced-fibre, and constructible-locus names: no exact declaration.  The nearby
  `AlgebraicGeometry.GeometricallyReduced` interface and the irreducible-fibre theorem have
  different statements and are not exact matches.
* The node's recorded searches were also checked: LeanSearch, Loogle, LeanFinder and grep
  all returned only generic constructibility or smooth/étale loci, with no exact match.

No new definition node, dependency module, statement correction, or `STATEMENT-DISPUTED` flag
is needed.

## Second reading by Q140

I reread the node, all six statement dependencies, their recorded declarations/mathlib matches,
and the complete module. The four hypotheses are represented by the morphism binder and the
four explicit typeclass binders. The conclusion has one set-builder clause: its point is a
scheme point `t : T`, its fibre is the pullback along the canonical algebraic-closure point,
and its property is exactly scheme reducedness; the outer predicate is
`Topology.IsConstructible`. No flatness or Noetherian assumption has slipped into the type,
and the empty-fibre case remains included. The source and Mathlib signatures compile cleanly
with `scompile.py`; no change was required after the second reading.
