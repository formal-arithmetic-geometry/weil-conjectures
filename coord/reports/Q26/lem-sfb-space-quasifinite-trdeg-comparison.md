## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceQuasifiniteTrdegComparison` states
`AlgebraicGeometry.AlgebraicSpace.trdeg_eq_of_chartwise_isLocallyQuasiFinite`.
Its only proof is `sorry`. It introduces no definition and changes only the item's
`lean` field. No statement correction or disputed statement is needed.

Source read: `literature/stacks-project/spaces-morphisms.tex`,
`lemma-compare-tr-deg` (Tag 06RX), and `definition-dimension-fibre` with its
following chart interpretation. The source proof reduces to scheme charts,
uses finiteness of the residue extension, and concludes equality of
transcendence degrees. The declaration docstring records all four steps of
the accepted DAG proof, including the isolated-fibre-point route to finiteness.

Hypothesis and clause correspondence:

- The ground field is `{k : Type u} [Field k]`.
- The scheme over k is `Y : Over (Spec (CommRingCat.of k))`, with underlying
  scheme `Y.left` and structure morphism `Y.hom`.
  `[LocallyOfFiniteType Y.hom]` is exactly local finite type over k, with no
  quasi-compactness added.
- The algebraic space over k is `E : AlgebraicSpace (Spec (CommRingCat.of k))`,
  using the recorded fppf-sheaf definition with representable diagonal and
  an étale surjective atlas. No atlas is chosen in this statement.
- The morphism over k is `g : E.obj.obj ⟶ yoneda.obj Y`. These are presheaves
  on schemes over `Spec k`; naturality is precisely the over-k compatibility.
  Yoneda represents a scheme target without introducing a duplicate algebraic
  space associated to Y.
- `hg` quantifies over every `W : Over (Spec k)` and every chart natural
  transformation `c : yoneda.obj W ⟶ E.obj.obj`. `IsEtale c` includes
  representability as in the dependency. The scheme morphism representing
  the composite is `(yoneda.preimage (c ≫ g)).left`.
  Requiring its `IsLocallyQuasiFinite` uses the Stacks finite-type-inclusive
  predicate, not Mathlib's weaker bare `LocallyQuasiFinite`.
- `e : Point E.obj.obj` is the field-valued point class, with the recorded
  atlas topology imported. The assertion needs only the underlying points.
  The chosen chart is `W,c,hc`, and `w : W.left` lies above e exactly by
  `hw : schemePointMap c w = e`.
- The first conjunct is the cardinal equality of `Algebra.trdeg` for
  `W.left.residueField w` and
  `Y.left.residueField ((yoneda.preimage (c ≫ g)).left w)`.
  The latter point is g(e): it is evaluated using the representative supplied
  by c,w and hw. This avoids any choice of a representative of e or a new
  point-comparison map. Since Y is a scheme, changing representatives does
  not change this target scheme point.
- The explicit algebra arguments are
  `(W.hom.residueFieldAlgebraMap w).toAlgebra` and the analogous expression
  for Y at the composite image. These are the canonical k-structures from
  structure morphisms and residue maps, never arbitrary algebra structures.
- The second conjunct quantifies over any other `W',c',w'` with `IsEtale c'`
  and `schemePointMap c' w' = e`, and equates its residue transcendence degree
  with that of w. This is the stated independence from chart and chosen point.
- No hypothesis requires either chart to be surjective, quasi-compact,
  separated, affine, or nonempty. No finiteness of transcendence degree is
  encoded by replacing the cardinal with a natural number.

Dependency declarations read and used (including through public imports):

- `Field` from `Mathlib.Algebra.Field.Defs` (def-weil-field).
- `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec` and `Spec.map` from
  `Mathlib.AlgebraicGeometry.Scheme` (def-pc-scheme, def-weil-affine-spectrum).
- `LocallyOfFiniteType` from `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  (def-weil-finite-type-morphism).
- `AlgebraicGeometry.AlgebraicSpace` and `AlgebraicSpace.IsEtale` from
  `Sheaf.AlgebraicGeometry.AlgebraicSpace` (def-trf-algebraic-space).
  The latter uses `Etale` from `Mathlib.AlgebraicGeometry.Morphisms.Etale`
  (def-weil-etale-morphism) on each representing scheme projection.
- `Scheme.Hom.IsLocallyQuasiFinite` and `IsQuasiFiniteAtPoint` from
  `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`
  (pqf-def-quasifinite).
- `AlgebraicSpace.pointTopologicalSpace` from
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`
  (def-a1-space-point-topology), with `Point` and `schemePointMap` supplied
  by its public import `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`.
- `Scheme.residueField` and `Scheme.Hom.residueFieldMap` from
  `Mathlib.AlgebraicGeometry.ResidueField` (def-weil-residue-field).
  `Scheme.Hom.residueFieldAlgebraMap`, read in `WeilConjectures.ZetaSeries`,
  composes the canonical ground-field identification with that residue map.
- `Algebra.trdeg` from `Mathlib.RingTheory.AlgebraicIndependent.Basic`
  (def-kun-transcendence-degree).
- The proof imports the recorded modules
  `WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite`,
  `WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated`, and
  `WeilConjectures.AlgebraicGeometry.FiniteDimensionalResidueFieldOfIsolatedFiberPoint`.
  Their declarations are respectively
  `Scheme.Hom.locallyOfFiniteType_of_isLocallyQuasiFinite`,
  `Scheme.Hom.quasiFiniteAtPoint_isolated_in_fiber`, and
  `Scheme.Hom.finiteDimensional_residueField_of_isOpen_singleton_asFiber`.
- The field-extension notion is `Algebra` from `Mathlib.Algebra.Algebra.Defs`
  (def-pc-field-extension). For lem-kun-transcendence-degree-tower, the
  proof imports `Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis`
  and `Mathlib.RingTheory.AlgebraicIndependent.Transcendental`; signatures of
  `lift_trdeg_add_eq`, `trdeg_add_eq` and `trdeg_eq_zero_iff` were read.

Edge cases checked before writing: an empty chart has no w and imposes no
case; a chart missing a particular e also has no w satisfying hw. The
identity chart gives equality with itself. A non-surjective open chart
works at every point it contains. Finite inseparable residue extensions
remain algebraic, so no perfection or characteristic restriction is needed.
The squaring map on the affine line has finite residue extensions at closed
and generic points, including in characteristic two. Disjoint unions of
arbitrarily many quasi-finite charts need no quasi-compactness. All schemes,
fields, and chart tests share the recorded algebraic-space size universe u;
points have the existing quotient universe u+1. There is no independent
smaller test universe and no auto-bound implicit (`autoImplicit false`).

Actual searches for an existing statement (msearch logs are in the sandbox):

- LeanSearch: `locally quasi finite algebraic space charts residue field
  transcendence degree` returned eight hits, including
  `AlgebraicGeometry.LocallyQuasiFinite.mk` and
  `Algebra.instFiniteResidueFieldOfQuasiFiniteAt`. These are scheme/ring
  ingredients, not the chart statement with its canonical k-structures.
- Loogle: `"LocallyQuasiFinite", "trdeg"` returned zero hits.
- LeanFinder: `An etale scheme chart of an algebraic space locally quasi
  finite over a scheme over a field preserves residue field transcendence
  degrees` returned eight hits including `AlgebraicGeometry.Scheme.Etale`,
  `AlgebraicGeometry.IsEtale`, and residue-point preimmersion declarations;
  none states this comparison.
- msearch grep: `trdeg|transcendence|schemePointMap` in `AlgebraicGeometry`
  returned zero hits. This wrapper result is supplemented by direct source
  searches rather than interpreted as absence of all relevant ingredients.
- Direct rg over `lean/WeilConjectures` and `lean/Sheaf` for
  `trdeg.*quasi|quasi.*trdeg|trdeg.*chart|chart.*trdeg` found only the scheme
  theorem `finite_residue_extension_trdeg_zero_of_quasiFinite` in
  `RegularLCIGeometricCalculus` and an unrelated chart proof comment.
  That scheme theorem assumes Noetherian schemes and gives relative
  transcendence degree zero, so it is not the current statement.
- Direct rg for residue-field transcendence degrees found the existing
  `residueFieldTrdeg` wrapper and closed-point criteria. The delivered
  statement uses the underlying recorded `Algebra.trdeg` directly.
- The required node-id grep in `lean/WeilConjectures` found no declaration.
  Searches in `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and
  `lean/Sheaf` found no collision for the chosen declaration name.

Validation: scompile.py compiled the delivered module in both sandbox and
library module contexts, with no errors or non-sorry warnings. The node's
`lean.statement` is extracted verbatim from the source signature. The
prescribed deliver2.py dry run and final delivery follow this report.

## Second reading by Q26

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
