## Worker report

States `AlgebraicGeometry.AlgebraicSpace.qcqs_source_of_finitePresentation` in
`Sheaf.AlgebraicGeometry.SpaceFinitePresentationQcqsSource`. Its only proof is `sorry`.
The node statement is unchanged. Its proof is reproduced in four steps in the docstring.
The source was read at `spaces-morphisms.tex`,
`lemma-finite-presentation-quasi-compact-quasi-separated` (Stacks Tag 06G5).

Clause-by-clause comparison:

- The arbitrary base scheme is `{S : Scheme.{u}}`. The size convention is rendered by
  explicit `universe u`, using exactly the recorded space and point constructions.
- Algebraic spaces over S are `{X Y : AlgebraicSpace S}`; the morphism is `(f : X ⟶ Y)`.
  These are the existing fppf sheaves with representable diagonals and etale atlases,
  with natural transformations as morphisms.
- The point topology is the existing `pointTopologicalSpace` on `Point Y.obj.obj`
  and `Point X.obj.obj`; it is final for representable etale scheme charts.
- Quasi-compactness of the target, meaning every open cover has a finite subcover,
  is `(hYqc : CompactSpace (Point Y.obj.obj))`.
- Absolute quasi-separatedness of Y is `(hYqs : IsAbsolutelyQuasiSeparated Y)`.
  This landed predicate tests compactness of `h_U ×_Y h_V` for every pair of affine
  S-schemes mapping to Y, the equivalent absolute-diagonal criterion of Tag 0AHR.
  It does not mean only quasi-separatedness relative to S.
- Quasi-compactness of f is `(hfqc : MapIsQuasiCompact f.hom.hom)`.
  Unfolding the existing definition gives exactly every affine scheme test and
  compactness of the point space of the actual presheaf fibre product.
- Quasi-separatedness of f is
  `(hfqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom))`.
  This is the canonical relative diagonal into the sheaf fibre product, evaluated
  on underlying presheaves; no representability of f is required.
- Local finite presentation on etale charts is
  `(hflfp : MapIsLocallyOfFinitePresentation f)`. Its existing definition tests
  Mathlib's `LocallyOfFinitePresentation` on every compatible pair of etale scheme charts.
  Thus all three components of the node's finite-presentation assumption are retained.
- The conclusion `CompactSpace (Point X.obj.obj) ∧ IsAbsolutelyQuasiSeparated X`
  gives both required source properties, with the identical meanings as for Y.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, and `Spec.map` (the latter two underlie affine tests).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and the scheme-test representability and etaleness predicates.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicGeometry.AlgebraicSpace.pointTopologicalSpace`; the imported
  `AlgebraicSpacePointClasses` supplies `Point` and `schemePointMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme` in the same namespace. These justify the
  canonical sheaf/presheaf pullbacks in the statement and proof.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, used by the chart predicate.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocally` and `MapIsLocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`.

The last three owning definition nodes were added to `stmt_deps`, as permitted for
landed notions. They are reused unchanged; no new definition or dependency module
is needed. The size-convention node is metatheoretic and has no module to import.

Available proof-dependency modules are imported plainly:
`AlgebraicSpacePointOpenCalculus` (`point_open_calculus`) and Mathlib's
`AffineScheme` / `Morphisms.QuasiSeparated` (`Scheme.compactSpace_of_isAffine`,
`quasiSeparatedSpace_of_isAffine`). The fibre-product module is already public
because it is also a statement dependency. The proof-only node
`lem-sfb-qc-space-affine-etale-atlas` has no Lean record or Mathlib match at the
read base, so no module is fabricated for it; its intended use remains in the proof
docstring. It is not needed to type the present statement.

Edge cases checked before writing: empty Y forces empty X on points and both
conclusions hold; empty X is permitted; an identity morphism recovers the assumed
qcqs properties; nonrepresentable f is permitted; arbitrary nonseparated or
non-quasi-separated S is permitted because the space predicate is absolute.
There is no nonemptiness assumption, chosen atlas, field-characteristic restriction,
index restriction, or additional universe equality. Local finite presentation is
retained even though the proof only uses quasi-compactness and quasi-separatedness.
No statement dispute or correction was found.

Searches (all remote queries made through msearch.py, recorded in searches.jsonl):

- LeanFinder: "A finite presentation morphism of algebraic spaces with quasi compact
  quasi separated target has quasi compact quasi separated source". Eight hits,
  including scheme `QuasiCompact.of_comp` and `quasiCompact_over_affine_iff`;
  none concerns algebraic spaces.
- Loogle: `"AlgebraicSpace", "QuasiCompact"`. Zero hits.
- Mathlib grep: `AlgebraicSpace|algebraic space`. Zero hits.
- LeanSearch: "Finite presentation morphisms of algebraic spaces over quasi compact
  quasi separated targets have quasi compact quasi separated sources". Eight hits,
  all scheme/ring properties; no exact algebraic-space statement.
- `rg` on the complete `lean/WeilConjectures` for
  `lem-sfb-space-fp-qcqs-source|AlgebraicSpace|algebraic space`: no hits.
- `rg` on `lean/Sheaf` for quasi-compact, quasi-separated, qcqs and
  finite-presentation source statements: found the three reusable predicates above,
  and consumers mentioning this node in proof docstrings, but no theorem stating it.
  Also checked `lem-sfb-space-qcqs-source-products`: it has no Lean record and states
  different permanence assertions, so it supplies no existing declaration of this item.

Validation: scompile.py compiled the delivered file both as its sandbox module and
as `Sheaf.AlgebraicGeometry.SpaceFinitePresentationQcqsSource`, cleanly (1.6 s and
1.7 s). No diagnostic commands, definitions with postponed data, or auto-implicit
variables are present. Delivery preflight is run separately through deliver2.py.

## Second reading by Q37

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
