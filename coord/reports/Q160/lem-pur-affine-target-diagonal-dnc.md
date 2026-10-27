## Worker report

Q160 states `lem-pur-affine-target-diagonal-dnc` in
`Sheaf.Paper.AffineTargetDiagonalDnc`, declaration
`WeilConjectures.PurityFiniteSetting.affineTargetDiagonalDnc`.
There is one postponed theorem, with `sorry`; every definition has real data.
The module's other six declarations are chart packaging and canonical-arrow/
normalization helpers belonging to this item, listed in `lean.declarations`.
The original statement, dependencies and proof are unchanged.

Source read: current blueprint main-20261015,
`sec-smooth-purity/sk-prop-sp-orientation/thm-pur-diagonal-dualizing-object.proof.md`,
Steps 1--2, together with the item's eight-step proof and dependency records.

Hypotheses and clauses:

- `P : PurityFiniteSetting.{u}` is exactly the finite coefficient datum: algebraic
  closure of a finite field, the distinct coefficient prime, finite coefficient
  extension, and positive quotient level. The fixed scalar realization uses
  `P.Coefficient` and the intrinsic realization uses `P.Ring`; these are the
  recorded coefficient objects, not a replacement ring.
- `X Y : Scheme.{u}`, their maps `aX aY` to `Spec P.field.k`, and the respective
  `LocallyOfFiniteType` and `QuasiCompact` instances express finite-type
  k-schemes. `hf : f ≫ aY = aX` expresses the k-morphism condition.
  `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f`, and
  `SmoothOfRelativeDimension d f`, with `d : ℕ`, are precisely the morphism
  hypotheses. There is no absolute separatedness instance on either aX or aY.
- `∃ S : Finset Y.affineOpens, (⨆ V ∈ S, V.1) = ⊤ ∧ ...` is the finite affine
  cover. `(...).appTop.hom.FiniteType` is finite generation of its coordinate
  algebra over the global functions of `Spec k` (canonically k by ΓSpecIso).
  Affine opens carry their canonical Spec-coordinate-ring identification.
- The universal quantifier over `V : Y.affineOpens` and the same ring-map finite
  type condition covers every affine open required by the statement.
  `X_V` is `(f ⁻¹ᵁ V.1).toScheme`, `j_V` its open inclusion, `f_V` is `f ∣_ V.1`.
  `isPullback_morphismRestrict` is the actual Cartesian square. The self-product,
  projections and diagonal are Mathlib's `pullback`, `pullback.fst`,
  `pullback.snd`, and `pullback.diagonal`.
- The existential `H : P.AffineDiagonalGeometry f aY d V` consists of conclusions,
  not additional hypotheses. Its source and product fields give separatedness,
  local finite type and quasi-compactness over k. Its first four fields give the
  separated finite-type smooth dimension-d restriction. The same properties of
  both projections follow by the existing base-change instances, with no
  extra assumption. The base finite-type fields make subsequent constructions
  type correctly over the actual affine base.
- `AffineDiagonalConclusion` first asserts invertibility of the specified open
  dualizing-complex base-change mate. `affineDiagonalRho` constructs rho as its
  `asIso`, preceded by the published pullback/site comparison. It invokes the
  smooth cohomological base-change theorem and obtains compactifications from
  the finite-type data; no arbitrary map is selected.
- Its next conjunct quantifies over every point of X_V, chooses an affine
  neighborhood of its diagonal image, and a list `r` of coordinate functions
  with `r.length = d`, `RingTheory.Sequence.IsRegular ... r`, and
  `Ideal.ofList r = Delta.ker.ideal U`. This is exactly local regularity and
  pure codimension d. The existing separatedness instance gives a closed
  immersion; it is not silently replaced by another embedding. The section
  identity is the existing `pullback.diagonal_fst`, supplied explicitly to all
  section-invariant and normal-section constructions.
- The relative differential sheaf has `IsFiniteLocallyFreeOfRank d`.
  The actual normal cone `Delta.ker.normalCone` is uniquely isomorphic to
  `RelativeTangentBundle.scheme f_V` with `AffineDiagonalTangentNormalized`.
  This predicate fixes projection and zero section and, on every local section,
  sends da to the degree-one class of p2*a-p1*a, using the existing symmetric
  algebra and normalized Rees comparison. Thus it specifies the canonical
  normal/tangent isomorphism, not a freely chosen bundle automorphism. Together
  these clauses assert the vector bundle of rank d. The normal projection and
  zero section are the recorded actual constructions.
- The next `IsIso` is the actual self-product dualizing base-change mate.
  `affineDiagonalAlpha` constructs alpha by `Dnc.sourceComparison` followed by
  the recorded `diagonalComparedRestriction`; this is the specified inverse
  mate, diagonal pullback and composition/identity chain.
- The `Nonempty` intrinsic comparison conjunct records only the equivalence of
  the two published coefficient realizations of the same section object. Its
  endpoints are the image of `Dnc.sourceSection` under the published
  `sfIntrinsicDerivedEquivalence` and the recorded `sectionInvariantFinite`.
  It is not used to select either canonical arrow or the normal bundle.
- The final `∃! δ` has the actual `Dnc.sourceSection` and `Dnc.normalSection`
  endpoints for `(p1, Delta)`, hence C(p1,Delta) and C(pi,z).
  `AffineDiagonalDncNormalized` is the full equation already printed in
  `Dnc.existsUnique_dncInvariance`, expressed as a named predicate for this
  conclusion: it quantifies over every separated finite-type k-base change,
  every object C0 and every base-pulled trivialization of the DNC family, and
  compares the specified fibre-one and fibre-zero readings through the
  published site comparisons. No pre-existing named predicate for this
  equation is duplicated. This is the dependency's normalization that gives
  identity in standard etale coordinates, including uniqueness.

Dependency declarations used (full names have their usual namespaces):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `Ring`, `Coefficient` and the coefficient exponent/unit facts.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `...QuasiCompact`: `QuasiCompact`; `...Proper` / `...Separated`: `IsSeparated`;
  `...Smooth`: `Smooth`, `SmoothOfRelativeDimension`; `...Etale`: `Etale`;
  `...ClosedImmersion`: `IsClosedImmersion`; `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `IsOpenImmersion`; `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback` and its projections/diagonal.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` imports the
  recorded coefficient system `ConstructibleExceptionalCoefficients.System`
  and fixed finite exceptional functor `ProEtale.sfFiniteExceptionalAt`;
  `Sheaf.Paper.DerivedPullbackTensorHom` provides `finiteDerivedPullback` and the
  actual finite coefficient operations. Their finite realization underlies
  the section-invariant declaration used here.
- `Sheaf.Paper.PuritySectionInvariantIntrinsic`:
  `PurityFiniteSetting.sectionInvariantFinite`, `intrinsicDualizing` and the
  published intrinsic coefficient realization.
- `Sheaf.Paper.PurityNormalProjection`:
  `Scheme.Hom.purityNormalProjection`, `purityNormalProjection_eq`, importing
  the actual normal cone, projection and zero-section constructions.
- `Mathlib.RingTheory.Regular.RegularSequence`:
  `RingTheory.Sequence.IsRegular`.
- `Sheaf.AlgebraicGeometry.RelativeTangentBundle`:
  `RelativeTangentBundle.scheme`, `projection`, `zeroSection`, `algebraIso`.
- `Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension`:
  `diagonal_isRegularImmersionOfPureCodimension`. Its current blueprint update
  treats positive codimension and no longer supplies a tangent conclusion.
  This item's local regular-sequence, d=0 and canonical tangent clauses are
  retained explicitly, rather than assumed from a stronger replacement
  dependency. The module is imported for the recorded proof plan.
- `Sheaf.Paper.CohomologicalSmoothnessTheorem`:
  `ProEtale.isCohomologicallySmooth_of_smooth` and the finite smooth exceptional
  base-change interface used to construct rho.
- `Sheaf.Paper.PurityDiagonalBaseChangeCompared`:
  `PurityFiniteSetting.comparedDiagonalBaseChange`,
  `PurityFiniteSetting.diagonalComparedRestriction`.
- `Sheaf.Paper.PurityDncInvariance`: `Dnc.existsUnique_dncInvariance`,
  `pullComparison`, `sourceComparison`, `normalComparison`, and the actual
  family/source/normal objects from its public imports.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, its map and zero/one
  sections. `Sheaf.AlgebraicGeometry.ReesConeNormalizedExistence` supplies the
  imported canonical Rees normalization interface used to characterize the
  normal/tangent arrow.
- The proof-only permanence leaves use the recorded Mathlib composition and
  base-change instances for separatedness, local finite type, quasi-compactness
  and smooth relative dimension, `locallyOfFiniteType_iff` / `finiteType_appLE`,
  and `IsAffineHom` / `IsSeparated.of_isAffineHom`. These are available through
  the listed imports; no private permanence predicates were written.

Edge cases checked: empty Y permits `S = ∅`; empty X makes pointwise diagonal
assertions vacuous but retains actual empty objects and morphisms. No nonempty
hypothesis is imposed. `d = 0` permits the empty regular sequence on a neighborhood
of each diagonal point; the condition is deliberately not imposed on affine opens
away from the diagonal. The normal/tangent object then has rank zero. Identity
morphisms and arbitrary base-change maps occur in the DNC normalization, including
the identity trivialization. Nonseparated X or Y (e.g. identity of the doubled
origin) are permitted; absolute separatedness is only concluded after restricting
to affine V. All coefficient levels n >= 1 remain, with no divisibility condition.
All universe and variable binders are explicit and `autoImplicit` is disabled.

Searches (the raw launcher results are in sandbox `searches.jsonl`):

- msearch leanfinder: “Affine target restriction of smooth separated finite type
  morphism diagonal section invariant normalized deformation to normal cone
  isomorphism”: eight unrelated normalization results, no exact statement.
- msearch loogle: `AlgebraicGeometry.IsRegularImmersion,
  CategoryTheory.Limits.pullback.diagonal`: zero results (the first name is not
  a Mathlib declaration).
- msearch grep: `affineTargetDiagonal|affine.*[Dd]iagonal|dncInvariance`:
  thirteen ordinary affine-diagonal hits, no finite DNC affine-target theorem.
- msearch leansearch: “The diagonal of a smooth separated scheme morphism has a
  tangent normal bundle and canonical normalized deformation to normal cone
  section comparison”: eight ordinary geometric results, including closedness
  of a separated diagonal, no exact combined statement.
- rg in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for the item id and proposed declaration names: no existing exact declaration.
  The broader normal/tangent search found the upstream conormal-differential
  interface and downstream `DiagonalDncChartNormalization`; the latter is a
  chart normalization consumer, not this affine-target domain theorem, and is
  not imported. Existing canonical objects and comparison maps are reused.

Validation: scompile.py compiled the final declaration module against the live
server library without errors or unexpected warnings. Only its main theorem
is postponed. The dry-run and delivery results follow in the launcher output.
No node correction, disputed statement or new independent definition node is needed.

## Second reading by Q160

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
