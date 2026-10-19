## Worker report

The module `Sheaf.TraceFormula.ProperGeometricSpecializationLift` defines the set-valued
étale inverse-image functor `etaleSetInverseImage` and states
`AlgebraicGeometry.exists_proper_geometric_specialization_lift` with proof `sorry`.
The hypotheses are a proper surjective scheme morphism `p`, algebraically closed endpoint
fields and geometric points `s,t`, and the inverse-image mate `c` of the prescribed
2-morphism. The conclusion gives algebraically closed field extensions, maps `rs,rt`,
geometric points `s',t'` over `T`, a lifted stalk natural transformation `c'`, the two
commuting endpoint triangles, and comparison isomorphisms `is,it` whose composite sends
`c'` to `c` on every set sheaf.

The properness and surjectivity hypotheses use Mathlib `AlgebraicGeometry.IsProper` and
`AlgebraicGeometry.Surjective`. Geometric points and the small étale sites use
`Scheme.pointSmallEtale`, `Scheme.Etale`, and `Scheme.smallEtaleTopology`. The geometric
morphism and stalk-morphism dependencies are imported from
`Sheaf.CategoryTheory.Sites.GeometricMorphism` and
`WeilConjectures.AlgebraicGeometry.GeometricPointMorphismStalkBijection`; the latter
supplies the canonical stalk transport used in the proof plan. The oriented-product
convention is represented by the direction of `c` as an inverse-image mate.

Edge cases checked: identity endpoint extensions, equal endpoint points, empty schemes
(where the hypotheses are vacuous), and arbitrary universe level `u`; no finiteness or
Noetherian hypothesis is introduced. The category of set-valued sheaves is used directly,
so no additive or coefficient assumption is added.

Searches recorded in the node were rerun: LeanFinder on proper-surjective geometric
specialization lifting (only Zariski-specialization results), Loogle on
`AlgebraicGeometry.IsProper, Specializes` (no hits), LeanSearch on lifting arrows of
geometric étale points (only generic surjectivity declarations), and grep in Mathlib
`AlgebraicGeometry/ValuativeCriterion.lean` for specialization/geometric-point names
(Zariski-only declarations). No exact existing theorem was found.

## Second reading by Q50

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer fix (maintainer review, 2026-10-18)

- The delivered last clause quantified the comparison isomorphisms `is, it` existentially. With
  arbitrary isomorphisms, any automorphism of a stalk functor (e.g. a Galois twist) can absorb
  the prescribed arrow, so the statement no longer says that `p c'` is exactly `c` under the
  canonical isomorphisms furnished by the field extensions. The fixed module states the equation
  with canonical data: `geometricPointMorphismSheafFiber` (the stalk map of a morphism of
  geometric points, Stacks 04FN, Mathlib `GrothendieckTopology.Point.Hom.sheafFiber`; bijective by
  `Scheme.geometricPointMorphism_stalk_bijection`) and `etaleSetPullbackSheafFiberIso` (the
  inverse-image stalk identification, Stacks 03Q1, the composite already used in
  `etaleSetInverseImageStalkGerm`). Since the stalk maps of `rs`, `rt` are bijective, the
  equation `c ≫ rt^* = rs^* ≫ (p^{-1}-stalk iso)^{-1} ≫ p^{-1}c' ≫ (p^{-1}-stalk iso)` is the
  node's clause.
- The endpoint equations are now Prop binders `hs : rs ≫ s = s' ≫ p`, `ht : rt ≫ t = t' ≫ p`
  (the node's `p s' = s r_s`, `p t' = t r_t`), used by the stalk maps.
- The local `etaleSetInverseImage` duplicated `AlgebraicGeometry.Scheme.etaleSetPullback`
  (WeilConjectures.AlgebraicGeometry.EtaleSheaves, the same `sheafPullbackConstruction`
  definition); it is removed and the existing functor used (one definition per notion).
- Compiled with nt_compile.py: rc 0, no error, no warning other than the `sorry`.
