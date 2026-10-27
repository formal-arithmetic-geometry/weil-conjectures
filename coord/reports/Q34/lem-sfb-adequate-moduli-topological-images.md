## Worker report

The module `Sheaf.AlgebraicGeometry.AdequateModuliTopologicalImages` states
`CategoryTheory.adequate_moduli_topological_images`, with its sole proof `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
The item's original fields are preserved; only `lean` is set.

The mathematical source is Alper, *Adequate moduli spaces and geometrically reductive
group schemes*, arXiv:1005.2398v3, Theorem 5.3.1(1), (2), (4), printed pp. 29--30.
Read the primary PDF at https://arxiv.org/pdf/1005.2398, theorem on PDF page 29.
It asserts surjectivity, universal closedness, and equality of the set-theoretic
intersection of images with the image of the intersection of closed substacks.
Those are precisely this node's three clauses. The module docstring records the
node's scheme-chart descent and disjoint-quotient power-lifting proof, step by step.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`, using Mathlib's `Field` from
  `Mathlib.Algebra.Field.Defs` (the `def-weil-field` Mathlib match).
- The algebraic stack over k is
  `(F : BasedCategory.{v, w} (Over (Spec (.of k))))`
  with `(hF : IsAlgebraicModuliStack F)`. The two category universes `v`, `w`
  are independent; all universes and binders are explicit, with `autoImplicit false`.
- The algebraic space over k is `(Y : AlgebraicSpace (Spec (.of k)))`.
- The actual stack morphism to Y is
  `(φ : BasedFunctor F (discreteModuli Y.obj.obj))`.
- Adequacy is exactly `(hφ : IsAdequateModuliSpace F hF Y φ)`, reusing the
  recorded predicate including qcqs, the canonical structure-sheaf isomorphism,
  and power lifting on every affine etale chart; no extra hypothesis is imposed.
- Underlying point sets are the recorded `ModuliPoints`; all maps are
  `moduliPointMap` of the actual functor. Their field-object quotient is not replaced.
- The first conjunct `Function.Surjective (moduliPointMap φ)` states surjectivity
  of the underlying map to the point set of the discrete stack associated with Y.
- The second conjunct quantifies over every
  `(T : AlgebraicSpace (Spec (.of k))) (t : T ⟶ Y)`.
  `discreteModuliMap t.hom.hom` is the induced functor of discrete stacks.
  `moduliTwoFiberProduct φ (discreteModuliMap t.hom.hom)` is the actual 2-fibre
  product, with projection `moduliTwoFiberSnd φ (discreteModuliMap t.hom.hom)`.
  `Continuous` and `IsClosedMap` are each supplied explicitly with
  `moduliSmoothPointTopology` on that product and on `discreteModuli T.obj.obj`.
  Thus the continuous map in the node is closed for every space base change.
  Using the discrete-stack point space for T and Y is exactly the point/topology
  convention of the statement dependency, not a replacement by a chosen atlas.
- The last conjunct quantifies over both `Z₁ Z₂ : ClosedModuliSubstack F`, not just
  reduced substacks. `Set.range (moduliPointMap Zᵢ.inclusion)` is its underlying
  subset of the stack. Its image by `moduliPointMap φ` gives each left-hand image;
  `∩` is their set-theoretic intersection in the point set of Y.
  On the right, `moduliTwoFiberFst Z₁.inclusion Z₂.inclusion` projects their actual
  2-fibre product to Z₁; composition with `Z₁.inclusion` is the map to F. The range
  of its point map, followed by image under φ, is exactly the node's right side.
- There is no finite-type, reducedness, characteristic-zero, or finite-inertia binder.
  The only structural hypotheses are the field, algebraic stack, algebraic space,
  morphism, and adequate-moduli property specified in the node.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AdequateModuliSpace`,
  `CategoryTheory.IsAdequateModuliSpace`: exact recorded definition, read in full.
- `Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets`,
  `CategoryTheory.moduliSmoothPointTopology` and
  `CategoryTheory.smooth_presentation_closed_subsets`: exact recorded smooth-atlas
  topology and theorem, read with signatures and proof docstring.
- Through those public imports, the existing `IsAlgebraicModuliStack`,
  `AlgebraicSpace`, `BasedCategory`, `BasedFunctor`, `discreteModuli`,
  `discreteModuliMap`, `moduliTwoFiberProduct`, `moduliTwoFiberFst`,
  `moduliTwoFiberSnd`, `ModuliPoints`, `moduliPointMap`,
  `ClosedModuliSubstack`, and its `inclusion` and `category` are reused.
  Relevant sources read: AlgebraicModuliStack, AlgebraicSpace,
  StablePointedModuliGroupoids, OpenModuliSubstack, DmStackMorphismProperties,
  ClosedModuliSubstack, and StackPointTopologyFlatLfpOpen.
- Of the proof dependencies, AdequateModuliSpace, SmoothPresentationClosedSubsets,
  and StackQuasiCoherentAlgebra are already in the public import closure.
  `lem-sfb-adequate-moduli-universal-closed-topology`,
  `lem-sfb-disjoint-closed-substacks-algebra-quotient`, and
  `lem-sfb-algebraic-stack-fibre-products` have no recorded Lean declarations yet;
  there are no modules for those proof-only dependencies to import. Their
  mathematical steps remain named in the theorem docstring. None is needed as
  a missing notion to formulate this statement.

Edge cases checked before writing:

- The empty target permits only an empty source point set; surjectivity is the
  ordinary empty-to-empty assertion. No nonemptiness assumption excludes it.
- Empty algebraic-space base changes are included and their maps are closed.
- Empty closed substacks give empty images and empty intersection; the full
  substack and repeated closed substacks give the corresponding identity cases.
- Arbitrary nonreduced closed substacks are retained; the conclusion concerns
  their supports, without asserting scheme-theoretic equality of images.
- All characteristics are admitted, and arbitrary, nonflat, nonreduced,
  non-finite-type space base changes are quantified over. Adequacy is not asserted
  for those base changes; only the stated topological properties are concluded.
- Point and category universes follow the existing site conventions; no equality
  between independent category universes is imposed.

Searches for an existing statement (all on 2026-10-24):

- `msearch.py leanfinder`: "An adequate moduli space of an algebraic stack is
  surjective universally closed and preserves intersections of images of closed
  substacks". Eight hits, including `Scheme.IsJointlySurjectivePreserving`,
  `IsProper`, `descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`,
  `universallyClosed_isZariskiLocalAtTarget`, `isProper_eq`, `UniversallyClosed`,
  and `Surjective`; these are scheme assertions or definitions, no adequate-moduli
  theorem.
- `msearch.py leansearch`: "An adequate moduli space of an algebraic stack is
  universally closed and surjective". Eight scheme hits: surjectivity from
  universal closedness and dominance, `UniversallyClosed` and its constructor,
  composition lemmas, properness implication, `universallyClosed_eq`, and
  `Scheme.Hom.isClosedMap`; no adequate-moduli statement.
- `msearch.py loogle`: `"AlgebraicGeometry", "adequate"`. Zero hits.
- `msearch.py grep`: `adequateModuli|adequate_moduli|geometrically.?reductive`
  under Mathlib `AlgebraicGeometry`. Zero hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf`, and the upstream name index,
  for `AdequateModuli|adequate_moduli|adequateModuli`: the predicate in
  AdequateModuliSpace and an adequacy-of-direct-image notion in
  AdequatelyAffineMorphism, plus the import in FiniteFlatAffineGroupoidModuli.
  No topological-image theorem.
- Search for the node id in `lean/WeilConjectures`: no matches.
- Search for both proposed theorem name forms in Mathlib, `lean/WeilConjectures`,
  and `lean/Sheaf`: no matches, so no declaration collision.

Validation: `scompile.py Q34 lem-sfb-adequate-moduli-topological-images` compiled
both its sandbox form and final library module against the live server build,
without errors or warnings (16.2 s and 11.3 s respectively). Delivery dry-run and
final delivery are run after assembling this report and the lean-only node record.
No statement dispute or node fault was found.

## Second reading by Q34

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
