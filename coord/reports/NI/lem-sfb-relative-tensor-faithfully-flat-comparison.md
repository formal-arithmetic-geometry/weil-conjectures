## Worker report

The module states `DerivedCategory.relative_tensor_faithfully_flat_comparison`, with one
whole-proof `sorry` and no new definitions. Source read: Stacks More on Algebra,
`lemma-no-change-tor-amplitude` (Tag 0DJF), including its total-tensor proof. The node's
statement is unchanged. Its statement dependencies gain the already recorded
`def-pc-mixed-total-tensor`, whose public upstream construction is used directly.
No new nodes, dependency repairs, or statement disputes.

Clause-by-clause correspondence:

- Commutative rings and maps R → A → B: `(R A B : Type u)`, three `CommRing`
  instances, the three `Algebra` instances and `IsScalarTower R A B`.
  The R-action on B is their composite; its compatibility is data already implicit
  in writing the composite R → A → B, not a further mathematical restriction.
- Faithfully flat A → B: `[Module.FaithfullyFlat A B]`, exactly the recorded
  definition and the STATE convention. No R-flatness assumption is present.
- Unbounded derived categories: `DerivedCategory (ModuleCat.{u} R/A/B)` with
  explicitly bound independent localization universes `wR`, `wA`, `wB` and their
  `HasDerivedCategory` instances. All complexes have integer degrees and there are
  no boundedness assumptions. Rings and module carriers live in the same chosen
  ambient universe `u`; this universe may be enlarged to contain all rings and
  test modules. The test-module universe is never independent or smaller than R.
- Exact termwise extension: `PreservesFiniteLimits (ModuleCat.extendScalars
  (algebraMap A B))`; the ordinary extension functor is already a left adjoint,
  hence preserves finite colimits. Thus this says it is exact.
- Every representing A-complex computes derived extension: the existential `L`,
  its natural counit `ε : Q ⋙ L ⟶ extendScalars.mapHomologicalComplex _ ⋙ Q`,
  `L.IsLeftDerivedFunctor ε ...` and `IsIso ε`. Each component identifies
  `L(Q(C))` with `Q(B tensor_A C)` for every C, without a K-flat condition on C.
  Hence for every isomorphism Q(C) ≅ K this also computes L(K).
- `K tensor_R^L N` with the A-action through K: `TA : D(A) ⥤ D(R) ⥤ D(A)`
  with natural counit `εA` to the existing `ModuleCat.mixedTotalTensor` followed
  by Q. The latter is literally `M tensor_A (A tensor_R E)` on coefficient modules,
  not the R-derived tensor with its coefficient action forgotten. For each
  coefficient complex C, `Functor.bifunctorCounit₁ εA C` is required to be a
  universal left-derived counit in the R-complex variable. Its component is
  invertible for every R-K-flat F, with the recorded `.kFlat` predicate.
  This determines the mixed derived functor up to the unique counit-compatible
  isomorphism, rather than choosing an arbitrary functor. The identical clauses
  for TB and εB use B-coefficients. Signed symmetry relates this orientation to
  the flipped second-factor API in the proof dependency.
- Degree-zero modules: the second variable is restricted through the existing
  `singleFunctor (ModuleCat.{u} R) 0`.
- Comparison in D(B), natural in all K and all R-module maps: `Nonempty` of a
  natural isomorphism of curried bifunctors. Its source is TA postcomposed with L,
  and its target is L followed by TB. Both are precomposed in the R-variable with
  the degree-zero single functor. Thus its component is precisely
  `L(TA(K,N[0])) ≅ TB(L(K),N[0])`, and functor-category naturality includes
  arbitrary derived morphisms K → K' and every module map N → N'. This is an
  isomorphism of derived objects, with no replacement by per-degree assertions.
- Every interval a ≤ b: the final clause binds `(a b : ℤ)`, `a ≤ b`, and every
  `K : DerivedCategory (ModuleCat A)`. Its two sides universally quantify over
  `N : ModuleCat R` and `i : ℤ` with `i < a ∨ b < i` and assert `IsZero` of
  the appropriate derived cohomology object. The connective is `↔`. These are
  exactly the node's two relative Tor-amplitude conditions. Computing cohomology
  in A- or B-modules retains useful scalars; forgetting to R preserves and
  reflects zero underlying modules, so this is the stated restriction to R.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.singleFunctor`.
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` supplies
  `DerivedCategory.homologyFunctor` and its localization comparison.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat` (publicly reexported
  by the imported `...Abelian.Flat.KFlat`): `CategoryTheory.MorphismProperty.kFlat`.
  This is the recorded ordinary-module K-flat predicate, not a private copy.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat` and
  `Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality`.
- `WeilConjectures.Algebra.Homology.MixedTotalTensor`:
  `ModuleCat.mixedTensor`, `ModuleCat.mixedTotalTensor`; direct public import.
- Proof imports retain all recorded, available proof dependencies:
  `CategoryTheory.Functor.homologyFunctorIso` from
  `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`;
  `CochainComplex.exists_quasiIso_flat_kFlat` from
  `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`;
  `DerivedCategory.exists_derivedTensor_second_factor_functor` from
  `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`;
  `CochainComplex.exists_mixedTensor_restriction_iso` from
  `WeilConjectures.Algebra.Homology.MixedTensorRestrictionComparison`;
  `RingTensorCohomology.exists_mixedTotalTensor_scalarExtension` from
  `WeilConjectures.Algebra.Homology.MixedTotalTensorScalarExtension`;
  `CochainComplex.mixedTensor_kFlat_quasiIso` from
  `WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso`;
  `CategoryTheory.Localization.lift`, `fac`, `liftNatTrans`, `liftNatIso` from
  `Mathlib.CategoryTheory.Localization.Predicate`.
  The faithfully-flat tensor-zero leaf is in the already imported Basic module.
- `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedTwo` supplies
  the existing `whiskeringLeft₂` and `Functor.bifunctorCounit₁` interfaces.
  ModuleCat's Abelian and closed monoidal imports expose the instances needed
  by the statement in module mode.

Edge cases checked mathematically before writing: K = 0 and N = 0; the zero
ring (allowed; no `Nontrivial`); A = B and identity extension; negative a and b;
a = b; cohomology at endpoints is allowed and outside is excluded by strict
inequalities; genuinely unbounded C and R-K-flat F; A not flat over R (for example
R = ℤ, A = ℤ/2, B = A). None is removed by a hypothesis. There is no assumption
of A-K-flatness on a representative C and no assumption of R-K-flatness on K.
No hollow definition, arbitrary map, resolution choice, or new instance is added.

Searches (all performed for this item with msearch.py):

- LeanFinder: `Unbounded relative derived tensor over R commutes with faithfully
  flat extension of an A coefficient algebra to B and detects Tor amplitude`:
  8 hits, headed by `Module.FaithfullyFlat.rTensor_reflects_exact`,
  `lTensor_reflects_exact`, and `rTensor_exact_iff_exact`; ordinary exactness only.
- Loogle: `"FaithfullyFlat", "Tor"`: 0 hits.
- Mathlib grep: `(FaithfullyFlat|faithfullyFlat).*(Tor|amplitude)|
  (Tor|amplitude).*(FaithfullyFlat|faithfullyFlat)`: 0 hits.
- LeanSearch: `Relative derived tensor over R commutes with faithfully flat
  extension of coefficient algebras`: 8 hits, ordinary faithful-flat tensor
  exactness and flatness descent; no unbounded derived comparison.
- `rg` on project and upstream sources for `derivedTensor`, `mixedDerived`,
  mixed derived tensors, `TorAmplitude`, `torAmplitude`, `derivedExtend`:
  found and read the existing mixed total tensor, the fixed-second-factor
  derived tensor, scalar-extension chain comparison, generic `torAmplitudeIn`,
  and `ModuleCat.derivedExtendScalars`. The last is flat scalar extension only;
  `torAmplitudeIn` concerns a single ring's derived tensor. Neither states the
  relative coefficient-algebra result. The existing mixed construction is reused.
- `grep -rn` for this node id in `lean/WeilConjectures`: no match.
  `rg` of `dag/lean_names_upstream.json` for the node id: no match.
  `rg` for `relative_tensor_faithfully_flat_comparison`, `relativeTensorModules`,
  `mixedTensorToDerived` throughout Mathlib and both source roots: no match.

Validation: scompile.py compiled both the sandbox probe and the actual library
module against the published live build with exit 0 and no warnings. Only the
item's authorized sandbox was edited. The theorem is deliberately unproved.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
