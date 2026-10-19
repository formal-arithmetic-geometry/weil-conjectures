## Worker report

The module `Sheaf.Paper.OrdinaryCompletedIntegralPullback` states
`WeilConjectures.ordinaryCompletedIntegralPullback`, with `sorry`. It also supplies the
canonical ordinary ringed pullback and the comparison that the item itself introduces.
These are helpers of this item's specified construction; no independent notion or new
DAG node is introduced. Every helper theorem has `sorry`, a source, the item's blueprint
identifier and a proof plan. Definitions contain actual data. The only choices are a
uniquely projection-normalized ring map, adjoint/derived universal constructions, and
uniquely generator-normalized maps. No endpoint isomorphism or arbitrary cone lift is
chosen.

The statement and every other original node field are unchanged. The added Lean record
lists every declaration in the module. There is no statement dispute or correction.

Clause-by-clause reading:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The recorded coefficient-extension
  constructions provide its valuation ring, chosen uniformizer, quotient at exponent
  `n+1`, and reduction homomorphism. Thus `n : ℕ` covers exactly the positive exponents.
- `X Y : Scheme.{u}` and `f : X ⟶ Y` introduce arbitrary schemes and their morphism.
  `[IsNoetherian X] [IsNoetherian Y]` mean locally noetherian and quasi-compact: Mathlib's
  class extends `IsLocallyNoetherian` and `CompactSpace`. No separatedness, finite-type
  morphism, flatness, or field-linearity assumption is made.
- `_hXdim`, `_hYdim` assert `∃ n : ℕ, topologicalKrullDim _ ≤ n`. The latter dimension
  is the supremum of lengths of strict chains of nonempty irreducible closed subsets,
  exactly the item's convention. `_hXinv`, `_hYinv` say `IsUnit (l : Γ(_, ⊤))`.
  Invertibility in the structure sheaf is equivalent to invertibility of its global
  integer section: local inverses glue uniquely. This applies also to the empty scheme.
- The small site is the recorded `Scheme.ProEt` with `ProEt.topology`. In the arbitrary
  common ambient universe `u`, site objects have size `u+1`, morphisms size `u`, and
  coefficient/module sections size `u+1`. These are the recorded detailed-category
  universes; the site object and morphism universes have not been identified.
- `completedIntegralCoefficientSheafUnrestricted l E W` is exactly `B_W`, the existing
  limit of `integralCoefficientSheafSystem`. No second completed coefficient ring is
  constructed. `integralTowerModules l E W` is the existing `SheafOfModules B_W`.
  `DerivedCategory` is its ordinary unbounded localization at quasi-isomorphisms with
  the existing standard derived-category instance.
- `ordinaryIntegralFiniteDirectRingMap` is the existing constant-section ring map,
  forgetting commutativity only. `ordinaryIntegralDirectRingMap_existsUnique` fixes its
  completed lift `ρ : B_Y ⟶ f_* B_X` by
  `ρ ≫ f_*(π_n) = π_n ≫ ρ_n` for EVERY positive exponent. Taking its ring-adjunction
  transpose is exactly the item's `c_f`, since transposition takes this equation to
  `c_f ≫ π_n = f⁻¹(π_n) ≫ c_n`. No isomorphism of completed coefficient sheaves is
  assumed.
- `ordinaryIntegralModulePush` is Mathlib's sectionwise pushforward along that ring
  map. `ordinaryIntegralModulePull` specializes Mathlib's `SheafOfModules.pullback`,
  with its `pullbackPushforwardAdjunction`; thus it is the sheafified module Kan
  extension, equivalently `B_X ⊗_(f⁻¹ B_Y) f⁻¹(-)`. The named existence theorem gives
  the required universal adjoint, not a chosen arbitrary functor. Transport through the
  recorded small models supplies the adjunction without changing site universes.
- `ordinaryIntegralDerivedPull` uses Mathlib's `totalLeftDerived` and its canonical
  counit. `ordinaryIntegralPullComplexCounit` includes all cochain/homotopy localization
  comparisons. Its named `isIso` assertion applies to the existing
  `integralOperationsGoodComplex`, i.e. precisely K-flat complexes with flat terms.
  This supplies the canonical K-flat identification required for `P_f`.
- The hypothesis `hK : sfIntegralConstructible l E Y K` is the recorded detailed
  `D^b_c(Y,R)`: derived completeness, constructibility at EVERY positive reduction,
  and one finite cohomological interval independent of the exponent. The first
  conjunct of the theorem applies that same predicate to the ORDINARY pullback.
- The completed endpoint is the existing `integralDerivedPullback l E f` from
  `IntegralDerivedOperations`, publicly retained by its recorded `OnSlices` module.
  It is the normalized descent of the STRICT finite-pullback tower followed by Roos.
- `ordinaryIntegralQuotientAugmentation_existsUnique` specifies a natural map of strict
  towers. On EVERY cochain complex, degree, positive exponent, base-change test object
  and local input section it sends the ordinary adjunction-unit generator to
  `integralOperationsPullbackGenerator ... (unrestrictedIntegralTensorSection ... 1 x)`.
  In tensor notation this is `1 ⊗ q ↦ 1 ⊗ (q ⊗ 1)`. Completed linearity gives the
  required formula for `b ⊗ q`, with coefficient `π_n(b)`. Restrictions of these unit
  generators and their scalar multiples generate the inverse-image tensor sheaf on
  every test object, so this specifies the whole map, not only base-change objects.
  Its target is the EXISTING `integralOperationsPullbackTowerFunctor`, hence its
  transitions are the actual quotient transitions, not arbitrary identifications.
- `ordinaryIntegralProductAugmentation` takes the actual product of these maps.
  `ordinaryIntegralCompletionChain_condition` expresses their composite with `1-s`
  being zero, with the zero degree-minus-one cochain. `ordinaryIntegralCompletionChain`
  uses `CochainComplex.mappingCocone.lift` with that product map and literal `0`.
  Therefore the unshifted cone coordinate is exactly the quotient product and the
  shifted coordinate is zero. Its target is the existing Roos model.
- `ordinaryIntegralCompletionComparison_existsUnique` fixes a natural transformation
  `η : ordinaryIntegralDerivedPull ... ⟶ integralDerivedPullback ...` by its equality
  with that chain map after the two CANONICAL representative computation maps.
  `ordinaryIntegralCompletionComparison` chooses this uniquely specified transformation.
  The theorem's second conjunct is `IsIso (η.app K)` for this very map.
- Naturality is encoded by `η` being a natural transformation, whose component square
  holds for every derived morphism. The normalization holds for EVERY good
  representative, not a single chosen resolution. For a quasi-isomorphism `Q → A`,
  compose with the inverse of its image under the two derived functors; the counit
  and representative-comparison naturality give the item's canonical resolution
  identifications. These images are isomorphisms. The normalization equation hence
  proves that any resolution gives the SAME `η.app K` under those comparisons,
  including comparison zigzags. This retains the identity and arbitrary-resolution cases.

Dependency declarations read and used (recorded modules, including their public exports):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; its imported `CoefficientExtension` supplies
  `coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionRing`, and `coefficientExtensionTransition`.
- `def-weil-scheme-morphism-properties` is a convention node, not a declaration.
  `Mathlib.AlgebraicGeometry.Noetherian` supplies `IsLocallyNoetherian`, `IsNoetherian`;
  `Mathlib.Topology.KrullDimension` supplies `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: reexports
  `completedIntegralCoefficientSheafUnrestricted`, `integralCoefficientSheafSystem`,
  its limit projections and the coefficient-universe constructions unchanged.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleBaseChange`,
  `proEtaleSheafDirectImage`, ring inverse image and adjunction. Its public companion
  `ProEtaleCoefficientPullbackUniverses`, already used by the finite tower, supplies
  `coefficientProEtaleDirectRingMap`.
- `Sheaf.Paper.RingedTopoiDerivedPullback`: `SheafOfModules.ringedTopoiDerivedPullback`.
  It is the general resolving-class input: apply it on the common small models and
  transport the universal derived pair back. The helper existence/computation theorems
  are the specialization to this item's canonical ring map. They do not impose equality
  of object and morphism universes on the original sites.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices` publicly retains
  `IntegralDerivedOperations`: `integralDerivedPullback`,
  `integralDerivedPullbackComparison`. The retained `IntegralOperationsWellDefined`
  supplies the exact finite tower, its transitions, good representatives, generators,
  and the strict Roos functor; none is copied.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`, `Qh`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, the transparent
  specialization of Mathlib's existing `SheafOfModules`.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.

Every stated proof dependency is imported, including the stratified-perfect
characterization, immersion and slice restrictions, composition/tensor comparisons,
K-flat pullback, coefficient DVR facts, Koszul reconstruction, and finite constant
exactness. The Mathlib leaf `lem-weil-valued-dvr-finite-quotients` has no Lean record;
its `Valued.integer.finite_quotient_maximalIdeal_pow_of_finite_residueField` match is
provided by the imported `Mathlib.Topology.Algebra.Valued.LocallyCompact`.

Edge cases checked: empty X or Y (dimension is bottom; no nonemptiness binder), zero
complexes, the identity morphism, nonflat and nonseparated morphisms, maps without any
base-field structure, every positive quotient including exponent one, all integer
degrees and unbounded flat-term K-flat resolutions. There is no bound on the chosen
resolution, and the uniform interval belongs only to the recorded constructibility
predicate. Finite dimension and invertibility are assumed on BOTH schemes as written.

Searches for an existing statement, performed with msearch.py and recorded in the
sandbox `searches.jsonl`:

- LeanFinder: "canonical ordinary derived pullback to completed pullback is an
  isomorphism on bounded constructible integral sheaves". Eight hits about ordinary
  sheaf pullback, sheafification and free modules; no derived completion theorem.
- Loogle: `SheafOfModules.pullback`. Twelve hits. Read `PullbackContinuous.lean`:
  this supplies the ordinary module pullback and adjunction used here, not the
  constructible completed comparison.
- Mathlib grep: `completedPullback|derivedComplete`. No hits.
- LeanSearch: "ordinary derived pullback of constructible completed integral
  coefficient sheaves is complete". Eight ordinary pullback/free-module hits;
  no exact statement.
- `rg` in upstream `WeilConjectures`, side `lean/Sheaf`, and the upstream name index:
  no occurrence of the proposed declaration names or this item's blueprint id.
  Concept searches found generic completed towers, their comparisons and scalar
  extension constructions. They supply the reused infrastructure, but none states
  this noetherian constructible theorem for the detailed coefficient category and
  specified quotient-zero cone map. In particular `proEtaleRingModulePullback`
  requires an ISOMORPHISM of inverse-image coefficient rings; this item's canonical
  map is arbitrary and is not silently replaced by that stronger hypothesis.

The supplied Bhatt--Scholze PDF was read at Lemma 6.5.9, Proposition 6.6.11 and
Remark 6.8.15. The strict comparison normalization is the agent formulation explicitly
identified in the node's source, consistent with Stacks 06YY and 08TC. Those Stacks
passages, together with 0G7E and 099M, were also read in the local source tree.

Validation: the module compiled cleanly using the prescribed scompile.py wrapper
before packaging; only the expected sorry declarations are postponed. The final
preflight result is recorded below after the dry run.

Dry run: `deliver2.py Q147 lem-tw-ordinary-completed-integral-pullback --no-push`
printed `OK (dry run): commit 30d7b7fab0 passes the preflight and compiles; nothing pushed`.
It staged exactly the module, the item's node record, and this worker report.

## Second reading by Q147

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
