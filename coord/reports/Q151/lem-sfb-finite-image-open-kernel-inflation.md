## Worker report

Group Q151, stage 2, 2026-10-22. The delivery states
`Profinite.CondensedAction.PrimeToEll.finite_image_open_kernel_inflation` in
`Sheaf.Paper.FiniteImageOpenKernelInflation`. Its only postponed proof is this theorem's
`sorry`. The three helper definitions package precisely its image identification,
canonical augmentation, and coefficientwise conclusions. They contain real terms and
no postponed data. No statement correction, new node or dependency repair is needed.

The interrupted sandbox held an uncompiled draft and search log, but no node record,
report or delivery. I checked that no compile or delivery process for this item remained
before resuming. The draft's duplicate kernel constructors were removed in favor of the
already landed `normalKernel`, `normalProjection`, and `normalKernelInclusion`.

Hypotheses and clauses, with the node and source open:

- A prime ell is `(ell : ℕ) [Fact ell.Prime]`; the coefficient field is `ℚ_[ell]`.
  The algebraic closure with its extended norm is `(Ω : Type u) [NormedField Ω]
  [NormedAlgebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]`. There is no completeness
  hypothesis on Ω and no completion in any object or arrow.
- A finite intermediate field is `(E : IntermediateField ℚ_[ell] Ω)
  [FiniteDimensional ℚ_[ell] E]`. Its inherited norm and algebra map to Ω are used.
- The groups are `(B L : ProfiniteGrp.{u})`. `_hB` quantifies over every finite
  discrete group H, every continuous homomorphism `B →ₜ* H`, and surjectivity;
  `Nat.Coprime (Nat.card H) ell` is exactly the prime-to-ell quotient condition.
  Every finite quotient can be represented in this universe; H need not initially
  have any preferred enumeration, since a finite type admits Fintype.
- The vector space is `(V : Type (u + 1)) [NormedAddCommGroup V]
  [NormedSpace E V] [FiniteDimensional E V]`. `ρ : Representation E (B × L) V`
  encodes linearity and the action laws; `_hρ` is joint continuity on `(B × L) × V`.
  `_hfinite : Finite (Set.range (fun b : B ↦ ρ (b, 1)))` says exactly finite B-image.
- The conclusion chooses `K : OpenNormalSubgroup B` and identifies its subgroup
  with `(Representation.asGroupHom (ρ.comp (MonoidHom.inl B L))).ker`. Thus K is
  the actual kernel, open and normal, rather than an unspecified subgroup.
- `FiniteKernelImageIdentified L ρ K` uses the range subgroup of the group
  homomorphism into units of `Module.End E V`. Its topology is induced by all vector
  evaluations into V. It requires a topological group isomorphism from `B/K` to
  this actual image, sending each coset bK to ρ(b,1). Finite image is a hypothesis;
  openness makes B/K finite discrete by the existing OpenSubgroup instances.
  Evaluation topology is Hausdorff, so the finite operator image is also discrete.
- The next universal finite-quotient clause is `_hB` with B replaced by
  `normalKernel B K`. This is the actual subgroup with the inherited topology,
  bundled by the dependency; there is no new topology on K.
- The last two conjuncts specialize `FiniteKernelCoefficientAssertion` to F=E and
  F=Ω. They use `Extended E F V`, the actual `F ⊗[E] V` with the recorded module
  topology, and `extendedRepresentation`. `Realization` identifies every section
  module with all continuous functions into this tensor product, preserving scalar
  action, restriction, and generalized group action. Thus the coefficients are the
  stated C_F, not locally constant functions or an abstract isomorphism class.
- The coefficient assertion first gives a residual representation σ of `(B/K) × L`
  with `σ (QuotientGroup.mk b, l) = ρ (b,l)`. It asserts existence of realizations
  on both groups and normalized invariant data for K, B×L, and (B/K)×L. These
  existence clauses prevent the subsequent universal clauses from being vacuous;
  they do not select an unspecified coefficient object for a definition.
- For every pair of these actual realizations M and MQ, the action restricted by
  `normalKernelInclusion B K L` fixes each section for every profinite S and every
  continuous `g : C(S, normalKernel B K)`. Quantifying over all test objects also
  includes every base change. The next clause is an isomorphism of K-action modules
  to the trivial action on `∏ᶜ (_ : Fin (Module.finrank E V)), Mod.regular C_F.X`.
  This is precisely C_F^d with trivial action.
- The augmentation uses an equivariant `iK` whose underlying module map is
  `𝟙 M.object.module`. `finiteKernelAugmentation` applies the normalized ordinary
  adjunction transpose, inserts it in degree zero, and follows it by the recorded
  `unitZero`. Its type is exactly `V_F[0] ⟶ RΓ_K(V_F[0])`. Its IsIso clause holds
  for every normalized invariants datum dK; no arbitrary arrow is quantified over.
- The quotient arrow uses `normalProjection B K L`, the actual quotient on B and
  identity on L. Its coefficient map i is specified by `RepresentsMap` for the
  identity linear map on `Extended E F V`, after `Realization.inflate` of MQ.
  This fixes i on every continuous section and hence uniquely. The final IsIso
  assertion applies to `inflationZero ... i` for every pair dBL,dQL of normalized
  invariant data. These are ordinary total right derived invariants in the
  recorded standard unbounded localizations, not a separately chosen bar complex.
  `invariantMap_inclusion`, `unitZero_h0_isIso`, and `inflationZero_unit` from the
  recorded arrow module give exactly the stipulated invariant-inclusion H^0
  normalization; no additional arbitrary normalization hypothesis is needed.

Dependency declarations read and used:

- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingSheafOfUniverse`, its underlying ring object and
  multiplication. `normContinuousRing` is the normed-field specialization already
  used by the continuous-representation dependency, with these same sections.
- `def-weil-size-convention` is a metatheoretic convention with no module or
  declaration. Explicit `universe u`, `Profinite.{u}`, fields in Type u and vectors
  in Type (u+1) put continuous-section sheaves in the prescribed next universe.
- `Sheaf.CategoryTheory.CondensedActionModule`:
  `Profinite.CondensedAction.Modules`, `sectionModule`, `ActionModule`, `inflate`,
  `trivial`, and `Invariants`, with its section inclusions and normalized adjunction.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  the recorded derived-category convention, alongside the standard ordinary
  `Functor.rightDerivedFunctor` on these Grothendieck module categories.
- `Sheaf.CategoryTheory.CondensedDerivedInflationArrows`:
  `Profinite.CondensedAction.PrimeToEll.unitZero`, `inflationZero`,
  `modulesDerived`, `actionsDerived`, and the normalization facts listed above.
- `Sheaf.Paper.ContinuousRepresentationCondensation`:
  `Profinite.CondensedAction.ContinuousRepresentation.Realization`,
  `Realization.inflate`, `RepresentsMap`; and
  `Profinite.CondensedAction.PrimeToEll.Extended`, `extendedRepresentation`,
  `extendedTopology`, and its topological-module instances.
- Added landed statement dependency `def-sfb-normal-invariant-comparison-data`,
  `Sheaf.CategoryTheory.CondensedNormalInvariantData`:
  `Profinite.CondensedAction.normalKernel`, `normalKernelInclusion`,
  `normalProjection`. These give the actual existing group constructions, avoiding
  a private copy. No hypotheses from the NormalSystem certificates are imposed.
- Proof-only imports are the recorded modules
  `Sheaf.CategoryTheory.PrimeToEllCondensedAcyclicity`,
  `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`,
  `Sheaf.CategoryTheory.CondensedNormalSubgroupComparison`, and
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`. The proof dependency
  `lem-sfb-normal-inflation-resolution-naturality` has no recorded Lean module in
  the read repository, so no nonexistent import is invented. Its role is retained
  explicitly in the theorem's full natural-language proof docstring.

The source paragraph (3) was read in the current main-20261015 snapshot. It gives
proper/open direct-image stability and factorization, not an external proof of this
analytic input. The node honestly labels its seven-step proof agent-formulated and
its exact ordinary-condensed reference WANTED; the theorem docstring preserves that
proof route (open kernel; normal core; basis coordinates; finite-rank augmentation;
normalized normal-subgroup comparison; detection; canonical quotient inflation).
The inherited review flags a completeness gap in a dependency's proof. This delivery
states this node and does not claim that gap has been proved away.

Edge cases checked: V=0 gives finrank zero and the empty categorical product, so no
positive-rank condition excludes it. K=1, Q=1, B=1, and L=1 are permitted by every
binder; the maps are the same actual inclusion and quotient maps in those cases.
The empty profinite test object is included in all section conditions. Ω is not
assumed complete. Normed finite-dimensional V is Hausdorff, as needed for openness
of the finite-image kernel. No faithful B-action, quotient splitting, chosen basis,
or nontrivial group assumption was added.

Searches for an existing identical statement (the retained searches.jsonl records
these calls from the interrupted draft): msearch grep
`finite.*image|open.*ker|quotient.*inflation` in RepresentationTheory returned no
Mathlib hit; Loogle `"Representation", "ker"` returned invariants/coinvariants and
intertwiner kernels, not this result; LeanFinder
`A continuous finite image linear representation of a profinite group has open kernel
and derived condensed invariants are unchanged by quotient inflation` returned
condensation, profinite quotient limits and ordinary continuous H^0, no matching
ordinary internal condensed derived statement. Direct rg searches for the same
patterns in WeilConjectures and Sheaf, and the item's blueprint id in WeilConjectures,
found no identical theorem. Source inspection found the reusable actual kernel and
quotient constructions in CondensedNormalInvariantData, which are now used.
The draft declaration names were also searched in both source roots with no collision.
The example CompactObject module currently contains only a withdrawal marker;
its node record was read, and the delivery follows the active module-mode headers
and explicit namespace conventions of the recorded dependencies.

No STATEMENT-DISPUTED flag: the statement is preserved. The dependency-proof gap
mentioned above is disclosed, not silently converted into a stronger hypothesis.

Validation: the delivered module passed scompile.py in both sandbox and library-name
mode, with no errors or warnings (30.8 s and 17.4 s respectively).

## Second reading by Q151

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
