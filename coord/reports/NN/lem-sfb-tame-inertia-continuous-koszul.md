## Worker report

Stage 2, NN, lem-sfb-tame-inertia-continuous-koszul. The delivery states
`Profinite.TameInertiaKoszul.continuous_koszul` in
`Sheaf.Paper.TameInertiaContinuousKoszul`. Its only postponed proof is the item
itself. The helper definitions have real data; the structures specify normalized
objects by their sections, restrictions, actions, and derived universal properties.
Their existence is part of the conclusion `Nonempty Result`, never an extra
hypothesis on the representations. No object is chosen from this theorem.

The previous attempt reported that the item had already been merged. The live
node contains a stage-1 split/review, but no `lean` binding. This is its stage-2
statement. The mathematical statement is retained verbatim. Its `stmt_deps`
gains the already landed `def-sfb-condensed-action-module`, whose internal action
category and normalized invariants are used directly.

### Hypotheses and mathematical objects

- Distinct primes: `(p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_distinct : p ≠ ℓ)`.
- The background characteristic-p field: `(k : Type v) [Field k] [CharP k p]`.
  It is retained even though this abstract inertia calculation does not depend on k.
- Algebraic closure with extended norm: `(Ω : Type u) [NormedField Ω]
  [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]`.
  `NormedAlgebra` supplies the algebra structure and the extended field norm;
  there is no completeness assumption on Ω.
- Finite intermediate field: `(E : IntermediateField ℚ_[ℓ] Ω)
  [FiniteDimensional ℚ_[ℓ] E]`. Its norm and topology are the inherited ones.
  The scalar inclusion used in the result is the actual subtype inclusion,
  with its existing proof `continuous_subtype_val`.
- Rank: `(r : ℕ)`, with zero allowed.
- `Group p r` is the multiplicative spelling of the additive product
  `Fin r → (q : {q : Nat.Primes // (q : ℕ) ≠ p}) → ULift (PadicInt q)`.
  The topology is the actual product topology. `ULift` only aligns universes.
  `complement p ℓ r` is the subgroup with zero in all ℓ coordinates; it is
  canonically the stated product over q different from p and ℓ.
  `generator p ℓ r i` has 1 in the i-th ℓ coordinate and 0 elsewhere.
- `Inputs E p ℓ r` is the full subcategory of the existing `Rep E (Group p r)`
  with predicate `admissible`. The predicate is exactly: finite dimension;
  joint continuity of `(g,m) ↦ ρ(g)m` for the finite-dimensional module
  topology; finiteness of `Set.range (ρ.comp complement.subtype)`; and
  `Nat.Coprime (Nat.card thisRange) ℓ`. The range is the actual Q, not a
  larger auxiliary quotient. Morphisms are all equivariant E-linear maps.
- `fixed M` reuses `Representation.invariants` for the restricted H-action.
  `average M` is literally `|Q|⁻¹ • ∑ q : Q, q.val`, using the finite-image
  proof supplied by admissibility. `Result.average_range` states
  `fixed M = LinearMap.range (average M)`, recording N=im(e) as well as N=M^H.
  `operator M i` is the existing `Representation.toInvariants` applied to γ_i.

### Coefficients, complexes, and every conclusion clause

- `ring F` bundles the dependency's actual
  `continuousMapRingObjOfUniverse F` and its recorded monoid-object structure.
  Its sections are all continuous F-valued functions, with the prescribed
  universe lift. This is the internal-ring presentation of C_F, not constant
  or locally constant coefficients. The background notation C_{F,T}=p_T^*C_F
  is the imported `AlgebraicGeometry.ProEtale.coefficientRing`; no T enters
  this local group calculation, so no extra scheme is quantified.
- `Space E F V` is the algebraic tensor product `F ⊗[E] V`, with
  `moduleTopology F` installed explicitly. For the finite-dimensional V in
  this theorem this is precisely the finite-dimensional product norm topology.
  `Sections E F V S` is `ULift C(S, Space E F V)`.
- `Model E F V obj` gives additive bijections from the existing internal
  module's section modules to exactly these all-continuous functions, with
  pointwise scalar multiplication and every restriction equal to precomposition.
  These conditions determine the module up to its unique presented isomorphism;
  there is no unspecified coefficient object.
- `Realization.action`, `.module`, and `.action_sections` give M_F and its
  action by EVERY local section `g : C(S, Group p r)`, evaluated as
  `LinearMap.baseChange F (ρ (g s))`. This uses the landed internal action
  category, not the abstract category of discrete group representations.
  `.map_sections` fixes the action functor on equivariant morphisms.
- `.invariants` and `.fixedModule` similarly present N_F;
  `.fixed_map_sections` uses `fixedMap` and scalar extension for every morphism.
- `Indices r a = {I : Finset (Fin r) // (I.card : ℤ) = a}`.
  `.coordinates`, `.coordinates_scalar`, and `.coordinates_restriction`
  identify each term with the finite direct sum of copies of N_F indexed by
  these subsets, naturally and linearly on all profinite test spaces.
  Since the index set is finite, its function object is the finite biproduct.
- `.koszul` is a functor to actual `CochainComplex ... ℤ`.
  `.differential` states exactly the displayed formula: its finite matrix
  sums over I and i, retaining the entry iff `i ∈ J` and `J.erase i = I`;
  its sign is `(-1 : ℤ) ^ (J.filter (fun j ↦ j < i)).card`; its operator is
  `LinearMap.baseChange F (operator M i - LinearMap.id)`. Thus this has exactly
  the stated sign and omitted-index convention. `.koszul_map_sections` fixes
  naturality termwise, without permutations or an unspecified chain map.
- `ActionAbelianData` and `actionAbelian` express abelianness of the actual
  action category while keeping the EXISTING `actionPreadditive` definitionally.
  `modulesDerived` is the standard ordinary localization. `Context` supplies
  ordinary unbounded derived invariants: the landed `CondensedAction.Invariants`
  plus a functor, its unit on the homotopy category, and the existing
  `Functor.IsRightDerivedFunctor` universal property at ALL quasi-isomorphisms.
  This is not a bounded, completed, or separately cohomological substitute.
- `derivedInvariants d` applies that ordinary total right derived functor to
  M_F placed in degree zero.
  `Comparison.kappa` is the natural isomorphism
  `d.koszul ⋙ DerivedCategory.Q ≅ derivedInvariants d`, in exactly the direction
  K_F(M) → RΓ_G(M_F). Both E and Ω comparisons occur in `Result`.
- `Comparison.inclusion` starts from the ACTUAL G-invariant module in degree
  zero. The first conjunct of `ComparisonNormalization` identifies its section
  formula with the inclusion of invariant vectors into M_F through N_F.
  The second conjunct is the equality
  `Q.map (inclusion M) ≫ kappa.hom.app M = augmentation ... M`.
  `augmentation` explicitly uses the derived unit and the standard
  single-complex and quotient comparison isomorphisms. This is the requested
  degree-zero normalization, not merely an isomorphism on H^0.
- `coefficientMap` is the dependency's map obtained by postcomposition with
  `algebraMap E Ω`. `coefficientRestriction` is the actual `Mod.comap` along
  that internal ring map. `ScalarRestriction` presents its action version
  using an underlying-module isomorphism, the equation for every local group
  action, and an invariant comparison preserving the ACTUAL invariant inclusions.
  Its exactness is concluded in `Result`, not assumed of M.
- `restrictionDerivedUnit` and `restrictionTargetUnit` assemble the ordinary
  derived units and exact-functor comparison isomorphisms.
  `RestrictionUniversal` records the ordinary derived universal property for
  action restriction followed by invariants. `derivedCoefficient` is a REAL
  definition using `Functor.rightDerivedDesc` with those two units. Thus the
  derived scalar transformation is canonical; it is not an arbitrary map
  introduced to make the final square commute.
- `extension E Ω V` is literally
  `TensorProduct.map (Algebra.linearMap E Ω) LinearMap.id` on
  `E ⊗[E] V → Ω ⊗[E] V`. Under the usual identification of E⊗_E V with V,
  this is v ↦ 1⊗v. `CoefficientMaps.action_sections` and `.koszul_sections`
  require the representation map and EVERY termwise Koszul coordinate to
  have exactly this formula on every profinite test space.
- `representationCoefficient` takes this actual action-module morphism,
  places it in degree zero, applies the ordinary derived functor, and
  composes with `derivedCoefficient`. `CoefficientSquare` says, for every M,
  `κ_E ≫ inducedCoefficient = termwiseCoefficient ≫ Res(κ_Ω)`, including
  the exact-functor localization transport. This renders the full requested
  square in the ordinary derived category.
- For r=0 the third conjunct of `ComparisonNormalization` makes both the
  invariant inclusion and its map into K isomorphisms. Their explicit section
  normalizations identify both with the identity M_F. The derived-unit
  equation then identifies κ_F with the identity on M_F[0] under the canonical
  derived-unit identification. This fixes the identity normalization, rather
  than merely asserting that some comparison is invertible.
- All tensor products and continuous-map spaces are literal. There is neither
  a completed tensor product nor a filtered union of finite-subextension sheaves.

### Dependency declarations and source reading

The item's source paragraph (3) in main-20261015 was read: it is the direct-image
stability context. As its node explicitly records, this analytic tame input and
its proof obligations are agent-formulated, with an exact analytic reference
WANTED. No stronger citation or finished analytic proof is claimed here.

- `def-sfb-continuous-map-condensed-ring`:
  `Sheaf.Topology.ContinuousMapCondensedRing`,
  `Profinite.continuousMapRingSheafOfUniverse`, and its recorded internal
  presentation `continuousMapRingObjOfUniverse` /
  `continuousMapRingObjOfUniverseMonObj`.
- `sk-def-sfb-pulled-back-coefficients`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing` (background pulled-back notation).
- `sk-def-sfb-module-objects`:
  `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.Mod`.
  This is the internal module category throughout.
- `sk-def-sfb-module-derived-pushpull`:
  `Sheaf.Paper.CondensedModuleDerivedPushpull`,
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward` /
  `moduleObjectDerivedPullback`. Their full signatures and docstrings were
  read. The present group calculation uses the same ordinary derived
  universal property, specialized to the invariants functor, not the
  geometric scheme-specific pushforward itself.
- `def-sfb-continuous-map-condensed-ring-map`:
  `Sheaf.Topology.ContinuousMapCondensedRingMap`,
  `Profinite.continuousMapRingObjMapOfUniverse` and
  `isMonHom_continuousMapRingObjMapOfUniverse`.
- Added already-landed dependency `def-sfb-condensed-action-module`:
  `Sheaf.CategoryTheory.CondensedActionModule`,
  `Profinite.CondensedAction.Modules`, `sectionModule`, `ActionModule`,
  `actionPreadditive`, `forgetAction`, and `Invariants`.
  Their full definitions, normalized fixed-section condition and adjunction
  inclusion formulas were read and reused.

The three proof dependencies currently have no usable recorded Lean module;
none is silently substituted by discrete or finite-coefficient cohomology.
Their exact role is retained in the theorem's complete natural-language proof
plan. They are proof prerequisites, not missing objects needed to TYPE this item.

### Edge cases

Checked before finalizing: r=0 (the products are trivial, Q=1, N=M, and the
normalized comparison is the identity); M=0 and N=0 (all section models and
Koszul terms give zero objects); negative degrees and degrees above r (Indices
is empty, so the term has only the zero section); the empty profinite test
space (continuous-map spaces have their unique sections); r=1 (d=γ_0−1);
r=2 (the signs are positive for omission of the smaller index and negative
for the larger index, with commuting operators cancelling in d²).
Q=1 and E=ℚ_ℓ are permitted. Nontrivial finite prime-to-ℓ H-actions are
retained. The uncompleted Ω topology is used even for continuous maps whose
image is not contained in any one finite subextension.

No statement correction or STATEMENT-DISPUTED flag is introduced: the analytic
assertion remains the explicitly wanted input of this node. Its proof is not
claimed to follow just from finite averaging or from discrete group cohomology.

### Searches and validation

- LeanFinder (msearch): “Derived invariants of continuous tame inertia actions
  on condensed finite dimensional ell adic vector spaces are computed by
  Koszul complexes”: eight hits, including continuous-cohomology/topological
  module complexes, but none stating this internal condensed comparison.
- Loogle (msearch): `"Condensed", "invariants"`: zero hits.
- Mathlib grep (msearch):
  `(Condensed|condensed).*(invariant|Koszul|koszul|TopModule)|(invariant|Koszul|koszul|TopModule).*(Condensed|condensed)`:
  zero hits.
- LeanSearch (msearch): “Internal condensed modules associated to continuous
  finite dimensional representations and their signed Koszul complexes”:
  eight hits including CondensedMod/LightCondMod constructions over fixed
  discrete base rings; none is this internal norm-topological statement.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for condensed actions,
  invariants and Koszul comparisons: the landed internal action framework is
  reusable, while representation/continuous-cohomology results do not state
  this comparison. The exact item identifier has no upstream theorem match.
- DAG/blueprint search for continuous representations returned existing
  l-adic representation nodes and four blueprint references, not this
  all-continuous internal Koszul theorem. No new independent notion/node
  is introduced; the normalized section and derived transport helpers
  belong to this item's specified objects and canonical maps.

All compilation uses the prescribed `scompile.py`, against the live published
library. A large dependent structure's derived normalization originally
elaborated too slowly; factoring its laws into the separate real predicate
`ComparisonNormalization` fixed this within the default 60-second limit.
The full theorem compiled; the final pass removes an overlapping algebra
instance warning by retaining just `NormedAlgebra`, which already contains
`Algebra`. The dry run passed the clean per-file compile and maintainer preflight
(`OK (dry run)`, candidate commit `34da4b7cde1`); no errors or non-sorry
warnings remain.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
