## Worker report

The module `Sheaf.Paper.TwoTermReductionCohomology` states
`AlgebraicGeometry.ProEtale.TwoTermReduction.two_term_reduction_cohomology`.
The only postponed proof is that theorem. All auxiliary definitions have real data;
the result records specify the canonical comparisons, not arbitrary maps between
isomorphic objects. The node's mathematical statement, proof and proof dependencies
are unchanged. No new nodes or dependency repairs are needed.

### Hypotheses and conventions

- A prime is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The algebraically closed field is `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`;
  the scheme is literally `Spec (.of Ω)`.
- `Scheme.ProEt.topology X` is the existing small pro-etale topology. Its object
  and morphism universes remain `u+1` and `u`, respectively; coefficients are in
  `u+1`. No equality of these two site universes is assumed.
- `HasDerivedCategory.{w}` fixes the chosen localization universe, as in the
  recorded derived-category and size-convention nodes.
- `p` and `N` are the existing `SuccessiveDerivedQuotient.Presentation` and
  `Normalization`: presentations of the already specified ordinary sheaf tensor
  extension and its universal left-derived pair, with the normalized ordinary
  and derived adjunctions and their comparison maps. They are not additional
  flatness, surjectivity, or boundedness assumptions. The landed definition node
  `def-pbc-successive-derived-scalar-normalization-data` owns these data types;
  the result is stated for every such canonical presentation and does not choose
  them from the normalization existence theorem. These binders let the formula
  refer to the actual canonical quotient mate, including its computation counit.

### Clause-by-clause correspondence

All names below are in `AlgebraicGeometry.ProEtale.TwoTermReduction` unless qualified.
The data records have separate predicates `IsRealization`, `IsCohomology`, and
`IsTensorCalculation`; each conjunction clause is labeled by its descriptive name
in a source comment. `Calculation` contains both the data and these predicates.
Separating equations from data avoids expensive generated structure projections.
The paper's positive exponent is the Lean index plus one: `n : ℕ` means exponent
`n+1`, and the paper's inclusion multiplier is consequently `ℓ^n`.

- The inverse image is the recorded `upperStarFromPoint X`, definitionally the
  dependency's `sfbPullbackFromPoint X`. `ring X A` applies its `mapCommMon` to
  the existing continuous-function condensed ring and then applies the existing
  `InternalAbelianSheafModule.sectionRingSheaf` transport. Thus `ring X ℤ_[ℓ]`
  is exactly R and `finiteRing ℓ X n` is exactly B_(n+1), as section rings.
  The integral coefficient is not replaced by a discrete constant ring.
- `map` applies the actual continuous postcomposition map through these same
  functors. `projection` uses `PadicInt.toZModPow`, `step` the consecutive
  `ZMod.castHom`, and `residue` reduction to `ZMod ℓ`. `Realization.compatible`
  states the equality of these actual quotient maps.
- `k ℓ X n` is restriction along `residue` of the unit module over
  `ring X (ZMod ℓ)`. Its B_(n+1)-action is therefore reduction modulo ℓ.
  The `constantResidue` clause of `IsCohomology` identifies its common underlying abelian sheaf
  with the existing `constantSheaf` of `ULift (ZMod ℓ)`. The recorded finite
  discrete ring-comparison theorem is imported for precisely this identification.
- `complex ℓ X R` is `HomologicalComplex.double` of `ℓ • 𝟙` on the actual unit
  module, in degrees -1 and 0. Its other terms are the zero object by construction.
  `termMinus` and `termZero` are the library's double-complex term isomorphisms.
- `localized` is Qh of the homotopy quotient, the canonical factorization of
  Q(P) (`DerivedCategory.quotientCompQhIso`). `localizedHomology` is the existing
  pair of homology-factorization isomorphisms, not a new cohomology definition.
- The `kflat` clause of `IsRealization` is the recorded independent-coefficient K-flat predicate
  on this literal integral complex.
- `Realization.ordinary` identifies the recorded ordinary scalar extension with
  the literal finite two-term complex; `ordinary_sections` fixes it on pure tensors
  to b times the image of the integral coefficient in both nonzero degrees.
- `Realization.model` identifies the actual derived reduction with the finite
  complex's localization. `model_eq` fixes its hom to the universal computation
  counit followed by the ordinary comparison, so the representative identification
  cannot be chosen with an unrelated normalization.
- `Realization.chain`, `chain_minus`, and `chain_zero` specify the quotient chain
  map and say that both of its components are the actual consecutive reduction.
  `transition` is the adjunction mate of the normalized scalar-composition map;
  `transition_eq` identifies that actual derived quotient mate, after the models
  and exact restriction factorization, with localization of this chain map.
- `Cohomology.minus`, `zero`, and the `vanishes` specification clause give the two B_(n+1)-linear
  identifications and all other-degree vanishing on the finite representative.
  `derivedMinus`, `derivedZero`, and `derivedVanishes` state these on the actual
  derived reduction; their `_eq` specification clauses fix the transport by `model` and
  `localizedHomology`.
- `kernelCoefficient` is an additive coefficient map whose values on every integer
  class are fixed by `kernelCoefficient_formula` to a ↦ ℓ^n a. `additiveMap`
  constructs the actual continuous additive postcomposition map. `inclusion_eq`
  requires that the underlying additive sheaf map of `inclusion` is exactly its
  pullback. `minus_eq`, using `homologyπ` and `iCycles`, says that the degree -1
  identification is the inverse of this inclusion on cycles. This retains the
  prescribed pre-pullback coefficient map, not just an unspecified isomorphism.
- `reduction_eq` fixes `reduction` on every section to the actual residue map;
  `zero_eq` says the degree-zero identification is its induced cokernel map.
- `minus_transition` is zero for the homology map of the actual chain reduction,
  with the canonical `restrictHomology` comparison. `zero_transition` is the
  corresponding identity under the two `zero` identifications.
  `residueIdentity_eq` fixes that identity as an equality of underlying additive
  sheaf maps on the common residue sheaf.
  Together with `transition_eq` these are the asserted transitions on H(K_n).
- The `nonzero` clause of `IsCohomology` says `¬ IsZero (k ℓ X n)` for every positive exponent.
- `TensorCalculation.action` is an isomorphism from the existing sheafified
  `changeOfRings (step ...)` of H^-1(P_(n+2)) to the residue sheaf. By the
  specified derived model this is the tensor in the node. `pure` is the existing
  sheaf pure tensor, written scalar first by the dependency's convention;
  `action_eq` fixes it to b acting through the residue action on the identified x.
  `sectionSMul` merely projects the section module's existing scalar action.
- The `induced_eq` clause of `IsTensorCalculation` fixes the balanced induced map on those same
  pure tensors to b times the cohomology transition, and `induced_zero` says it
  is zero. Thus both the isomorphism and the final zero-map clause refer to the
  canonical maps of the node.

`Calculation` bundles `Realization`, `Cohomology`, `TensorCalculation`, and all
three specification predicates to keep Lean's structure elaboration small.
These records use the existing ring, tensor, cohomology, and derived category.

### Dependencies read and used

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`:
  `sfbPullbackFromPoint`, the alias of upstream `upperStarFromPoint`.
- `Sheaf.Topology.ProfiniteCondensedRing` and its public continuous-coefficient
  imports: `Profinite.CondensedRing`, `continuousMapRingObj`,
  `continuousMapRingSheafMap`. The latter is the standard postcomposition map.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`; these are the monoidal pullback construction used by `ring`.
- Mathlib's padic integers and ring-hom modules: `PadicInt`, `toZModPow`;
  `WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms`:
  `PadicInt.continuous_toZModPow`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, used by the
  dependency's transparent `Modules` abbreviation.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and its upstream
  tensor imports: the independent-universe sheaf tensor and `changeOfRings`.
- Mathlib `CochainComplex`, `HomologicalComplex.double`, `doubleXIso₀`,
  `doubleXIso₁`, `homologyπ`, `iCycles`, and `homologyMap`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` and `HomologySequence`:
  `DerivedCategory`, `HasDerivedCategory`, Qh, `homologyFunctor` and its
  factorization isomorphisms; homotopy quotient and homology factorization.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `DerivedChangeOfRingsCochainModel` and its existence theorem. The statement
  uses the already landed equivalent normalized universal-pair presentation
  below to name simultaneous canonical maps.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`: `Modules`,
  `restriction`, `pure`, `Presentation`, `sectionTensor`, `Normalization`,
  owned by `def-pbc-successive-derived-scalar-normalization-data`. The existence
  theorem `successive_derived_quotient_normalization` is not used in the signature.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `sectionRingSheaf`, `commMonToRing`, the existing internal-to-sectionwise transport.
- `Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`:
  `sheafRingCoefficientOrdinaryAdjunction`. Its finite-limit and finite-colimit
  preservation witnesses define `restrictHomology`, the canonical exact-functor
  homology comparison. These witnesses are propositions; no data is chosen from
  an undetermined existence theorem.
- `Sheaf.Paper.CondensedPointDiscreteConstantComparison`:
  `condensed_point_discrete_constant_comparisons`, read in full.

The last three extra statement interfaces have existing landed DAG nodes, appended
to `stmt_deps` as allowed by brief §5; they are not new definitions or repairs.
Proof-dependency modules are imported ordinarily: bounded-flat K-flatness,
K-flat scalar-tower realization (landed while this item was being written),
condensed-point coefficients and finite comparisons, constant-ring module
sheaves, constant-realization detects-zero, and the locally-bijective constant
module unit. The sheafification and flatness Mathlib interfaces are available
through their existing dependency imports.

### Edge cases

For the paper exponent 1 (Lean index 0), multiplication by ℓ on ZMod ℓ is zero;
both cohomology objects are k and the prescribed kernel inclusion is multiplication
by ℓ^0 = 1. The next quotient reduction kills its kernel generator ℓ. For ℓ=2,
the reduction Z/8 → Z/4 kills the source kernel generator 4 and preserves reduction
to Z/2. Prime 0 and prime 1 are excluded by exactly the prime hypothesis, and
exponent 0 is excluded by the shifted indexing, not by an extra hypothesis.
The characteristic of Ω is unrestricted, including characteristic ℓ: these are
coefficient sheaves, not O_X-modules. Spec Ω is nonempty for every field, so the
residue sheaf is nonzero; there is no empty-scheme exception suppressed in the
statement. All integers q outside {-1,0}, including negative q, are quantified.
The final tensor is ordinary sheaf tensor, not derived tensor: the zero induced
map and the nonzero source therefore coexist as required.

### Searches

- Prescribed msearch LeanFinder: “two term complex differential multiplication
  prime derived reduction cohomology ZMod prime power”: eight generic group
  cohomology/cyclic resolution hits, no instance of this sheaf calculation.
- Prescribed msearch Loogle: “CochainComplex.single, CochainComplex.of,
  ZMod.castHom”: no hit (the first searched name was not a known declaration).
- Prescribed msearch grep in `Algebra/Homology`: `twoTerm|two.term|TwoTerm`:
  no hits. The actual two-term constructor was found directly as
  `HomologicalComplex.double`, and reused.
- Prescribed msearch LeanSearch: “two term complex prime power quotient
  cohomology transition zero identity”: eight generic cohomology and homotopy
  hits, no exact statement.
- `rg` of both project source roots for two-term/prime-power cohomology found
  determinant, procyclic and unrelated two-term material; none states this node.
  Searching this node id in upstream WeilConjectures returned no declaration.
- `tools/blueprint_refs.py search 'two-term'` returned five different notions
  (Koszul/Nakayama/diagonal tower/procyclic/Roos), not a duplicate statement.
- Read the existing node records and actual signatures/docstrings for every
  statement dependency, including the mathlib-match records. No new independent
  mathematical notion was needed; helper declarations belong to this calculation.

No statement dispute, source correction, or dependency interface fault was found.
Validation: `scompile.py O2 lem-pe-two-term-reduction-cohomology` passed with
no errors or warnings (sandbox 43.3 s, actual library module 54.5 s, each below
the unmodified 60-second limit). `deliver2.py ... --no-push` then returned
`OK (dry run)` at d3dee967597: preflight and compilation passed, nothing pushed. No global build or direct repository write was performed.

## Second reading by O2

I reread the full node against the module, including both map normalizations and
all three parts of `Calculation`. The dispatcher explicitly instructed this worker
to deliver itself and not start other agents; this is therefore a worker self-check,
not a claim of an independent second worker. The maintainer's independent delivery
review is still required. The rereading found and repaired a missing `mapHomotopyCategoryFactors` transport
in `transition_eq`: exact restriction and termwise restriction agree by the
canonical comparison, not by an assumed definitional equality. It retained the
canonical counit in `model_eq`,
the coefficient inclusion before pullback in `inclusion_eq`, the residue action in
`action_eq`, and all universe levels. It found no change to the mathematical node
was required. An inferred scalar-action mismatch was repaired by using the explicit
existing section-module action, rather than changing a scalar ring or hypothesis.

## Returned-delivery repair (2026-10-21)

The return at immutable head `f2a79c6fbcc8` identifies one H2 fault: the added
statement dependency named the normalization existence theorem although this
statement only uses its plain data declarations. Replaced
`lem-sfb-successive-derived-quotient-normalization` in `stmt_deps` with the
already landed `existing: true` definition node
`def-pbc-successive-derived-scalar-normalization-data`. Read that node and the
actual `Modules`, `restriction`, `pure`, `Presentation`, `sectionTensor` and
`Normalization` declarations and docstrings in
`Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`. They are exactly
the interfaces used by this module; `p` and `N` remain parameters, with no choice
from the normalization existence theorem. No dependency module or new node is
needed. The mathematical statement, proof, proof dependencies and Lean file
remain unchanged.

Retained `lem-pur-sheaf-ring-coefficient-ordinary-adjunction` in `stmt_deps`: the
`restrictHomology` definition uses `.choose` and `.choose_spec.choose` of its
exactness witnesses, and the cohomology transition and tensor clauses use that
definition. This is a genuine theorem dependency as the return confirms.

Self-check: reread the complete saved module and matched the prime and field
binders, all positive exponents, K-flatness, canonical counit normalization,
termwise transition, both cohomology identifications, other-degree vanishing,
zero/identity transitions, nonvanishing and the two tensor-map equations against
the unchanged node. No further mismatch was found. The saved packet first passed
`deliver2.py --no-push` at `1bca2f93523` before this repair; the repaired packet is
validated again below.

Repair validation: prescribed `scompile.py` passed both the sandbox (43.3 s)
and actual library module (54.5 s), with no diagnostics. A direct self-check
confirmed that only `lean` and `stmt_deps` differ from the current read-clone
node, the recorded signature is verbatim, the sole postponed proof is the named
item theorem, and the Lean file SHA256 remains
`c7da68fc1c3c5dd7d6c680550e4f756db47f09df90d61b30aafa596dfa47cf96`.
