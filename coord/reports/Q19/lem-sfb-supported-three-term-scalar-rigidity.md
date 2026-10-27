## Worker report

This stage-2 delivery states
`AlgebraicGeometry.ProEtale.CondensedRing.supported_three_term_scalar_rigidity`
in `Sheaf.Paper.SupportedThreeTermScalarRigidity`. Its sole theorem proof is `sorry`.
No definitions or subsidiary theorems are introduced. The module docstring records the
source; the theorem docstring reproduces all eleven reviewed proof steps with their
node citations. The accepted stage-1 statement and proof remain unchanged.

The previous worker's unchanged-item failure concerned stage 1, not this stage-2
assignment. I followed the maintenance stage-handoff paragraph of brief-stage2 §0:
the current node was split and reviewed but had no `lean` field. No repair note exists.
The queue lists stage 2 as the open work.

### Hypothesis and clause correspondence

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]`. |
| Commutative condensed coefficient ring and pulled-back coefficients | `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, `[MonObj Λ] [IsCommMonObj Λ]`, and the existing `condensedRingObj Λ V`. |
| Finite commutative A with discrete topology and an ell-power annihilator | First disjunct of `hΛ`, with CommRing, DiscreteTopology, IsTopologicalRing, Finite, and `∃ n, ∀ a, (ℓ ^ n) • a = 0`. Finite rings have small representatives, so `A : Type` loses no ring isomorphism class. |
| Z_ell | Second disjunct, `Profinite.continuousMapRingObj ℤ_[ℓ]`. |
| O_E for finite E in the fixed algebraic closure | Third disjunct, `E : PadicAlgCl.FiniteIntermediateField ℓ` and `Profinite.padicIntegersRingObj ℓ E`. |
| Q_ell | Fourth disjunct, `Profinite.continuousMapRingObj ℚ_[ℓ]`. |
| Finite E | Fifth disjunct, `Profinite.continuousMapRingObj E`. |
| Omega with all continuous maps | Final disjunct, `Profinite.continuousMapRingObj (PadicAlgCl ℓ)`. It is not the finite-subextension-valued `padicAlgClRingObj`. |
| Literal coefficient rings, independent of their presentation | Each case is a `Nonempty (Mon.mk Λ ≅ Mon.mk ...)`, an isomorphism of ring objects, preserving both addition and multiplication; this permits precisely copies of the listed coefficients. |
| Small sites and fixed indexing universe | Explicit `universe u`, `Scheme.{u}`, `Scheme.ProEt.topology`, `smallEtaleTopology`, and `Ab.{u + 1}`. No equation identifying site object and morphism universes is added. Derived category sizes are the existing framework's. |
| Closed immersion between qcqs schemes | `t : T₀ ⟶ T`, `[IsClosedImmersion t]`, `[CompactSpace T] [QuasiSeparatedSpace T]`, and the same two instances for T₀. |
| Every locally torsion abelian etale sheaf, without a common annihilator | `ht` quantifies over every `F` satisfying the recorded `Scheme.IsTorsionAbelianSheaf F`. There is no common killing integer. |
| Actual restriction bijective for every q >= 0 | `∀ q : ℕ, Function.Bijective (Etale.cohomologyMap t F q)`. This is the recorded actual cohomology restriction. |
| Finite admissible support chain | `tree : QcqsOpenClosedTree T` and arbitrary `p : tree.Path S`; see the representation check below. In particular `p` is not required to be a leaf path. |
| Open J_k = (a_k)! and closed J_k = (a_k)*; J = their composite | The existing `(p.extension Λ)` recursively uses exactly `CondensedRing.openImmersionLowerShriek` or `CondensedRing.lowerStar`, in the stated order. |
| Three terms and arbitrary b,c with cb = 0 | `L : ShortComplex (Mod ... (condensedRingObj Λ S))`, with `X₁,X₂,X₃` representing degrees -1,0,1, `L.f = b`, `L.g = c`, and `L.zero : L.f ≫ L.g = 0`. No matrix condition is imposed. |
| Each term has a finite constant scalar local model | The three independent hypotheses `hL₁`, `hL₂`, `hL₃` use the recorded `HasFiniteConstantLocalModel`. Each independently quantifies its cover, and its P may depend on each member. |
| N = ker c / im b | `L.homology`, Mathlib short-complex homology in this abelian category. Its kernel/cokernel universal property is precisely this quotient. |
| J(N)[0] | `(DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj L.homology)`. |
| Actual uncompleted module-derived sections with output D(Ab) | `Functor.rightDerivedPullback (upperStar Λ t)` is instantiated with the existing `condensedModuleSections Λ T` and `condensedModuleSections Λ T₀`. These derive module evaluation, not sections of an arbitrarily chosen underlying resolution. Its output is the ordinary unbounded derived category of `Ab.{u + 1}`. |
| Actual derived restriction is an isomorphism | `IsIso` of the component of that canonical derived natural transformation at J(N)[0]. The ordinary map is the existing module adjunction unit followed by presheaf restriction from the pullback of the terminal T-object to the terminal T₀-object. No arbitrary map is a parameter. |
| Exact inverse image with coefficient identification | The existing `upperStar Λ t` includes scalar extension along `condensedPullbackHom Λ t`. Its exactness instances are already supplied. Its `mapDerivedCategory` is the target of `rightDerivedPullback`. |
| Natural in morphisms of three-term complexes | The restriction in the conclusion is a natural transformation on the entire ordinary derived module category. Composing it with `ShortComplex.homologyFunctor`, `p.extension Λ`, and the degree-zero single functor supplies naturality on all short-complex morphisms. Naturality is encoded by this constructed transformation, not assumed or left as an arbitrary family of arrows. |
| No condition on N or on pulled-back matrices | There is no hypothesis on `L.homology`; only the three terms have local-model hypotheses. `L.f`, `L.g`, and their inverse images remain arbitrary actual morphisms. |
| No properness, henselian, Noetherian, or ell-invertibility restriction | None occurs in the theorem signature, the path constructors, or the local-model predicate. |
| Original t need not have qc complement | `t` is independent of `tree` and `p`; its hypotheses never mention its complement. Only path arrows have the complementary quasi-compact-open condition. |

### Support-chain representation and duplicate check

I first searched for a support-chain notion, then found the already landed
`def-sfb-qcqs-open-closed-tree` and read its full node and module, including all
constructors of `QcqsOpenClosedTree`, `Path`, and the full `Path.extension` body.
I reuse it and add only that landed node to `stmt_deps` as authorized by brief-stage2 §5.

This does not restrict the stated chains: inductively, for each open arrow in the
original chain, adjoin its reduced closed complement as a sibling leaf; for each closed
arrow, adjoin its open complement as a sibling leaf. The root is qcqs. Every subsequent
vertex and every sibling is qcqs: quasi-compact open subspaces and closed subspaces of
qcqs schemes are qcqs. A quasi-compact open immersion has a quasi-compact complementary
closed immersion. The open complement at a closed step is quasi-compact by precisely
the node's hypothesis. These are exactly the split constructor's assumptions. Carry the
remaining chain in the chosen child and terminate with a leaf at S. Conversely every
path has the original specified arrow conditions. Auxiliary siblings carry no modules,
rigidity assumptions, or choices of comparison maps, and `p.extension` ignores them.
The root path in a one-vertex tree is the r=0 case. This is the existing representation
of finite chains, rather than a new copy of their composite functor.

The ordinary and derived restriction expressions are the bodies of the existing
`torsionRigiditySectionsRestriction` / `torsionRigidityDerivedRestriction` in
`Sheaf.Paper.ClosedTorsionRigiditySerreTransfer`. I read those definitions. Importing
that module would import the downstream Serre-transfer theorem whose proof uses this
item. Instead the signature applies the existing general `rightDerivedPullback` directly
to the canonical unit-and-section expression, with an explicit type ascription. There
is no second named definition and no circular statement or import dependency.

The more general recorded `IsLocalizingAdmissibleCoefficient` now also includes the
distinct finite-subextension-valued algebraic closure. I read its full definition and
use exactly the item's six explicit disjuncts, so that no extra coefficient case is
silently substituted or asserted. No dependency record needs repair.

### Recorded dependency declarations

- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`; `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`, `CategoryTheory.IsLocalizingSubcategoryOfSize`, `CategoryTheory.localizingClosureOfSize`.
- `sk-def-sfb-module-derived-pushpull`: `Sheaf.Paper.CondensedModuleDerivedPushpull`; `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`, `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback`, `AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`, `CategoryTheory.Functor.rightDerivedFunctor`, `CategoryTheory.Functor.rightDerivedFunctorPlus`, `CategoryTheory.Functor.leftDerivedFunctor`, `CategoryTheory.Functor.leftDerivedFunctorCounit`, `CategoryTheory.Functor.isIso_leftDerivedFunctorCounit_app_of_kFlat`, `AlgebraicGeometry.ProEtale.CondensedRing.preservesKFlatQuasiIso_upperStar`, `AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunctionPlus`, `AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerStarIso`, `AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarIso`.
- `def-sfb-condensed-module-sections`: `Sheaf.Paper.CondensedQcqsPushforwardContinuity`; `AlgebraicGeometry.ProEtale.condensedModuleSections`.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`; `AlgebraicGeometry.Scheme.Etale`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`; `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-size-convention`: metatheoretic convention, rendered by explicit universe levels and the scheme-property binders; no new Lean definition.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`; `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-pbc-scheme-conventions`: metatheoretic convention, rendered by explicit universe levels and the scheme-property binders; no new Lean definition.
- `def-weil-pbc-torsion-etale-sheaf`: `WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf`; `AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf`.
- `def-weil-pbc-etale-cohomology`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`; `AlgebraicGeometry.Etale.cohomology`, `AlgebraicGeometry.Etale.rightDerivedGlobalSections`.
- `def-weil-pbc-cohomology-pullback`: `Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback`; `AlgebraicGeometry.Etale.cohomologyMap`, `CategoryTheory.Sheaf.H.mapFunctor`, `AlgebraicGeometry.Etale.abelianDerivedCohomologyPullback`, `AlgebraicGeometry.Etale.moduleDerivedCohomologyPullback`, `AlgebraicGeometry.Etale.moduleLerayPlus`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`; `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `def-sfb-module-open-lower-shriek`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`; `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek`, `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek_comp_forget`, `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek_additive`, `AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteLimits_openImmersionLowerShriek`, `AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteColimits_openImmersionLowerShriek`, `AlgebraicGeometry.ProEtale.CondensedRing.preservesHomology_openImmersionLowerShriek`.
- `def-sfb-module-lower-star`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`; `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar`, `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar_comp_forget`, `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar_obj_X`, `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar_obj_smul`, `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar_additive`, `AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteLimits_lowerStar`.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`; `AlgebraicGeometry.ProEtale.HasFiniteConstantLocalModel`, `AlgebraicGeometry.ProEtale.IsFiniteConstantStratified`, `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`, `AlgebraicGeometry.ProEtale.ConstantModelConstructible`, `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible`, `AlgebraicGeometry.ProEtale.ConstantModelBoundedConstructible`, `AlgebraicGeometry.ProEtale.ConstantModelConstructibleFiniteTor`.
- `def-sfb-qcqs-open-closed-tree`: `Sheaf.Paper.QcqsOpenClosedTree`; `AlgebraicGeometry.ProEtale.QcqsOpenClosedTree`, `AlgebraicGeometry.ProEtale.QcqsOpenClosedTree.Path`, `AlgebraicGeometry.ProEtale.QcqsOpenClosedTree.Path.toRoot`, `AlgebraicGeometry.ProEtale.QcqsOpenClosedTree.Path.IsLeaf`, `AlgebraicGeometry.ProEtale.QcqsOpenClosedTree.Path.extension`.

Mathlib's `ShortComplex`, `ShortComplex.homology`, and its abelian homology interface
are used directly. The generic `Functor.rightDerivedPullback` is read in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`.
Every proof-dependency module that already has a recorded module is imported privately;
unstated proof dependencies are preserved in the proof docstring for stage 3.

### Edge cases

- Empty T: both the pair and every support-chain vertex are empty; no Nonempty hypothesis.
- Empty S in a nonempty T: allowed by the tree and module definitions, and its extension is zero.
- r=0: `Path.root (QcqsOpenClosedTree.leaf T)` has `extension Λ = 𝟭 _` by definition.
- Zero coefficient ring A: `Finite A` and the annihilation clause allow it; MonObj is not required nontrivial.
- Zero terms, zero maps, and identity maps: all are allowed ShortComplex data when the composite is zero. There is no exactness or monomorphism hypothesis on b or c.
- Different P_i on each cover member and different covers for the three terms: all allowed by the separate existing local-model predicates.
- Original closed t with non-quasi-compact complement: allowed; t is not a path constructor.
- Finite discrete, integral, rational, and all-continuous Omega coefficients: separately retained; no completion or finite-field descent is assumed of N or of Omega-valued sections.

### Searches performed

- msearch.py LeanFinder: “A closed immersion inducing cohomology isomorphisms for every torsion etale sheaf induces derived restriction isomorphisms for supported three term scalar local model complexes”. Eight hits (open-immersion restriction and unrelated complex restriction isomorphisms); none states this item.
- msearch.py LeanSearch: “closed immersion torsion etale cohomology rigidity supported module homology”. Eight hits, all generic closed-immersion declarations; no rigidity theorem.
- msearch.py Loogle: `ShortComplex.homology, IsIso` returned unknown identifier `ShortComplex.homology` and zero hits. Retried with the qualified `CategoryTheory.ShortComplex`, which returned its genuine structure, projections, and morphism category. This is the chosen three-term encoding, not a match for the item.
- msearch.py grep: `rigidity|SupportChain|supportChain` in Mathlib/AlgebraicGeometry returned zero hits. `supported_three_term|torsionRigidity|QcqsOpenClosedTree` across Mathlib also returned zero hits.
- msearch.py LeanFinder: “Finite chains of open and closed immersions with compact open complements and composite extension by zero and direct image” returned eight unrelated scheme/gluing declarations. Loogle `Quiver.Path` returned the generic path type and its operations; it does not supply the required scheme edge conditions or module operations.
- `tools/blueprint_refs.py search 'support chain'` returned zero blueprint matches. `ancestor` returned det-sf-comp-coherence-cocycle. DAG and Sheaf searches then located def-sfb-qcqs-open-closed-tree, reused above.
- `rg` of upstream WeilConjectures for `lem-sfb-supported-three-term-scalar-rigidity` found no declaration. Corresponding Sheaf search found only the proof-plan citation in ClosedTorsionRigiditySerreTransfer. Broader searches for support chains and closed restriction found that module's canonical maps, ProperWContractibleClosedFibreRigidity, and the existing tree-path extension, all inspected. None already states this item.

No STATEMENT-DISPUTED claim and no statement correction: the reference-WANTED status
is inherited from the accepted agent-extracted statement and its proof, not concealed.

### Validation

`scompile.py Q19 lem-sfb-supported-three-term-scalar-rigidity` compiled the delivered
module in both sandbox and library mode (13.2 s and 7.8 s) with no errors or unexpected
warnings. The first probe needed an explicit type ascription for the section natural
transformation; that was repaired. `autoImplicit false` is enabled. No diagnostics,
local notation, private definitions, local instances, or proven theorem bodies remain.

## Second reading by Q19

I reopened the complete node, compiled signature, and the definitions of Path.extension,
HasFiniteConstantLocalModel, ShortComplex and homology, and rightDerivedPullback for a
separate second pass. The dispatcher explicitly forbids starting other agents, so this
is a self-audit; the maintainer's independent delivery review is still required.

The two points most likely to alter the claim were checked explicitly: the current
admissible-coefficient predicate has an extra coefficient case and therefore is not used
as a hypothesis; the support path is not required to be a leaf and its extra siblings
place no additional condition on the original chain, as the construction above shows.
Each of hL₁,hL₂,hL₃ binds its own cover; no shared P or matrix is introduced. The restriction
uses actual module-derived sections and the exact pulled-coefficient inverse image;
there is no arbitrary arrow, equivalence, completion assumption or hollow data. Naturality
comes from the constructed natural transformation and functorial short-complex homology.
No further mismatch was found; the sole elaboration repair was the explicit type
ascription, with the same canonical map before and after.
