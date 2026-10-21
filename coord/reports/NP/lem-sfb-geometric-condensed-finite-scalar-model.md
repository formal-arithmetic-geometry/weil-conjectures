## Worker report

The delivery states `AlgebraicGeometry.ProEtale.GeometricFiniteScalar.geometric_condensed_finite_scalar_model`
in `Sheaf.Paper.GeometricCondensedFiniteScalarModel`. Its proof is `sorry`; no proof of the
item is attempted. The definitions contain actual data. The source is the current
main-20261015 direct-images proof, paragraph (3), together with this node's reviewed
seven-step structural expansion. The literature obligation marked WANTED in the node
remains WANTED; the delivery does not claim to discharge it.

Hypotheses and objects, read against the complete node:

- The prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The field k, its specified separable closure ks, and their embedding are the explicitly
  declared `(k ks : Type u) [Field k] [Field ks] [Algebra k ks] [IsSepClosure k ks]`.
  The group is literally `ks ≃ₐ[k] ks`, with the existing Krull topology from Mathlib.
- Positive characteristic p different from ell is `(p : ℕ) [Fact p.Prime] [CharP k p]`
  and `(hpℓ : p ≠ ℓ)`. A positive field characteristic is prime, so this excludes no case.
- X/k is the specified `(X : Scheme.{u}) (a : X ⟶ Spec (.of k))`. Finite type is
  `[LocallyOfFiniteType a] [QuasiCompact a]`; separatedness is `[IsSeparated a]`.
  No properness, smoothness, geometric connectedness or nonemptiness is assumed.
- The algebraic closure is an arbitrary `(Ω : Type u) [NormedField Ω]`
  `[NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]`. NormedAlgebra extends the ground norm:
  `norm_algebraMap` and `norm_one` give exactly equality of the ground norms. There is
  no completeness assumption and no replacement of Ω by its completion or PadicAlgCl.
- The specified embedded finite subextension is `(E : IntermediateField ℚ_[ℓ] Ω)` with
  `[FiniteDimensional ℚ_[ℓ] E]`. Its norm and topology are inherited from Ω.
- `finiteRing ℓ Ω E` bundles the existing continuous-function coefficient object A.
  `closureRing ℓ Ω` bundles this item's actual finite-subextension-valued ring C
  for the specified arbitrary Ω. `normRing Ω` bundles the existing all-continuous coefficient object B.
  `finiteInclusion ℓ Ω E` and `inclusion ℓ Ω` are the sectionwise inclusions, not variable
  ring maps or unspecified comparison isomorphisms.
- The geometric functors are the recorded `CondensedGalois.OrdinaryData.geometric.functor`
  and their ordinary `rightDerivedFunctor`. `GeometricData` fixes their underlying module,
  sections on all geometric profinite tests, and action of every variable Galois element.
  The categorical structures and functors are supplied existentially in `Assertion`;
  their existence is not an additional hypothesis on k, X, E or V.
- `CondensedGalois.Modules` uses the recorded point pullback `coefficientRing`.
  `extendOnScheme` is the existing `Mod.extendScalars` followed by its K-flat total
  `leftDerivedFunctor`, on these actual internal module categories.
- The bounded constructible input V is quantified inside `FiniteAssertion`, using the
  recorded `constantModelBoundedConstructible (finiteRing ℓ Ω E).X X V`, including its
  finite constant local model convention. No finite Tor-amplitude hypothesis is added.

Conclusions and specified arrows:

- Boundedness of K_A is `DerivedCategory.TStructure.t.bounded` of the geometric derived
  object in the equivariant category, before taking any arithmetic invariants.
- For every integer q, the family `m : ∀ q : ℤ, CohomologyModel ...` supplies a normed
  finite-dimensional E-vector space W and an E-linear G-action. `continuous` is joint
  continuity on G times W. `sections` is an additive equivalence with C(P,W) for EVERY
  profinite P. `restriction`, `scalar`, and `action` make it the actual equivariant
  condensed E-module: scalar compatibility is tested on canonical presheaf pure tensors
  in the sheaf tensor, and equivariance uses every continuous generalized G-element.
- `lo hi : ℤ` and `Subsingleton (m q).W` outside their interval express W_q = 0 there.
  This is zero as a vector space, independent of any particular choice of zero carrier.
- `Extension` normalizes equivariant derived scalar extension by the existing ordinary
  internal relative derived scalar extension after forgetting the action. Its unit
  equation requires the SAME standard scalar unit, not merely an underlying functor
  isomorphism. `internalAdjunction` and `schemeAdjunction` derive the existing
  `Mod.extendRestrictAdjunction` and use exact restriction termwise.
- `projectionComponent` is exactly the inverse hom-equivalence of the equivariant
  derived scalar adjunction applied to K_A of the scheme scalar unit followed by the
  recorded normalized geometric scalar-restriction comparison. `Projection.normalization`
  fixes every beta component to this actual morphism. The two final `IsIso` clauses are
  precisely beta_C and beta_B being invertible in their respective equivariant categories.
- `ScalarSystem.comparison` is the dependency's `ScalarData`, retaining its sectionwise
  and total-derived-unit normalizations. It is not an arbitrary natural isomorphism.
- `SchemeComposition.normalization` fixes the underlying sheaf map to the identity.
  `ActionComposition.normalization` fixes the action restriction coherence to the existing
  `Mod.comapComp`. Their derived comparisons are obtained term by term.
- `Square.gamma_normalization` defines gamma by transposing the composite scalar unit;
  on K-flat representatives it is z tensor v mapped to c(z) tensor v.
- `schemeChange` is the corresponding scheme scalar-unit transpose.
  `Square.kappa_normalization` is K_C applied to that arrow followed by the dependency's
  same geometric scalar-restriction comparison. Thus it is exactly the specified kappa.
- `Square.commutes` asserts gamma followed by restricted beta_B equals beta_C followed
  by kappa, in D(A_G(C)), for each bounded constructible V. Applying the exact restriction
  to A to this equality gives the stated further-restriction clause without changing arrows.
- Naturality is encoded by the actual natural transformations in `Projection` and `Square`.
  Their `NatTrans.CommShift` fields give compatibility with shifts. The extension shift
  structures are the unique ones induced by their adjunctions from exact restriction,
  via the existing `Adjunction.leftAdjointCommShift`, not freely chosen structures.
- Nothing asserts an isomorphism or flatness of C_X to B_X. All categories and tensors
  are ordinary unbounded derived categories and internal relative derived tensors.

Recorded statement dependencies used:

- `Sheaf.Topology.ProfiniteCondensedRing`, `Profinite.CondensedRing`.
- `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.Mod`, `ModObj`, module morphisms.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded ordinary
  total-derived convention; the canonical upstream `Functor.rightDerivedFunctor` is used
  on the Grothendieck categories as the dependency's record explicitly permits.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`: the recorded ordinary
  K-flat relative tensor framework. The actual coefficient-change functors use
  `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars` and its underlying
  `Mod.extendScalars`/`Adjunction.derivedAdjunction`, with exact scalar restriction.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `coefficientRing`,
  `condensedRingObj`, `upperStarFromPoint` and transported commutativity.
- `sk-def-sfb-qlbar-condensed`: its live attachment remains exactly
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
  `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj`,
  `Profinite.padicAlgClSubfunctor`, and `Profinite.padicAlgClRingPresheaf`.
  The canonical PadicAlgCl dependency is imported and is not rebound. For the arbitrary
  Ω quantified by this item, its owning module supplies
  `GeometricFiniteScalar.FiniteSubextension.ringSheaf`, `ringObj`, `inclusion`, and
  `finiteMap`, with sectionwise constructions and precomposition restrictions.
- `Sheaf.Topology.ContinuousMapCondensedRing`, the general continuous-map sheaf and
  ring-object convention. The existing `continuousCoefficientRingSheaf` and
  `continuousCoefficientRingObj` give its same-universe continuous-function construction.
- `Sheaf.Paper.CondensedConstantConstructibility`, `constantModelBoundedConstructible`.
- `Sheaf.AlgebraicGeometry.CondensedGaloisGlobalDescent`, `Modules`, `OrdinaryData`,
  `GeometricData`, `CoefficientComparison`, `ScalarData`, `restrictX`, and their
  standard localization-universe instances. Existing `CondensedBar.ScalarAction` and
  `ActionAbelian` are reused through this recorded dependency.

All available recorded proof-dependency modules are imported privately. The field-action
transport and supported-lattice projection nodes have no recorded Lean module at this
reading, so they are named in the proof docstring but cannot be imported. The qcqs-over-affine
node is a Mathlib match already provided by the imported scheme-morphism framework.

Edge cases checked by reading the definitions: zero input, empty X, trivial G, rank zero,
negative q, empty profinite parameters, and the case E = Q_ell. Empty parameters have their
unique continuous function; no nonemptiness or basis of positive rank is required. W can
be zero in every degree. Neither interval endpoint is fixed uniformly across V. No finite
cohomological dimension of G is assumed. The ambient universe includes k, ks, X and Ω;
ordinary derived localization morphisms remain in u+2, rather than silently using the
smaller default specialization of the module-scalar adjunction API.

Searches made before defining the interfaces:

- msearch.py LeanFinder: "Geometric pro etale cohomology finite dimensional continuous l adic
  representations and normalized scalar extension comparison". Eight hits, including
  Hilbert 90 and Kaehler/formally-etale scalar results; no geometric condensed comparison.
- msearch.py Loogle: "Condensed, DerivedCategory, IsIso". Zero hits; diagnostic unknown
  identifier IsIso. This failed identifier query is recorded as such, not as evidence of
  absence on its own.
- msearch.py grep: "geometric.*scalar|scalar.*geometric", Mathlib/Condensed. Zero hits.
- msearch.py LeanSearch: "Finite dimensional geometric pro etale l adic cohomology continuous
  Galois representation scalar extension to algebraic closure norm topology". Eight hits:
  norm extension to PadicAlgCl/PadicComplex, restriction of multilinear maps, norm/Galois
  identities and cyclotomic continuity, with no statement matching this node.
- rg over WeilConjectures and Sheaf for the item id, GeometricFiniteScalar, the declaration
  name and finite_scalar_model: no existing statement; NormAlgclCohomologyTopologyComparison
  only cites this node in its proof plan and states a different, arithmetic comparison.
- rg over the coefficient sources: the existing finite-subextension construction and maps
  are specialized to PadicAlgCl. The generic continuous-function sheaves already exist;
  those are reused. The arbitrary-Ω finite-subextension ring is now owned by the item,
  as expressly permitted in the return; it does not replace the shared dependency.
- The full recorded dependency signatures and docstrings were read. Compiler #check probes
  confirmed the actual universe order of leftDerivedFunctor and derivedAdjunction, and
  diagnosed the smaller specialized Mod-derived adjunction instead of imposing a universe
  equality. The delivered file contains no diagnostic commands or development pp options.

The unchanged stage-1 statement and its full proof are preserved. There is no statement
correction, new definition node, dependency repair, or STATEMENT-DISPUTED claim.

## Repair of the returned delivery

The return of immutable head `7f3441a31a06` identified H13/H4: the shared
`sk-def-sfb-qlbar-condensed` attachment had been replaced by an NP generic construction,
dropping the canonical declarations used by live consumers. This is repaired using the
return's explicit alternative, “keep arbitrary Omega with the construction in the item
module ... record unchanged.” The saved packet's initial mechanical dry run passed at
`edca9117858`; that did not discharge this semantic review finding.

- The dependency node copy is byte-identical to the current live file, including the
  Q83 `existing: true` record and all four `Profinite.padicAlgCl*` declarations.
  The repaired delivery makes no change to that node.
- The separate dependency module `FiniteSubextensionCondensedRingOfUniverse.lean` is
  removed from the packet. Its needed arbitrary-Ω construction is now in the item's
  module under the owned namespace
  `AlgebraicGeometry.ProEtale.GeometricFiniteScalar.FiniteSubextension`. All sixteen
  helpers are listed in the item's `lean.declarations`, with item source/blueprint
  docstrings. No shared dependency declaration or record is removed or redefined.
- The arbitrary Ω, norm topology, specified embedded E, and all previously checked item
  clauses are retained verbatim. This takes the expressly permitted generic option,
  rather than narrowing the statement to the chosen PadicAlgCl model. The live parent
  `NormAlgclCohomologyTopologyComparison.lean` continues to use `padicAlgClRingObj` and
  its existing canonical sectionwise inclusion; neither it nor its coefficient identity
  is changed by this packet.
- The advisory about the descent interface is addressed by retaining `GeometricData`
  through `OrdinaryData`, and `ScalarData`, with the same sections, restriction, scalar,
  action, comparison, and derived-unit normalizations checked in the returned review.
  The private imports are the recorded available proof dependencies, as required by
  brief-stage2 §3 and stages/2-statements §3.7; no independent proof-only import is added.

The finite-valued helper properties remain named postponed theorems, each with its
natural-language proof: `finiteIntermediateFields_directed`, `finiteValued_closed`,
`finiteValued_comp`, and `isSheaf_ringPresheaf`. They state the directed-compositum,
pointwise subring, restriction, and sheaf clauses of the coefficient construction.
The item theorem is the fifth and final postponed theorem. All actual coefficient data
and the canonical maps are fully constructed. There are no additional mathematical
hypotheses and no new DAG node.

## Second reading by NP

This is a second pass by the repairing worker; no additional agent was started, as the
dispatcher forbids it. I reopened the returned finding, live dependency node and its
upstream `EllAdic` and `FiniteSubextension` declarations, live parent module, full item
node and final Lean module. The source remains main-20261015 direct-images paragraph
(3), with the item node's seven-step structural expansion.

Hypotheses still match one for one: prime ℓ; fields k and ks with their specified algebra
and separable closure; prime positive characteristic p distinct from ℓ; separated finite
type a; arbitrary normed algebraic closure Ω with extending norm; embedded finite E.
The full Ω quantifier and the absence of completeness are retained. The coefficient
helpers construct exactly the displayed finite-image section set, its pointwise operations,
precomposition, and the inclusions A → C → B. They are now owned by this item, while the
shared dependency record stays byte-identical to live.

The remaining clauses are unchanged: `FiniteAssertion` quantifies every bounded constant
model constructible V; `t.bounded` is before invariants; `CohomologyModel` pins all sections,
restrictions, E-scalars, and generalized G-actions of H^q to C(P,W_q), with joint continuity
and vanishing outside lo..hi. `Extension.unit`, `Projection.normalization`,
`Square.gamma_normalization`, and `Square.kappa_normalization` pin the actual derived
arrows. Both beta components are invertible, and `Square.commutes` is equality in the
C-equivariant derived category; exact further restriction gives the A-equality. Actual
natural transformations and their canonical adjunction-induced `CommShift` instances
supply naturality and shifts. Empty X, zero V, zero W, empty profinite parameters, trivial
G, negative degrees, and E = Q_ell remain permitted. The earlier dependency reattachment
was the mismatch found in this repair; its only necessary changes were restoration of
the node, relocation/ownership of the generic helpers, and the corresponding declaration
list and report. All item fields other than `lean` equal the current live node.

## Validation

The repaired single module compiled cleanly through scompile.py against the live
published build in both wrapper modes: sandbox 44.5 s and library 37.2 s. There were
no errors or warnings beyond the permitted postponed proofs. Static self-checks confirm
the exact theorem signature in lean.statement, line lengths at most 100, all explicit
binders, only lean changed on the item, and byte equality of the restored shared node.
The repaired packet passed deliver2.py --no-push at `94b1724545a`: preflight and
per-file compilation OK. The staged set contained exactly the item module, item node,
and this report; the shared dependency node and removed module were absent from the
changes. The initial retained packet passed its dry run but contained the semantic
finding repaired above.
