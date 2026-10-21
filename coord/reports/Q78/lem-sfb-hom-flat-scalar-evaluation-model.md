## Worker report

The module `Sheaf.Algebra.Homology.FlatScalarEvaluationModel` states
`CategoryTheory.FlatScalarEvaluation.model_exists`. Its conclusion is the
simultaneous existence of `Model M μ Θ`, whose component structures spell out
the actual chain-generator formulas, their derived transposes, descent along
every resolution, and both chain and derived coefficient-square equations.
The only postponed theorem is `model_exists`, with proof `sorry`; its docstring
contains all eleven steps of the node's proof. Every auxiliary definition has
actual data, and all structures have explicit fields.

The node's hypotheses and clauses correspond to Lean as follows.

- Site and sizes: `{C : Type c} [Category.{v} C]`, `J`, coefficient and module
  universe `max c v r`, and independent derived morphism universe `w`.
  `HasSheafify`, `WEqualsLocallyBijective`, `HasSheafCompose`, and the family of
  `HasDerivedCategory` instances provide the recorded site/module/localization
  interfaces; no equality of site object and arrow universes is imposed.
- Rings and coefficient maps: every field binds the relevant
  `R S : Sheaf J CommRingCat.{max c v r}` and `a : R ⟶ S`.
- Ordinary and derived extension and restriction: `M.scalar a` is the recorded
  normalized `ScalarDerivedPair`; `extension M a` applies its ordinary functor
  termwise, and `StrictScalarHom.restriction`/`scalarDerivedRestriction` are the
  recorded actual restrictions. Ordinary exactness is
  `PreservesFiniteLimits (M.scalar a).extension`; the ordinary scalar adjunction
  already supplies the colimit preservation, so this expresses exactness.
- Unbounded localization: every `[f]` is `DerivedCategory.Q.map f`; objects are
  `Q.obj D`. There is no boundedness predicate anywhere.
- Closed structures and simultaneous normalized tensor comparisons: explicit
  parameters `M : ScalarHomModels J`, `μ a : ScalarHomTensorComparison M a`, and
  `Θ : ScalarInternalHomAdjunction M μ` reuse the recorded declarations.
- Flat-term K-flat P: `IsKFlatIndependentCoefficients P` and
  `∀ n, IsFlatOnSite (P.X n)` in `Calculation`. The target I is the node's J:
  `I.IsKInjective`. D is an arbitrary `StrictScalarHom.Complex R`, and b is
  literally `D ⟶ homComplex (R := R) P I`.
- Chain evaluation tilde-b: `Representatives.evaluate` and `evaluate_pure`
  specify its value on every actual `coefficientTensorGenerator`, using
  `StrictScalarHom.evaluate` (product projection, then identity of the slice).
  The integer equations explicitly retain tensor order D,P.
- Beta: `transpose M D P I i f` is the closed derived transpose of `Q.map f`
  using the canonical one-factor tensor representative `i`. In particular the
  beta used in `adjunctionEvaluation` is the node's transpose of tilde-b.
- A = S tensor D: `StrictScalarHom.tensor a` is the existing termwise tensor
  with the restricted regular S-module. `Representatives.nu` and `nu_pure`
  give its canonical identification with UED, fixed on sheafification-unit
  generators. `extensionSection` is s times the normalized scalar unit, hence
  the actual s tensor x section, rather than an unspecified generator map.
- Exact-extension representative identification: `representative` is the
  actual universal derived counit; `exact_computes` asserts its invertibility
  on every complex under exactness. `exactRepresentative` uses `asIso` of this
  very map and the recorded restriction factorization. Its proof input cannot
  select a different map. `sourceTransport` also includes Q(nu).
- The representative formula: `scalarEvaluate` and `scalarEvaluate_pure` say
  exactly h_b((s tensor x) tensor p) = s tensor b(x)(p), in every homogeneous
  summand and on every object of the site. `extendedEvaluation` explicitly
  composes the source identification, scalar-unit tensor map `unitTensor`,
  inverse strong tensor comparison, and UF applied to Q(tilde-b).
  `Calculation.derived_formula` identifies that map with Q(h_b).
- The tensor comparisons do not assume D or A K-flat: `tensorIso` quantifies
  over every D, and `tensorIso_natural` over every chain map. Its equality to
  the specified K-flat comparison is `tensorIso_normalization`; thus this is
  the canonical extension of the existing comparison, not a new tensor.
  In particular D = Hom(P,I) is admitted without an extra hypothesis.
- Descent and independence: `Calculation.resolution` quantifies over EVERY
  flat-term K-flat V and quasi-isomorphism t : V ⟶ D. It asserts QuasiIso for
  Et, t tensor 1_P, E(t tensor 1_P), and the scalar first-factor map tensor
  1_P used for cancellation. Its final equality is the node's actual chain
  descent square, with nu, `chainUnitTensor`, the inverse
  `(μ a).complexIso V P`, and restricted extended evaluation. Each resolution
  descends to the same `scalarEvaluate a P I D b`; none is selected.
- Theta transpose: `adjunctionEvaluation` uses the existing
  `coefficientBaseChangeHom` for c, then U(c), then the component of Θ, and
  applies the inverse closed transpose. `Calculation.adjunction_formula`
  equates this map, with precisely the same representative transports, to
  Q(h_b).
- Arbitrary derived inputs and morphisms: `DerivedCoherence.naturality`
  quantifies over arbitrary K,L,K',L',f,g in the derived category. Hence
  inverses of localized quasi-isomorphisms and their composites are included;
  no requirement that a derived map lift to a single chain map is present.
- Coefficient towers: `DerivedCoherence.composition` is the actual equation
  F_b(c_a);c_b;Hom(comp_K inverse,comp_L) = comp_H;c_(ab), using the recorded
  unit-normalized `scalarHomExtensionComp` and both Hom-input transports.
  The equation in fact needs no exactness, as step 9 of the proof explains.
- Identity: `DerivedCoherence.identity` gives c_id = identity under
  `scalarHomExtensionId`, including its source and both Hom inputs.
- Compatible coefficient squares: `squareTransport` is exactly the composite
  of the two recorded extension-composition isomorphisms, with equality
  transport for φ;d = a;φ'. `DerivedCoherence.derived_square` equates the two
  successive Hom-comparison paths with the corresponding transports.
  `ChainPresentation` reuses `StrictScalarHom.Data`; `chainIso_pure` fixes
  the bridge to M's ordinary extension on generators. `ChainSquare` asserts
  the actual chain h equality on both coefficient routes, using the existing
  `CoefficientSquare`, `CoefficientCompatibility`, restriction mate, tensor
  comparison and Hom comparison. It explicitly extends b by E_a(b) and the
  strict Hom comparison. Evaluating the two routes gives
  φ'(r')d(s) tensor (1 tensor b(x)(p)). All squares, including identities and
  successive squares, are quantified over, without flatness assumptions.
- No finite freeness, finite product, filtered continuity, or boundedness
  assumptions appear. The order of evaluation is first factor then P, with
  no unrecorded symmetry or homogeneous sign change.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  (through the recorded `scalarModules` abbreviation).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`:
  `CoefficientClosedStructure`, its tensor/evaluation/transpose,
  `coefficientTotalTensor`, `coefficientTensorGenerator`,
  `CoefficientTensorModels.iso`.
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`: the actual Hom
  product projections and representative evaluation convention.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `DerivedChangeOfRingsCochainModel`, its universal pair and canonical counit.
  M's `ScalarDerivedPair` retains this same mathematical interface.
- `Sheaf.Algebra.Homology.ScalarInternalHomData`: `ScalarHomModels`,
  `ScalarDerivedPair`, `ScalarHomTensorComparison`, `scalarComplex`,
  `scalarPairComplexComparison`, `scalarDerivedRestriction`,
  `scalarRestrictionComparison`, `scalarHomUnitSection`,
  `scalarHomRestrictionTensor`, `scalarHomExtensionComp`,
  `scalarHomExtensionId`, `ScalarInternalHomAdjunction`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective` (the dependency's exact Mathlib match).
- `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`:
  `scalarInternalHomAdjunction_exists`, the recorded evaluation normalization.
- `Sheaf.Algebra.Homology.StrictScalarHomChain`: the `StrictScalarHom`
  Complex, tensor, tensorSection, evaluate, restriction, Data,
  CoefficientSquare, and CoefficientCompatibility interfaces.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `WeilConjectures.coefficientBaseChangeHom`, exactly the general
  evaluation-defined c required here; no private duplicate is introduced.

Proof-only imports retain the already stated resolution, quasi-isomorphism,
scalar-adjunction, tensor-coherence and exact-functor proof plan. The proof
nodes `lem-sfb-hom-kflat-chain-transpose` and
`lem-sfb-scalar-hom-chain-coefficient-coherence` have no Lean record in this
checkout; their ids remain in the proof docstring and DAG, but there is no
nonexistent module import. No missing statement notion is left: the relevant
one-factor comparison and coefficient equations are explicitly stated here
as clauses of this item's full assertion, using the already recorded data.

Edge cases checked before and during the statement audit: D = 0, P = 0,
I = 0, zero coefficient sheaves, identity coefficient maps, arbitrary
unbounded Hom(P,I), non-K-flat D and A, inverse quasi-isomorphisms, arbitrary
integer degrees (including degree zero), and identity/composite coefficient
squares. None requires an additional hypothesis. In particular Z → Q and
D = Z/2 is allowed (extension is zero on D); the formulas continue to agree.
The site object and morphism universes remain independent. The scalar tensor
comparison's normalization, rather than exactness of D, justifies descent.

Searches made (2026-10-21):

- msearch.py leanfinder, query `Scalar extension of evaluation with one K-flat
  tensor factor and arbitrary unbounded first complex`: eight hits, including
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat and Module.Flat tensor
  exactness lemmas. None states this ringed-site complex/derived assertion.
- msearch.py loogle, query `Functor.IsLeftDerivedFunctor,
  Adjunction.homEquiv`: no hits (unknown unqualified identifier). Refined
  query `CochainComplex.IsKInjective`: twelve hits including the exact
  K-injective predicate and its invariance lemmas; reused the predicate.
- msearch.py grep, query `scalar.*[Ee]valuation|flat.*[Hh]om`, Mathlib
  Algebra/Homology: zero hits.
- rg in both project roots for scalar evaluation, flat scalar, and the item
  id: no existing declaration of this assertion. Nearby
  `FlatInternalHomEvaluationRoof` specializes a different roof, and
  `ScalarHomComparisonTower` states only derived coherence; neither includes
  arbitrary-first-complex chain evaluation and descent. The existing general
  `coefficientBaseChangeHom` is reused for c.
- Read the item and all statement-dependency records and their declaration
  modules, plus the applicable proof-dependency interfaces. Read Stacks
  sites-cohomology.tex at labels lemma-pullback-tensor-product (07A4) and
  lemma-internal-hom (08J9), and the current blueprint
  main-20261015/blueprint/sec-six-functors-basics/
  sk-def-sfb-dc-restricted-functors/lem-sfb-dc-hom-preserves.proof.md.

No statement correction, new node, dependency repair, or disputed statement
is required. Only the item's lean record is changed.

## Second reading by Q78

This is a separate self-audit by the single dispatched worker, not a claim of
an independent second agent; the maintainer supplies the independent review
as specified in the dispatch. With the node and final module open, I checked
the hypothesis/clause correspondence above, in particular both representative
transports in extendedEvaluation and adjunctionEvaluation, unrestricted D and
A, the four explicit descent quasi-isomorphisms, the orientation of inverse
scalar tensor comparison, and all source and Hom-input transports in towers
and squares. The first draft's unqualified Complex conflicted with another
import; it now uses the dependency's fully qualified Complex. Implicit
universe inference in restriction/tensor applications was replaced by
explicit levels. Repeated elaboration of a single large structure was
reduced by packaging the identical formulas into Representatives,
Calculation, ChainPresentation, ChainSquare and DerivedCoherence. These are
only packages of the same assertion; no hypothesis or equation was removed.
