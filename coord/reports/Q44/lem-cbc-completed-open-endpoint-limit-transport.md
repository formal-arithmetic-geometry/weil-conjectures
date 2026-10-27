## Worker report

The module `Sheaf.Paper.CompletedOpenEndpointLimitTransport` states
`AlgebraicGeometry.Scheme.completedOpenEndpointLimitTransport`, with every theorem
proof postponed. Its auxiliary declarations construct the specified canonical
comparisons from the existing adjunctions, quotient augmentation, scalar map and
actual strict-tower pullbacks. No object or map is selected from a bare existence
of an isomorphism. Invertibility and naturality needed by a construction are named
theorems in the same node's module, with proof plans and the node's blueprint tag.
All 37 public declarations are listed in `lean.declarations`.

The source read is main-20261015,
`sec-six-functors-basics/sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md`,
especially its finite-reduction and final inverse-limit paragraphs, together with
the item's four explicit proof steps. The node statement and accepted split are
unchanged. No new node or dependency repair is required.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Noetherian adic datum with finite perfect positive quotients and torsion A/I | `{A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)`; the inherited `CompleteCoefficientDatum` fields give `noetherian`, `finitelyGenerated`, `quotientTorsion`, `quotientPerfect`; `quotientFinite` gives finiteness. |
| Completed coefficient sheaves and strict reduction tower | `d.completedRing T`, `d.derived T`, `completedReductionTower T d`; index `n : ℕ` means exponent n+1. |
| Cartesian open square, with j quasi-compact | `sq : OpenImmersionSquare v j' j u`, the two open-immersion instances and `[QuasiCompact j]`; the conclusion provides `hqc : QuasiCompact j'` by base change. The open instances duplicate only the proof-irrelevant fields already in sq. |
| Exact ringed extension by zero | `cbcEndpointOpen d j` abbreviates the existing `proEtaleRingOpenExtension` over `d.completedRing`; its existing exactness instances provide the derived functor. The chosen left adjoint is fixed up to unit-preserving unique isomorphism. |
| K intrinsically complete and j_!K complete | `K : d.derived U`, `_hK : cbcCompleteProperty d U r a ha K` and `_hJK` for the derived extension. `r`, `a`, `ha` explicitly give a finite generating tuple of d.ideal. `cbcCompleteProperty` uses the existing transported intrinsic Koszul completion unit, on the canonical representative. |
| Canonical quotient/open comparison | `cbcEndpointReductionInv` is the transpose of the reduced open unit using `d.reductionTowerPullbackIso`; `cbcEndpointReductionInv_properties` states invertibility and naturality in the full derived strict-tower category. `cbcEndpointReduction` is its inverse. |
| Q, C, M, H, N | Respectively `cbcEndpointQ`, `cbcEndpointC`, `cbcEndpointM`, `cbcEndpointH`, `cbcEndpointN`. These use `d.towerPull`, `exchangeTowerRes`, and the recorded constant-coefficient `StrictTower.G` and `StrictTower.J`. |
| Canonical a and d, scalar and finite-reduction comparisons | `cbcEndpointA` and `cbcEndpointD`, obtained from `exchangeResPull` and the quotient/open comparison, with all quotient transitions retained. |
| Identity-of-extension-presheaves e | `cbcEndpointScalarOpenInv` is the mate of `exchangeOrdinaryResPull`. Its named invertibility theorem identifies it with the inverse identity of extension presheaves after the unit-preserving slice identification; `cbcEndpointScalarOpen`, `cbcEndpointDerivedScalarOpen`, `cbcEndpointTowerScalarOpen` give the specified directions and exact localizations. |
| b = J(d)e_C | `cbcEndpointB` first applies tower e and then `StrictTower.J` to d. |
| Completed and constant total derived inverse limits | `completedRlim T (d.completedRing T)` and `completedRlim T (exchangeConstantRing T A)`. These remain different categories. |
| Exactly the normalized lambda, including strict augmentations | `cbcEndpointLimitMap F` is the mate of the identity constant-diagram comparison under the actual derived constant/limit adjunction. `CbcEndpointAugmentationNormalized` states its equation for every derived augmentation. `cbcEndpointScalarLimit_properties` and `cbcEndpointOpenLimit_properties` state invertibility and this normalization, explaining in their proof plans why it is exactly the resolution-normalized comparison of `exactProductFunctorStrictLimit`, transported from `ringedOpenScalarLimitCoherence`. |
| a-hat = L(a)lambda_r | `cbcEndpointSource`, a natural isomorphism, first scalar/limit comparison then limit of a. |
| b-hat = J(L(d)lambda_r)e | `cbcEndpointTarget`, a natural isomorphism, first derived scalar/open e, then J of scalar/limit comparison and limit of d. |
| Agreement with the completed-pullback endpoints | `AdicCoefficientDatum.completedPull` unfolds to reduction tower, tower pullback, completedRlim; hence the sources and targets of these isomorphisms are the actual completed pullbacks. `cbcEndpointA/D` are the specified finite-reduction/scalar endpoints rather than arbitrary isomorphisms. |
| Quotient completion units | `cbcEndpointReduction_augmentation` states the strict quotient/open augmentation equation. Together with `CbcEndpointAugmentationNormalized` for scalar restriction and both open functors and the unit-compatible `exchangeResPull`, this retains the actual completion units. |
| Endpoint pasting identity | The first conjunct of `completedOpenEndpointLimitTransport`: map of inverse completed-open lambda, then b-hat, equals scalar lambda at J C, then L(b), then inverse constant-open lambda. `≫` is Lean's order, opposite to the printed function-composition order. |
| Every theta and B_theta formula | The second conjunct quantifies over every arrow from Q to completed J C. B_theta is expanded as `(completedRlim ...).map theta ≫ ...inv.app C`; conjugation by a-hat inverse and b-hat equals limit of `a.inv ≫ r(theta) ≫ b.hom` followed by inverse constant-open lambda. |
| Naturality and no extra restrictions | All endpoints are natural isomorphisms of functors in K. The map is defined for every derived tower arrow theta and the identity holds for all of them. No open-unit-mate, etale-origin, common bound or evaluation-faithfulness assumption appears. Naturality follows from functoriality and those natural transformations. |

Dependency declarations read and used:

- `Sheaf.Paper.AdicCoefficientDatum`: `completedReductionTower`,
  `AdicCoefficientDatum.derived`, `.completedRing`, and quotient data.
- `Sheaf.AlgebraicGeometry.OpenImmersionSquare`: `OpenImmersionSquare` and its
  inherited `ChosenCartesianSquare`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact` and
  `quasiCompact_isStableUnderBaseChange`. Only quasi-compactness is required here.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`: `localizedSystemExact`
  and the unit-normalized `localizedSystemAdjunction` behind the ringed open API.
- `Sheaf.Paper.IntrinsicCompletionCompleted`: `IsCompletedIntrinsicallyDerivedComplete`;
  its publicly imported transport in `Sheaf.Paper.IntrinsicCompletion` supplies
  `IsDerivedCompleteIntrinsic`, used by the existing `cbcCompleteProperty` in
  `Sheaf.Paper.CompletedExtensionZeroComparison`. This is the same explicit
  Koszul fiber and unit under coefficient presentation equivalence.
- `Sheaf.Paper.PbcQbarCompletedPullback`: the recorded declaration is the rational
  common-stage specialization. For the ambient integral operation in this node,
  use its retained published integral interface `Sheaf.Paper.CompletedPullback`:
  `AdicCoefficientDatum.completedPull`, `.ordinaryToCompleted`, together with
  `.towerPull` and `.reductionTowerPullbackIso` from their public imports. No
  rational pair category or constructibility assumption is substituted.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `SheafOfModules.restrictScalars`,
  used by `proEtaleRingRestrictScalars` without a private scalar-restriction definition.
- `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`: `Towers`, `G`;
  `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`: `moduleJ`, `moduleJAdj`, `J`.
- `Sheaf.Paper.ConstantCompletionEquivalence`: `equivalence`, finite-reduction,
  quotient-transition and limit/unit comparisons. The actual site-universe
  specialization already provided by `Sheaf.Paper.StrictTowerExchangeMateNormalization`
  supplies `exchangeScalar`, `exchangeOrdinaryResPull`, `exchangeResPull`,
  `exchangeTowerRes`. These are used directly.
- `Sheaf.Paper.ExactProductFunctorStrictLimit`: `exactProductFunctorStrictLimit`,
  including its K-injective resolution formula and strict-augmentation clause;
  `Sheaf.Paper.RingedOpenScalarLimitCoherence`: `ringedOpenScalarLimitCoherence`,
  `cbcDerivedSquare`, `cbcDerivedTowerSquare`, `cbcTowerDerived`.

Edge cases checked before finalizing: the empty open (all extension objects and
maps are zero); identity bottom map and identity open (units and naturality,
without demanding definitional equality of chosen adjoints); K = 0 and theta = 0;
unbounded K and arbitrary derived roofs for theta; I = A (zero finite coefficient
rings and zero completed module category); I = 0 and an empty generating tuple;
no assumption that the ambient schemes are quasi-compact or quasi-separated.
Site objects retain universe t+1 and morphisms t, coefficient modules t+1; no
extra equality of site universes or independent small test universe is imposed.

Searches actually run (including the preserved interrupted-turn search log):

- LeanFinder: `Transport normalized derived inverse limit through restriction of scalars and extension by zero preserving quotient tower completion units`.
  Eight hits concern ordinary adic completion (`IsAdicComplete.StrictMono.of_comp_lift`,
  `AdicCompletion.congr`, etc.); no derived endpoint statement.
- Loogle: `CategoryTheory.NatTrans.naturality, CategoryTheory.Functor.map_comp`.
  No hits. Those generic functor identities alone are not this normalized theorem.
- Mathlib grep via msearch:
  `(derivedLimit|DerivedLimit|Rlim|rlim|inverseLimit).*(restrictScalars|RestrictScalars|extensionByZero)|(extensionByZero).*(limit|Limit)`.
  No hits.
- LeanSearch: `Canonical completed open endpoint comparisons transport every derived strict tower morphism through normalized scalar restriction inverse limits`.
  Eight hits on ordinary scalar restriction and adic completion, no match.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for the node id, `cbcEndpoint`,
  completed endpoint/limit and scalar/open patterns. No existing endpoint theorem.
  Existing etale scalar/open isomorphisms are on the etale module-sheaf categories,
  and do not state this pro-etale completed strict-tower normalization. The recorded
  pro-etale scalar/open coherence is reused rather than redefined.

Validation: scompile.py checked the module cleanly in both sandbox and library
module forms (49.4 s and 27.0 s). All lines are at most 100 characters. Variables
and universes are explicit and `autoImplicit` is false. There is no statement
correction or disputed statement.

## Second reading by Q44

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
