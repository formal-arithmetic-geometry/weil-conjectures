## Worker report

The module `Sheaf.Paper.IntegralPointTransportTowerRealization` states
`WeilConjectures.integralPointTransportTowerRealization`, with one postponed proof.
Its six helper declarations only assemble existing functors and the existing 1-s
endomorphisms; their data contain no sorry. There is no statement correction or
new DAG node. The representation uses common flat-term K-flat complexes and the
actual strict quotient transitions, rather than a sequence of unrelated derived
objects or a choice of a morphism with prescribed reductions.

Source read: `literature/blueprint/main-20261015/blueprint/sec-trace-formula/`
`sk-d-weil/prop-trf-rational-frobenius-integral-model.proof.md`, clause (3),
together with the item's six explicit proof steps. The source says that the
integral operators are derived limits on morphisms. This node isolates the point
transport needed for that assertion.

Hypotheses and clauses, matched individually:

* The finite-field data p,a,q,k0,k are `D : FiniteFieldDatum.{u}`. The point is
  literally `Spec (.of D.k)`, and geometric Frobenius is the recorded
  `(frobeniusPointIso D).hom`. No independently supplied automorphism is used.
* The prime ell is `l : ℕ` with `[Fact l.Prime]`; the excluded characteristic is
  `hl : l ≠ D.p`. The field E has `[Field E]`, `[Algebra ℚ_[l] E]` and
  `[FiniteDimensional ℚ_[l] E]`. Its valuation ring, completion and positive
  quotients are exactly the Padic coefficient constructions used in the
  dependencies. Exponent n+1 is indexed by n : ℕ, so all positive levels occur.
  No choice of a uniformizer changes these quotient ideals.
* An object N of the stated derived-complete integral constructible category is
  rendered in the realization clause by a good representative P with
  `sfIntegralConstructible l E (Spec (.of D.k)) (DerivedCategory.Q.obj P.obj)`.
  `integralOperationsGoodComplex` means K-flat with flat terms. This is a
  representative convention, not a restriction on N: the recorded K-flat
  resolution theorem supplies one for every N. The last clause also quantifies
  directly over all N,N' of `sfIntegralConstructibleCategory` and every derived
  morphism f between them. Boundedness and uniform amplitude are inherited
  unchanged from `sfIntegralConstructible`.
* The coherent reduction tower is computed on that single P by
  `unrestrictedIntegralComplexFunctor` and `unrestrictedIntegralTransition`.
  `trfPointSourceTower` is their existing strict sequence, followed by termwise
  `pointIntegralSections`. These are quotient tensor products with restricted
  completed coefficient action. Thus its positive level is Gamma(s,N_n) with
  O_E scalars, using the K-flat computation of the reduction functor in
  `def-weil-pbc-adic-coefficient-datum`.
* `trfPointTargetTower` applies sections to the already recorded
  `integralOperationsPullbackTowerFunctor`, whose levels are exactly
  `Res_n g_n^*(P_n)` and whose transitions are fixed by the quotient-induced
  pullback generator formula. Every tower here is over one fixed integral
  module category, not a diagram of changing coefficient categories.
* `U : trfPointSourceTower ... ⟶ trfPointTargetTower ...` is a natural
  transformation of functors to strict towers of complexes. Consequently
  each `U.app P` commutes with every transition before localization. The first
  conjunct fixes every component on every degree and section: restrict by
  `frobeniusPointRestriction`, insert the finite pullback unit using
  `integralOperationsPullbackGenerator`, and restrict along
  `proEtaleIsoCommaArrow`. These are exactly `frobeniusPointFiniteSigma` and
  `inverseImageFiniteComparisonComplex`'s defining formulas, so the evaluated
  derived component is the finite transport of the recorded definition,
  after restriction of scalars. This clause fixes all sections, not just
  pure tensors or the reductions of integral sections.
* The source completeness identification is the map α from sections of P
  into `integralOperationsRoos` of the evaluated source tower. Its next two
  conjuncts require every unshifted product projection to be the actual
  `unrestrictedIntegralTensorSection ... 1 x`, and its entire shifted
  product component to be zero. Those two components determine the chain
  map uniquely. It is the canonical identity-extension completion unit
  expressed in the ordinary quotient presentation, not an arbitrary
  isomorphism arising from a Roos triangle. The realization clause asserts
  `IsIso (DerivedCategory.Q.map (α.app P.obj))` for all complete constructible
  good representatives.
* The target completeness identification first uses the actual
  `integralDerivedPullbackComparison`, then the exact-sections localization
  comparison, then `DerivedCategory.Q.map (β.hom.app P.obj)`. The natural
  isomorphism β identifies sections of the actual sheaf Roos cone with the
  Roos cone of the evaluated tower. The two conjuncts about β normalize
  both its unshifted and shifted nth product components to sections of
  the actual sheaf cone projections. These conditions determine the
  comparison without a choice of a triangle filler. Its other factors
  are already natural isomorphisms, so this is the claimed target
  completeness isomorphism.
* The displayed realization equality starts with the recorded
  `frobeniusPointTransportIntegral`, not an unspecified arrow. Its left
  side is beta after the actual integral point transport; its right side
  is alpha followed by `DerivedCategory.Q.map
  (integralOperationsRoosMap (U.app P.obj))`. Thus it asserts equality of
  derived morphisms including the cone's shifted component. The recorded
  integral transport uses precisely comparison (b) in
  `inverseImagePullbackComparison`.
* Naturality of the tower map and both normalized identifications is expressed
  by the natural-transformation binders U,α and the natural-isomorphism binder
  β. The normalized completed-pullback comparison is already natural on
  good representatives. These constructions descend across quasi-isomorphisms
  by the recorded resolving-class interfaces, so their naturality applies
  to roofs. The last conjunct explicitly asserts the corresponding square
  for the integral transport for every derived morphism f : N ⟶ N'. No
  invertibility of f or Frobenius structure on N is assumed.

Dependencies read and reused:

* `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions`, its coefficientField,
  coefficientRing and pointFibre. Only its coefficient conventions are needed;
  its auxiliary separated finite-type X0 datum is not an added hypothesis here.
  The module is read but not imported: its extra compact-support dependency
  acquired unrelated compilation errors during delivery. The exact underlying
  finite-field and Padic coefficient declarations used here are already publicly
  imported by FrobeniusPointTransport; no coefficient notion is copied.
* `Sheaf.Paper.SfIntegralConstructible`:
  `sfIntegralConstructible`, `sfIntegralConstructibleCategory`.
* `Sheaf.Paper.AdicCoefficientDatum`:
  `AlgebraicGeometry.Scheme.completedReductionTower`, its
  `IsCompletedReductionTowerPair` and K-flat quotient computation. The strict
  representative uses the already published unrestricted integral quotient
  functors rather than introducing another reduction definition.
* `Sheaf.Paper.FiniteCoefficientPoint`:
  `pointFibreIntegralAmbient`, `pointIntegralSections`, exactness instances
  and the recorded derived-functor factors.
* `Sheaf.Paper.DerivedPullbackTensorHom`:
  `finiteDerivedPullback`, `constructibleIntegralPullback`; the ambient
  `integralDerivedPullback` and its normalized comparison are supplied by
  the existing integral derived operations module.
* `Sheaf.SixFunctors.FrobeniusPointTransport`:
  `frobeniusPointIso`, `frobeniusPointRestriction`,
  `frobeniusPointFiniteSigma`, `frobeniusPointTransportFiniteComplex`,
  `frobeniusPointTransportFinite`, `frobeniusPointTransportIntegral`.
* `Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison`:
  `inverseImageFiniteComparisonComplex`,
  `inverseImagePullbackComparisonFiniteIntrinsic`,
  `inverseImageReductionTheta`, `inverseImageRoosComparisonComplex`,
  `inverseImagePullbackComparison` and their full section formulas.
* Proof imports are the recorded independent-coefficient K-flat resolution,
  integral-operations well-definedness, exact pro-etale products,
  derived-limit existence, exact point sections and finite-free completed
  scalar comparison (especially its normalized identity unit). No proof
  dependency import is omitted for an import cycle.

Edge cases checked before drafting and again against the signature: n=0 is
exponent one, not a missing positive level; every integer cohomological degree
occurs, including negative degrees; P and N may be zero; quotient modules may
have torsion and need not be flat; E may be Q_l itself; D.k0 may have any
positive extension degree; no nonzero map, automorphism of N or Weil structure
is assumed. The site is still object universe u+1 and morphism universe u;
module sections have the coefficient universe u+1. None of these is forced
onto an equal-universe site. Countable indexing is fixed only for the actual
adic quotient tower.

Searches actually run through msearch.py (group Q14 and this item):

* leanfinder: `sections point transport on a derived complete sheaf is the
  derived inverse limit of finite coefficient transport maps`. Eight hits,
  including SheafOfModules.Presentation.map_π_eq and global-sections limit
  facts; none state the specified transport realization.
* loogle: `CategoryTheory.NatTrans, CategoryTheory.Limits.PreservesLimit`.
  Zero hits.
* grep: `point.*[Tt]ransport|[Tt]ransport.*[Tt]ower` in CategoryTheory.
  Zero hits.
* leansearch: `derived complete Frobenius point transport coherent quotient
  tower realization`. Eight unrelated hits on comonad/Grothendieck transport,
  scalar towers and Witt Frobenius; no match.
* Direct rg searched the item's id and integral/point/tower realization
  patterns in WeilConjectures and lean/Sheaf. It found the existing integral
  point-transport definition but no realization theorem. Direct rg for all
  proposed declaration names in Mathlib, WeilConjectures and lean/Sheaf
  returned no collisions. Existing tower, cone and section constructions
  found by these searches are reused as the helper definitions' real data.

Validation: every delivered Lean file is compiled through the prescribed
scompile.py wrapper, under its unchanged single-file timeout. There is one
sorry, the entire proof of the named item theorem. No definitions contain
postponed data. Compiler errors encountered while drafting were fixed by
making the tower's K family explicit and repairing parentheses; no hypothesis
or mathematical clause was changed to solve an elaboration error.

No independent second worker was started, as required by this brief. The
maintainer performs the independent reading of the delivery.

The first delivery dry run passed. The final command then refreshed an unrelated
compact-support dependency and exposed instance failures for `openRestrictionMap`
and `completedPullMap` in `IntegralCompactSupportCoefficientData`. The unused
broad coefficient-conventions import was removed; its actual coefficient data
remain imported through the point-transport module. The statement is unchanged.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
