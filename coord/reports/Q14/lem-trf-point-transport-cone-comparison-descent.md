## Worker report

The module `Sheaf.Paper.PointTransportConeComparisonDescent` states this node in
five named postponed theorems. `reductionSectionModel_eq` exposes the definitional equality of the two existing
scalar-extension presentations; `augmentation_condition` is the chain-map
well-definedness clause in node proof step 1; `pullbackRoof_isIso` is the
invertibility assertion in steps 7--8; `pointTransportConeComparison` gives the
unconditional fixed-resolution assertions; `pointTransportConeComparisonDescent`
gives the conditional independence, natural transformation, and explicit roof square.
All theorem proofs are `sorry`. Every definition has actual data: aliases of the
published constructions, products, the zero-homotopy mapping-cocone lift, or composites
of the specified comparison isomorphisms. No object is chosen from bare existence.

Hypotheses and clauses, in the order of the node:

| Node text | Lean rendering |
| --- | --- |
| Finite-field datum p,a,q,k_0,k | `D : FiniteFieldDatum.{u}`, with the existing finite field and algebraic closure instances. |
| Prime ell distinct from p, finite E/Q_ell | `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. |
| O_E, uniformizer quotients A_n, n >= 1 | Existing `Padic.coefficientExtensionIntegers` and finite quotient constructions inside the recorded reduction functors. Natural index n means exponent n+1, so includes exponent one and every positive exponent. No uniformizer choice changes these quotient ideals. |
| s, geometric Frobenius g, completed sheaf R, exact Gamma | `Spec (.of D.k)`, `(frobeniusPointIso D).hom`, `integralTowerModules l E ...`, `pointIntegralSections l E D.k`; `sections` is its termwise extension with the canonical integral coefficient action. |
| Flat-term K-flat P | `P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory`. The existing predicate is exactly `IsKFlatIndependentCoefficients P` and `∀ i, IsFlatOnSite (P.X i)`. No boundedness or completeness is part of it. |
| P_n, r_n, t_n | The existing `unrestrictedIntegralComplexFunctor`, `unrestrictedIntegralTransition`, and `unrestrictedTowerUnit`; reduction is the same sheafified pure-tensor unit, presented as 1 tensor x by the published scalar-extension convention. |
| C_n = Res_n g_n^* P_n, v_n | `integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom`, constructed from `integralOperationsPullbackLevel` and `integralOperationsPullbackTransition`; the latter is specified by the finite pullback unit and coefficient reduction. |
| D_n, B_n over one integral ring | `reductionTowers` and `pullbackTowers`, obtained by the same `sections` functor on both towers. The codomain is module complexes over `ULift (Padic.coefficientExtensionIntegers l E)`. |
| H, both products, and H(u) | Existing `integralOperationsRoos` and `integralOperationsRoosMap`, with the actual shifted mapping cone and its diagonal product map; no new cone convention. |
| N and quasi-isomorphism q:P -> N | Arbitrary `N : CochainComplex (integralTowerModules ...) ℤ`, `q : P.obj ⟶ N`, `[QuasiIso q]`. |
| sigma, theta, and strict tower map u with augmentation equations | `frobeniusPointIntegralSigma`, `inverseImageReductionTheta`, `v : reductionTowers.obj P.obj ⟶ pullbackTowers.obj P.obj`, and `hv : ∀ n, sigma ≫ sections.map theta_n = reductionUnit ... n ≫ v.app (op n)`. Strict tower compatibility is part of `v`'s natural-transformation type. |
| a_P and theta-tilde with zero shifted coordinate | `augmentation` is `mappingCocone.lift` of `reductionProduct` with cochain `0`; theta-tilde is the existing `inverseImageRoosComparisonComplex`, itself the same zero-homotopy lift of `inverseImageReductionProduct`. |
| c_C is identity on both sectionwise product coordinates | `coneSections` reuses `CompletedStalk.sectionsRoos`. Its existing unique specification contains separate `roosFirst` and `roosSecond` equations in every degree and level. |
| Strict chain equality, including shifted product | First conjunct of `pointTransportConeComparison`: `sigma ≫ sections.map thetaTilde ≫ c_C.hom = augmentation ≫ integralOperationsRoosMap v`. This is equality of whole chain maps; it retains the zero shifted component, not just finite-level projections. |
| Ambient completed Lg^*, specified b_q | `integralDerivedPullback` and `integralDerivedPullbackComparison`; `representativeComparison N P q` first inverts the resolution under pullback, then applies that specified representative comparison, `sectionsFactors`, and the localization of `coneSections`. Its type is a derived isomorphism on the entire ambient category. |
| Actual kappa and iota | `frobeniusPointTransportIntegral D l hl E (DerivedCategory.Q.obj N)` is the recorded actual integral comparison followed by point sigma, not a freely supplied map. Its defining `frobeniusPointTransportIntegralComplex` uses `inverseImagePullbackComparison`, whose definition is the localized zero-homotopy theta lift after inverse-image(q) inverse and the specified pullback comparisons. |
| Gamma(q) invertible and sigma natural | Second and third conjuncts of `pointTransportConeComparison`: `IsIso` of derived sections of q and the full chain sigma square. |
| b_q iota_N Gamma(q) = [H(u)a_P] | Fourth conjunct of `pointTransportConeComparison`, in Lean's left-to-right composition order. `resolvedArrow` inserts the exact-sections localization comparison so its source is derived sections of [P]. |
| b_q iota_N = [H(u)a_P][Gamma(q)]^-1 | Fifth conjunct of the same theorem. The only inverse on the source is derived sections of q. |
| Conditional chain naturality of u(P) | In `pointTransportConeComparisonDescent`, `v` is a natural transformation between the two tower functors restricted to the existing good full subcategory. Its naturality is exactly the chain-map compatibility required by the node; `hv` gives its level augmentation equations for each good P. |
| Independence and naturality for arbitrary derived morphisms | The first conjunct of `pointTransportConeComparisonDescent` asserts a unique natural transformation from exact derived sections to completed pullback followed by sections, agrees on EVERY ambient derived object with actual integral point transport, and has the prescribed resolution formula for every N,P,q. The second conjunct explicitly equates the formulas from arbitrary P,P',q,q' over the same N. A change of complex representative is handled by the same natural transformation on the ambient derived category. |
| Every roof P <-a- Q -b-> P' with a quasi-isomorphism | Final conjunct quantifies all good P,Q,P', morphisms a,b, and `[QuasiIso a.hom]`. It asserts invertibility of T(a) and the equation `eta_P ≫ T(a)^-1 ≫ T(b) = S(a)^-1 ≫ S(b) ≫ eta_P'`, where T is the actual localized two-component Roos map and S is localized exact sections. `pullbackRoofIso` uses the actual T(a) as hom. |
| No derived completeness and no invertibility of a_P | Neither is a binder or assumption in any theorem. The definitions invert only resolution maps and the specified comparison isomorphisms. |

Dependency declarations used (read the declarations and their source docstrings):

- `Sheaf.Paper.TraceFormulaCoefficientConventions`: `TraceFormulaCoefficientConventions`
  fixes the same underlying finite-field/coefficient conventions; this statement uses
  just its field and coefficient datum, not its extraneous scheme or single level.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Paper.AdicCoefficientDatum`: `Scheme.completedReductionTower`,
  `completedReductionLevel`, and the actual quotient-coefficient conventions. For the
  Padic specialization the already recorded unrestricted reduction interface is reused.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived` publicly retains
  `AlgebraicGeometry.ProEtale.inverseImageReductionTheta`,
  `inverseImageRoosComparisonComplex`, `inverseImagePullbackComparison`, and the
  arbitrary-object `inverseImagePullbackComparisonDerived`.
- `Sheaf.Paper.IntegralOperationsWellDefined`: `integralOperationsGoodComplex`,
  `integralOperationsTowerStep`, `integralOperationsRoos`, `integralOperationsRoosMap`,
  `integralOperationsPullbackTowerFunctor`, `integralOperationsPullbackComplexFunctor`,
  and `integralOperationsWellDefined`.
- `Sheaf.SixFunctors.FrobeniusPointTransport`: `frobeniusPointIso`,
  `frobeniusPointIntegralSigma`, `frobeniusPointTransportIntegralComplex`, and
  `frobeniusPointTransportIntegral`; the Frobenius is the Spec of the same geometric
  field automorphism as `FiniteFieldDatum.geometricFrobenius` in
  `Sheaf.AlgebraicGeometry.FrobeniusDetailed`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`; canonical scalar action is the published
  `pointIntegralSectionMap` / `pointIntegralSections` it re-exports.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.PointProEtaleSectionsExact`: `point_proEtale_sections_exact` and
  `pointModuleSections`; the integral specialization is `pointIntegralSections`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback` is exactly
  the restriction of the ambient `integralDerivedPullback` used here. The recorded
  common-stage internal Hom declaration is not an alternative pullback definition.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices` publicly retains the global
  `integralDerivedPullback` and `integralDerivedPullbackComparison` from
  `Sheaf.Paper.IntegralDerivedOperations`. The recorded slice completed tensor is not
  substituted for ambient pullback.
- Proof imports: `ProEt.countableProducts_exact`, `frobeniusPointTransport_natural`
  (only ambient sigma naturality is used),
  `SheafOfModules.site_derived_tensor_descent_independentCoefficients`, and Mathlib
  `Localization.lift`, `liftNatTrans`, `natTrans_ext`.

Two already landed nodes were added to `stmt_deps`, under the explicit authorization
for reusing existing recorded helpers. They are not new nodes or dependency repairs:
`def-weil-integral-reduction-tower` provides `unrestrictedTowerUnit` and its finite
reduction complexes through `Sheaf.Paper.IntegralReductionTowerCanonical`;
`lem-trf-completed-stalk-reparametrization-coherence` provides the existing two-coordinate
`CompletedStalk.sectionsRoos`, `roosFirst`, `roosSecond`, and `moduleQ` from
`Sheaf.Paper.CompletedStalkReparametrizationCoherence`. A recursive DAG read found no
path from either added dependency back to this item. The local-Frobenius normalization
module, whose DAG DOES depend on this item, was deliberately not imported for its
similar helper. No statements, source/proof records, or existing dependencies changed.

Edge cases checked before writing: the zero complex gives the zero strict lift in both
coordinates; a complex concentrated in degree zero still has a genuine shifted product
coordinate, fixed by the zero cochain; exponent one is n=0; unbounded good complexes and
arbitrary incomplete N are retained. The flat localization R[1/varpi] has zero reductions
and zero a_P, so the theorem must not assert a_P invertible; it does not. Identity roofs
are included, as are noninvertible b and arbitrary quasi-isomorphism denominators a.
The coefficient prime is excluded only by hl, and no hypotheses of constructibility,
finite Tor-amplitude of reductions, or chain lifts between chosen resolutions appear.
Small-site object and morphism universes remain u+1 and u. Coefficients and sections
are in u+1, with the existing standard source localization and Grothendieck small-Hom
target localization related by the explicit `sectionsFactors` isomorphism.

Searches performed through the required `msearch.py` wrapper:

- `leanfinder`, query: `point transport comparison with the zero homotopy Roos cone
  lift descends through quasi isomorphism roofs`: eight generic hits including
  `CochainComplex.mappingCone.lift_desc_f`, homotopy-localization compatibility, and
  mapping-cone additive-functor comparisons; no specified Frobenius/adic comparison.
- `loogle`, query: `CochainComplex.mappingCocone.lift`: eight hits giving the lift and
  both coordinate equations; these are the infrastructure used by the existing lifts.
- `grep`, query: `mappingCocone.lift|mapHomologicalComplexIso`, subdirectory
  `Algebra/Homology`: fourteen generic cone/short-exact/Ext hits, no target theorem.
- `leansearch`, query: `specified point transport to completed pullback equals the
  zero shifted component homotopy limit cone map and is natural under derived roofs`:
  eight generic cone and shift hits; no match.
- `rg` in the project's `lean/WeilConjectures` and `lean/Sheaf`, by item id and names
  `pointTransportCone`, `PointTransportCone`, `sectionsRoos`, `RoosComparison`,
  `unrestrictedTowerUnit`: no existing declaration states this node. The search found
  the exact reusable section/cone comparison and reduction unit named above.

No statement correction, disputed statement, new node, or dependency module is needed.
The only node deltas are the Lean record and two added landed statement dependencies.

Compilation diagnosis exposed an expensive implicit comparison between the independently
published `unrestrictedTowerComplex` and `unrestrictedIntegralComplexFunctor` presentations.
`reductionSectionModel_eq` states their definitional equality after sections, with the
complete unfolding proof in its docstring. `reductionUnit` is the PUBLISHED reduction unit
followed only by `eqToHom` of that equality; it introduces no new scalar extension or
arbitrary map. This is the common-model identification implicit in the node's definition
of D_n and r_n, exposed as a helper of the same notion. The module also gives the product
family explicitly and uses local irreducibility attributes for the chosen products, cone, section
functor, finite pullback levels, and reduction-tower alias. These are elaboration settings only; they do not change any imported declaration,
category, mathematical datum, or statement.

## Second reading by Q14

This is the dispatcher's single-worker check, not a claim of an independent agent review:
the brief explicitly forbids starting other agents and assigns independent review to the
maintainer. I reopened the node and the complete final module and checked every row above.
The fixed-resolution result is unconditional apart from the node's own level augmentation
hypothesis; the family result assumes exactly chain naturality, encoded by NatTrans. Both
cone coordinates are fixed by reused definitions. Composition order was checked explicitly:
b_q iota Gamma(q) is `Gamma(q) ≫ iota ≫ b_q`, and the roof is `inv a ≫ b`.
The comparison targets are actual derived objects and isomorphisms, not just degreewise
cohomology comparisons. No inverse of a_P occurs. Elaboration repairs only made the
product target and the invertibility witness explicit; they did not add a mathematical
hypothesis or alter a source statement. All five postponed theorems have the same node's
blueprint tag and a complete natural-language proof of their corresponding clauses.

Validation: prescribed `scompile.py Q14 lem-trf-point-transport-cone-comparison-descent`
compiled the complete final module both as the sandbox module (28.7 s) and under its
delivered module name (56.1 s), each within the unmodified 60 s limit. No errors or
unexpected warnings were reported. All diagnostic files and options were removed.
