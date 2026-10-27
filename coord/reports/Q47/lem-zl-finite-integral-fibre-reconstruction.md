## Worker report

The delivery states `lem-zl-finite-integral-fibre-reconstruction` in
`Sheaf.Paper.ZlFiniteIntegralFibreReconstruction`. The two postponed theorems are
`WeilConjectures.ZlFibreReconstruction.finite_integral_fibre_reconstruction` and
`WeilConjectures.ZlFibreReconstruction.finite_integral_fibre_roos`, respectively the
integral reconstruction clauses and the strict finite Roos clause of this one node.
Their docstrings give the node's seven-step proof, with the coordinate proof written
out for the Roos clause. No theorem is proved in this delivery. Definitions have real
data: the geometric lifts are pullback lifts, system arrows are actual adjunction
mates and counits, and finite-sum comparisons are biproduct lifts of their components.

Hypothesis and clause correspondence:

* The finite-field datum is `D : FiniteFieldDatum.{u}`, retaining p, a, q, the finite
  field and its fixed algebraic closure. The coefficient binders are `l : ℕ`,
  `[Fact l.Prime]`, `_hl : l ≠ D.p`, `E : Type u`, `[Field E]`,
  `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`. The valuation ring,
  uniformizer ideals and positive coefficient quotients are the dependency's Padic
  constructions. Index `n : ℕ` denotes exponent `n+1`, so exponent zero is never used.
* Separated finite-type k-schemes are `X Y : Over (Spec (.of D.k))`, with
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on each structure map.
  `f : X ⟶ Y` is a k-morphism; `[IsFinite f.left]` is the actual finite-morphism
  predicate. These are explicit hypotheses, with no additional smoothness,
  nonemptiness, flatness or dimension assumptions.
* `y : Spec (.of D.k) ⟶ Y.left` is the stated geometric point. The algebraic closure
  is part of D. `Limits.pullback f.left y`, `pullback.fst`, and `pullback.snd` are
  S, v and h. `Points f.left y` is exactly `{x // x ≫ f.left = y}`.
  `pointLift` is `pullback.lift x.val (𝟙 s) ...`, so both projection equations hold
  by the universal property rather than additional choices or hypotheses.
* Completion, integral module categories and exact scalar restriction are the
  recorded `completedIntegralCommRingSheafUnrestricted`, `scalarReductionSource`,
  `integralTowerModules`, and `coefficientFiniteDerivedRestriction` constructions.
  They retain the small pro-etale site with object universe u+1 and Hom universe u.
  E and the schemes share an ambient universe as in the recorded
  `sfIntegralConstructibleCategory` API; this does not identify those two site universes.
* Every integral constructible K is quantified as
  `K : sfIntegralConstructibleCategory l E X.left`. This is the recorded full
  subcategory, requiring derived completeness, all constructible finite reductions,
  and one common finite cohomological interval. It is not an arbitrary bounded
  category or an unrelated adic category.
* The first conjunct proves `Finite (Points f.left y)`. The following quantifier
  `∀ [Finite (Points ...)]` only lets the remaining formula use this proved instance
  when forming finite biproducts; it is not an added finiteness hypothesis.
* `imageSystem f K` is P_f applied to the coefficient calculus's strict reduction
  system. `imageEvaluation` identifies each evaluation with the recorded
  `sfFiniteDerivedDirectImage`, using the actual system evaluation mate and the
  identity-on-sections finite direct-image presentation. The quotient transitions
  are retained in the derived sequence-site category itself.
* `image f` is the functorial system-limit realization of the specified tower
  direct image. It is not a second arbitrary definition of Rf_*: the
  `ImageNormalization` clause quantifies over every `SfIntegralDirectImage f K`
  and requires an isomorphism to this realization preserving each of its actual
  Roos projections. In particular the realization uses exactly the existing
  finite direct image and restriction scalar action, not a completed coefficient
  direct image substituted without comparison.
* The first conclusion block asserts `sfIntegralConstructible` of image f K,
  integral v-pullback K, and image h of integral v-pullback K. The specified b and r
  are ambient derived isomorphisms between these objects. The full-subcategory
  interpretation and transport of the constructible predicate along isomorphisms
  put them in the stated Dbc category.
* `pullSystem f K` is G_f applied to strict reduction. `pullEvaluation` uses the
  dependency's finite pullback evaluation and the specified reduction evaluation.
  The recorded `integralSystemPullbackReductionIso` identifies reduction of the
  completed pullback with finite inverse image of the input reduction, for each
  flat-term K-flat representative. The duplicate `representativeEvaluation` has
  been removed.
* The chosen `cv`, `cy`, and `cx` have specified endpoints, and each satisfies
  `PullNormalization`. This equation is required for every good representative P,
  every identification Q(P) ≅ K and every level n. It identifies its total-limit
  projection with the scalar-extension adjunct of
  `integralSystemPullbackReductionIso.hom` followed by `pullEvaluation.inv`.
  The normalization tests universally over residue-invertibility instances and
  the constructibility proof for the input. Those tests are inhabited for all
  actual inputs: constructibility is already a conclusion (or K.property), and
  ell distinct from p gives a unit in the base field and then every residue
  field. Thus these internal tests neither add an assumption to the theorem nor
  remove any projection equation. Invertibility structures and constructibility
  proofs do not change the canonical comparison. A family of unrelated level
  isomorphisms cannot satisfy this normalization merely by being invertible.
* The three displayed system comparisons are the first system counit at
  `imageSystem f K`, `reductionComparison v K (cv K)`, and reduction of
  `fibreComparison` followed by the counit at `fibreSystem`. Their `IsIso`
  assertions are in the derived category of strict semilinear systems, so they
  include quotient-transition compatibility. `reductionComparison` is literally
  reduction of the normalized pullback comparison followed by the actual
  reduction/total-limit adjunction counit. The calculus's `counit_projection`
  formula fixes its evaluated components as the adjuncts of actual limit projections.
* `exchange` is the h-adjoint of the composite pullback commutation and the
  f-counit. `germ` uses h i_x = id, the h-counit, and v i_x = x. `restriction`
  is the biproduct lift of precisely these germ components. These are actual
  maps in the derived system category, derived from the published ordinary
  sectionwise operations and their canonical composition comparisons. They
  represent the level b_n and r_n before taking a total limit.
* The existential isomorphisms `b K` and `r K` have exactly the node's endpoints.
  Their defining equations identify b with the total limit of `exchange` after
  `exchangeComparison`, and r with `fibreComparison`, the total limit of
  `restriction`, `limitBiproduct`, and the inverse point comparisons. Their next
  two equations are the explicit total-limit projection identities for b and
  for each x-component of r. The last two clauses assert naturality for every
  K → L in the full integral constructible category.
* `limitBiproduct` is the canonical finite biproduct comparison: its x-component
  is the total-limit functor applied to the system biproduct projection. Its
  invertibility is explicitly asserted for the point systems.
* `pointTower` uses the recorded strict quotient tower of one flat-term K-flat P,
  the finite exact inverse image at x, and exact scalar restriction, with their
  existing quotient chain maps. `roosBiproduct` is the biproduct lift of the
  recorded strict Roos maps of each tower projection. The latter applies the
  same product map on both shifted-cone coordinates.
* `finite_integral_fibre_roos` asserts invertibility of this exact strict Roos
  arrow, and an isomorphism α between its two product presentations. The (x,n)
  equation pins α to coordinate reindexing. The next equation says it commutes
  with the same `towerTransitionEndomorphism` (1-s). These are chain maps, so
  commutation with differentials is in their types. The next equation records
  compatibility with each strict Roos projection. The empty clause asserts both
  Roos sums are zero and every isomorphism has the specified comparison as its
  hom, so it is the unique zero-object isomorphism. No point sections are applied.

Dependency declarations used:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (reexported):
  `Padic.coefficientExtensionRing`, `Padic.coefficientExtensionTransition`,
  `Padic.finite_coefficientExtensionRing` and the existing valuation-ring quotients.
* `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
  Scheme properties use the Mathlib declarations named by the convention node:
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, `Over`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `completedIntegralCommRingSheafUnrestricted`, its actual quotient projections,
  and the existing independent-universe completion interface.
* `Mathlib.AlgebraicGeometry.Sites.Proetale` (reexported): `Scheme.ProEt`,
  `Scheme.ProEt.topology`. Geometric points are morphisms from the spectrum of
  D.k; Mathlib `IsAlgClosed` / the closure datum supplies algebraic closedness.
* `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and
  `sfIntegralConstructibleCategory`.
* `Sheaf.Paper.IntegralDerivedOperations`: `integralDerivedPullback`, its good
  representative comparison, strict quotient towers and strict Roos maps.
  The recorded `IntegralDerivedOperationsOnSlices` reexports this global
  operation unchanged; only the global operation is needed here, so the
  smaller owning module is imported. The completed tensor is not used.
* `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage`,
  `sfFiniteDerivedDirectImage`, `sfDirectImageTerm`, and its actual projections.
* `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded
  scheme fibre product and universal pullback lifts. No module base change is needed.
* `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `coefficientDerivedSystemEvaluationCalculus`, its `reduction`, `adjunction`,
  `reductionEvaluation`, `reductionModel`, `counit_projection`, and the actual
  `coefficientSequenceLimit`, `coefficientSequenceProjection` functors/maps.
* `Sheaf.Paper.IntegralSystemReductionFullyFaithful`: `integralSystemRings`,
  `integralSystemTransition`, `integralSystemRings_finite`, and the existing
  coherent-reduction presentation. These definitions belong to the existing
  definition owner `def-sf-integral-system-reduction`, cited in stmt_deps.
* `Sheaf.Paper.FiniteSystemPullbackCoherence`:
  `finiteSystemDerivedPullbackEvaluation`, owned by the existing definition node
  `def-sf-finite-system-derived-pullback`, also cited in stmt_deps.
* `Sheaf.AlgebraicGeometry.VaryingRingOperations` (reexported):
  `AlgebraicGeometry.ProEtale.VaryingRing.G`, `P`, `adj`, `gComp`, `gId`, and
  `evalP`. Its already-landed definition node is added to stmt_deps rather than
  creating new copies of system operations.
* `Sheaf.Paper.IntegralPullbackSystemComparison`:
  `integralSystemPullbackReductionIso`, owned by
  `def-sf-integral-pullback-reduction-comparison`. It now supplies the entire
  projection-adjoint and representative comparison. None of
  `integralPullbackFiniteComparison`, `integralPullbackFiniteComplex`, or
  `integralFinitePullbackModel` is referenced directly in this delivery.
* Proof imports: the now-landed `Sheaf.Paper.FiniteCounitRestrictionTowers`,
  `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`, and
  `Sheaf.CategoryTheory.StrictRoosComparison`. The first supplies the strict
  exchange/germ theorem as a proof prerequisite; it is not a statement dependency.

Edge cases checked before and during writing: K = 0; empty X; empty fibre P_y;
identity finite f; a nonreduced finite fibre (points do not duplicate nilpotent
thickenings); a one-point fibre; multiple points; n = 0 as exponent 1; arbitrary
finite extension E; y need not be supplied as a k-linear point; site object and
Hom universes remain distinct. No nonempty or Fintype hypothesis excludes the
empty case. No point inverse image is commuted with an arbitrary inverse limit.

Searches actually made:

* `msearch.py leanfinder`: "Completed integral sheaf finite geometric fibre
  reconstruction with reduction system counits and finite Roos biproduct comparison".
  Eight hits, including `Condensed.profiniteSolidCounit` and affine-transition
  limit lemmas, with no matching reconstruction theorem.
* `msearch.py loogle`: `"lim", "biproduct"`. Twelve hits for abstract finite
  biproduct existence/preservation; none state the coefficient-system theorem.
* `msearch.py grep`: `Roos|finite.*fibre|finite.*fiber`, CategoryTheory. Eight hits
  in Galois and sheaf-point APIs; none state this reconstruction.
* `msearch.py leansearch`: "Integral sheaves reconstructed from coefficient
  systems on finite geometric fibres with Roos projection compatibility".
  Eight hits for module sheaves, quasicoherent data and sheafification; no match.
* `rg` in Mathlib for `mapBiproduct`, `biproductComparison`, and finite fibres
  found the canonical categorical comparisons and the finite-fibre geometry,
  which were reused; neither supplies the requested normalized integral theorem.
* `rg` of `lean/WeilConjectures` by item id returned no hit. Concept searches for
  integral fibre reconstruction found integral-closure ring geometry and unrelated
  adic purity reconstruction. `rg` of `lean/Sheaf` found existing reduction,
  pullback, direct-image and strict Roos infrastructure, all reused as above.

Sources read: the current blueprint's `lem-zl-finite-pushforward.proof.md`
(finite geometric-stalk paragraph), and the supplied Bhatt--Scholze PDF,
Lemmas 3.5.7 and 6.7.2, including their proofs. The first describes π* as
strict derived reductions and π*'s right adjoint as Rlim; the second gives
pushforward constructibility and its canonical finite-reduction comparison.

Validation: the full delivered module passes scompile.py in both sandbox and
actual module-name modes, with no errors or unexpected warnings. Each compile
stays below the required 60-second file limit. No local/global build was run.

No statement correction, disputed statement or new node is needed. The only
node-field changes relative to the base are lean and the landed definition
dependencies whose actual declarations the module uses.

## Repair of return at 2f6b0b077847

H2: replaced the statement dependency
`lem-pod-integral-system-reduction-fully-faithful` with its existing definition
owner `def-sf-integral-system-reduction`, and added the existing definition owner
`def-sf-finite-system-derived-pullback` for
`finiteSystemDerivedPullbackEvaluation`. Both owners are present on the current
base with `existing: true`; their recorded modules and signatures were checked.
No full-faithfulness theorem is used. The genuine dependency
`lem-coef-derived-system-evaluation-calculus` is retained because its chosen
calculus supplies data. The Lean source and mathematical statement are unchanged.
The sandbox node was compared with the current base: only stmt_deps and lean
were different, and this repair changes only stmt_deps and this report.


## Repair of return at 244e1e10d449

H2: reuse `def-sf-integral-pullback-reduction-comparison` rather than extracting
new ownership nodes for three lower-level theorem-owned helpers. The direct
references to `integralPullbackFiniteComparison`, `integralPullbackFiniteComplex`
and `integralFinitePullbackModel` are removed. `roosBiproduct` now uses
`integralOperationsRoosFunctor.map`, owned by `def-sf-strict-roos-functor`,
rather than referencing `integralOperationsRoosMap` separately. The functor's
map is definitionally that same diagonal map on both shifted-cone products.

The following requested existing definition owners were added to stmt_deps;
their node statements, recorded signatures and owning source docstrings were
checked. No definition node or theorem dependency is substituted for another.

| Definition owner | Recorded module and relevant declarations |
| --- | --- |
| def-coef-ringed-sequence-site | Sheaf.Paper.CoefficientRingedSequenceSite: coefficientSequenceDerived, coefficientFiniteAdjunction, coefficientFiniteDerivedRestriction, coefficientSequenceDerivedEvaluation, coefficientSequenceLimit, coefficientSequenceProjection |
| def-a1-flat-term-kflat-complex | Sheaf.Paper.IntegralOperationsWellDefined: integralOperationsGoodComplex |
| def-a1-integral-finite-pullback-tower | Sheaf.Paper.IntegralOperationsWellDefined: integralOperationsPullbackTowerFunctor |
| def-pur-integral-operation-complex-models | Sheaf.Paper.IntegralOperationsWellDefined: integralOperationsTowerStep, integralOperationsRoos |
| def-sf-strict-roos-functor | Sheaf.Paper.IntegralOperationsWellDefined: integralOperationsRoosFunctor |
| def-weil-tower-transition-endomorphism | WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism: towerTransitionEndomorphism |
| def-sf-scalar-reduction-categories-restriction | Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction: scalarReductionSource; scalarReductionTarget is used through the recorded comparison |
| def-weil-integral-derived-reduction | Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction: scalarReductionDerivedExtension |
| def-sf-finite-reduction-computation | Sheaf.Paper.CoefDerivedSystemEvaluationCalculus: coefficientFiniteReductionModel, now encapsulated in integralSystemPullbackReductionIso |
| def-weil-pbc-proetale-operations | Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations: proEtaleConstantRingDerivedPullback |
| def-weil-proetale-inverse-image | Sheaf.AlgebraicGeometry.ProEtaleInverseImage: proEtaleSheafAdjunction, proEtaleCoefficientDirectImageMap, proEtaleConstantModuleDirectImage |
| def-cbc-strict-constant-tower-operations | Sheaf.AlgebraicGeometry.StrictConstantTowerOperations: moduleDirectImage |

H4: removed `representativeEvaluation` entirely and removed its declaration
record. `PullNormalization` uses the existing `integralSystemPullbackReductionIso`
from `def-sf-integral-pullback-reduction-comparison` directly, followed only by
the inverse of the system-evaluation identification. Its scalar-extension
adjunct is exactly the previous map: the hom of the recorded iso is the old
projection-adjoint map followed by the same representative presentation factors.
No dependency repair under section 1(B) is needed.

The recorded iso requires constructibility and invertibility of ell at residue
fields. `PullNormalization` tests the equality for every such proof/instance,
so the theorem's signature has no additional hypotheses. For v and x, K.property
supplies constructibility; for y the theorem's first conclusion supplies it for
image f K. To obtain residue invertibility, the cardinality condition on k0 gives
characteristic p, and its algebraic closure k has the same characteristic.
If ell vanished in k then p would divide ell; since both are prime this would
force ell=p. Thus ell is a unit in k. For any scheme W mapping to Spec k, the
composite k -> Gamma(W,top) -> k(w) carries this unit to ell in each residue
field. This applies to X, Y, s and S (using S -> X -> Spec k), including empty
schemes. These tests are therefore nonvacuous for every occurrence of the
normalization. All good representatives and all n remain quantified.

Advisory check: `FiniteCounitTowers.square` is the same compositor square as in
`exchange`, using h followed by y, v followed by f and the pullback equation.
Its exchange is the unit-square-counit mate; the displayed derived exchange is
its adjunction-homEquiv expansion. `pointRestriction` and `component` insert the
identity comparison for h i_x=id, apply the h-counit, then use v i_x=x, in exactly
the order of `germ`. Their strict b/r are the termwise complex transformations.
The underlying ordinary right adjoints are both sectionwise inverse image on
site objects with constant-section scalar action; uniqueness of the corresponding
left adjoint gives the unit-preserving identification of their pullbacks and
compositors. Localizing that identification and the mate squares gives the
displayed derived exchange/germ arrows. The strict theorem's `Descent` records
localization factorization on every complex. This compatibility is a proof step,
not a definitional equality between the two presentations; no unrelated map is
chosen here. The landed strict theorem is now imported as a proof dependency.

Repair validation: scompile.py accepted the changed module in sandbox and actual
module-name modes with no errors or unexpected warnings. Only the two existing
node theorems remain postponed. The node's mathematical statement is unchanged;
its Lean theorem signature is still verbatim. The current base comparison showed
only lean and stmt_deps differences. The previous returned version was repaired
by deleting the duplicate construction and changing the Roos map, not re-pushed
unchanged. The required delivery preflight and per-file compile are run next.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
