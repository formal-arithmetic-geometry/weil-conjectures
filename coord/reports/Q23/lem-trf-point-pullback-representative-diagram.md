## Worker report

The delivery states `WeilConjectures.PointPullbackRepresentative.pointPullbackRepresentativeDiagram`
in `Sheaf.Paper.PointPullbackRepresentativeDiagram`. It also supplies the §1(B)
independent-coefficient interface for the recorded exact-point-sections dependency.
All three postponed results are named theorems with `sorry` and source/proof docstrings:
`point_proEtale_sections_exact_of_universes`, `sectionRoosComparison_existsUnique`,
and `pointPullbackRepresentativeDiagram`. Every definition and instance has actual data.
There is no statement correction, disputed statement, new definition node, or altered target.

The source was read at blueprint main-20261015,
`sec-trace-formula/sk-d-weil/prop-trf-rational-frobenius-integral-model.proof.md`,
clause (3), together with the item's six extracted proof steps and Stacks 0941,
`sites-cohomology.tex`, `lemma-derived-limit-is-ok`.

Hypotheses and clauses, in order:

| Node text | Lean rendering |
| --- | --- |
| Algebraically closed field k and s=Spec k | `(k : Type t) [Field k] [IsAlgClosed k]`, `Spec (.of k)` |
| Prime ell, finite extension E/Q_ell | `(l : ℕ) [Fact l.Prime]`, `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` |
| Ell invertible in k and Y, arbitrary morphism s→Y | `_hl : IsUnit (l : k)`, `{Y : Scheme.{t}}`, `f : Spec (.of k) ⟶ Y`, `_hY : ∀ y, IsUnit (l : Y.residueField y)`; residue-field and stalk formulations of invertibility agree |
| Valuation ring, fixed uniformizer, positive finite coefficient levels | The dependency's `Padic.coefficientExtensionIntegers` and `coefficientExtensionRing`; n indexes exponent n+1, never exponent zero |
| R_Y and R_s are limits of the actual finite constant ring sheaves | The recorded `completedIntegralCommRingSheafUnrestricted` and `integralTowerModules`; all module sizes are `max u (t+1)` |
| Exact final-object sections as an O_E-module functor | `sections`, the existing Mathlib evaluation followed by `ModuleCat.restrictScalars (scalarMap ...)`; `scalarMap` is evaluation of `integralConstantToCompletionOfUniverses` composed with the constant sheafification unit. `sectionsLimits`, `sectionsColimits`, `derivedSections`, `sectionsFactors` retain this exact functor |
| Arbitrary unbounded K and every flat-term K-flat representative | Every K in `DerivedCategory (integralTowerModules ... Y)` and every P in `(integralOperationsGoodComplex ... Y).FullSubcategory`. Its property is exactly `IsKFlatIndependentCoefficients P ∧ ∀ i, IsFlatOnSite (P.X i)`. `q : DerivedCategory.Q.obj P.obj ≅ K` is the localized representative; a quasi-isomorphism of complexes gives exactly such an isomorphism |
| P_n and C_f(P) with their actual quotient transitions | `pullbackTower` is the existing `integralOperationsPullbackTowerFunctor`: its level is `unrestrictedIntegralFiniteComplex ⋙ (integralOperationsLevelPullback ...).mapHomologicalComplex ⋙ integralOperationsRestrict`, and its steps are `integralOperationsPullbackTransition`. No unrelated level maps are supplied |
| These levels compute finite derived pullbacks simultaneously | The first conjunct uses `ReductionComputedBy`, whose full definition says the canonical `reductionCounit` is invertible on every good P at every level. This is the recorded universal left-derived comparison, not an arbitrary isomorphism. `finitePullbackLimits` and `finitePullbackColimits` instantiate exact finite module inverse image; restriction is the recorded exact scalar restriction. Thus the same strict tower computes reduction, then Lf_n*, then Res_n, with the given quotient maps |
| B_f(P) and its chain functor | `sectionTower = pullbackTower ⋙ whiskeringRight sectionsComplex`; `sectionRoos = sectionTower ⋙ integralOperationsRoosFunctor` |
| Signed H(Z), diagonal maps | The existing `integralOperationsRoos` is `mappingCocone (towerTransitionEndomorphism ...)`, i.e. Cone(1-s)[-1]; the displayed (b,a) convention orders the shifted `snd` before unshifted `fst`. Its map is the dependency's `integralOperationsRoosMap`, using the product map on both summands |
| c_Z is the canonical product comparison on both coordinates, an isomorphism | `RoosCoordinates`/`Coordinates` fixes both the unshifted and shifted coordinates after every nth product projection. This is precisely the canonical product comparison, since product projections jointly determine it. `sectionRoosComparison_existsUnique` supplies the unique chain isomorphism, `sectionRoosComparison` selects that uniquely determined map, and the main theorem repeats its coordinate specification |
| Strict naturality of c | `RoosNaturality`, used in the third conjunct, quantifies over every strict tower map w and equates Gamma(H(w)) followed by c with c followed by H(Gamma(w)) |
| Quasi-isomorphism invariance and localization descent | `hInv` asserts `QuasiIso u → QuasiIso ((sectionRoos ...).map u)` on all good complexes; the next conjunct gives a natural isomorphism from `integralOperationsGoodLocalization ⋙ completedSections` to the localized sectionwise chain functor, with components equal to the specified comparison |
| v=c Gamma(jmath) on every representative | `representative` first transports along q inverse, then applies exact derived sections to `integralDerivedPullbackComparison`, then `sectionsFactors`, then localization of `sectionRoosComparison`. `completedSections = integralDerivedPullback ⋙ derivedSections` |
| The commuting representative square for chain u and derived h with q'u=hq | The next universal conjunct uses `Q.map u ≫ q'.hom = q.hom ≫ h` and equates `completedSections.map h ≫ representative(...q').hom` with `representative(...q).hom ≫ moduleQ.map (sectionRoos.map u)` |
| Inverse quasi-isomorphisms and composites of roofs | The roof conjunct gives the explicit inverse-denominator/diagonal-numerator formula for every good roof a,b and every h equal to its image under q,q'. `hInv` supplies the invertible sectionwise denominator. The next conjunct says every derived arrow between good representatives has such a roof, with a good middle complex |
| All-derived naturality and independence | Both q and q' and h are arbitrary in the roof formula. The left side depends only on h; hence any two roofs have the same value. Setting h=id compares any two representatives of the same K. Composition follows by cancellation of the intermediate representative isomorphisms. This includes inverse quasi-isomorphisms and finite composites of roofs |
| The target is a derived limit of the entire evaluated tower | The final conjunct is `IsDerivedLimit` for `moduleQ.obj (sectionTower.obj P).obj (op n)` and exactly its `integralOperationsTowerStep` maps, with limit object `moduleQ.obj (sectionRoos.obj P)`; `moduleDerivedProducts` provides the standard derived products of ordinary modules |
| No completeness, constructibility, boundedness, invertibility of f | None occurs in the binders, resolving property, or theorem. The only resolution restrictions are K-flatness and termwise flatness |

Dependencies used, by recorded module and declaration:

- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; `Mathlib.AlgebraicGeometry.Scheme`: `Spec`; `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing` and the reexported recorded integer, uniformizer, quotient and transition constructions.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: `integralConstantToCompletionOfUniverses`; its coefficient modules give `completedIntegralCommRingSheafUnrestricted` and the actual projections.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact`: the exact restriction-of-scalars instances, used directly rather than inferred through large adjunctions.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`, `HasDerivedCategory.standard`.
- `Sheaf.Paper.PointProEtaleSectionsExact`: `AlgebraicGeometry.ProEtale.pointModuleSections`, `point_proEtale_sections_exact`; the delivery's generalized version uses the identical forget/evaluation construction.
- `Sheaf.CategoryTheory.StrictRoosModel`: `CategoryTheory.roosF`; the exact strict-tower-of-complexes presentation is the already recorded `integralOperationsRoos`/`integralOperationsRoosMap`, used throughout, not a second cone construction.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: `CochainComplex.IsKFlatIndependentCoefficients`; `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`, via `integralOperationsGoodComplex`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `SheafOfModules.restrictScalars`, via the recorded `integralOperationsRestrict`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`: `CategoryTheory.IsDerivedLimit`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the recorded finite `finiteDerivedPullback` interface and `commonStageDerivedInternalHom_existsUnique` were read; this statement uses its finite operation, not the rational/common-stage Hom clauses.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices` reexports `integralDerivedPullback` and `integralDerivedPullbackComparison`; `Sheaf.Paper.IntegralOperationsWellDefined` supplies `integralOperationsWellDefined`, its strict tower, quotient maps and Roos construction.
- The independent-size exact finite inverse image is the landed `AlgebraicGeometry.Scheme.coefficientProEtaleModulePullback_exact` in `Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackExact`.
- Proof imports include `ChangeOfRingsKFlat`, `StrictRoosComparison`, `DerivedLimitProducts`, `DerivedCategory.Fractions`, and `Localization.CalculusOfFractions`; the K-flat resolution and exact-product dependencies are reexported by the recorded integral-operation modules.

Edge cases checked before and during writing: arbitrary unbounded good complexes;
zero complex; identity and zero chain maps; identity f; non-isomorphism f;
exponent n=0 in the encoding means A_1; shifted coordinate in every integer degree;
characteristic zero and positive characteristic distinct from ell; unrelated universes t,u;
arbitrary representative isomorphisms q, including those obtained by localizing actual
quasi-isomorphisms; inverse quasi-isomorphisms, two roofs for one arrow, and a composite
of roofs. No finite-field datum is imposed. Spec k is nonempty; if Y is empty there
is no f, so no unmentioned nonempty-scheme hypothesis is needed. The ell-unit
hypotheses exclude real positive-characteristic cases and are not automatic hypotheses.

Searches made (Q23 msearch wrapper, plus read-only rg/grep):

- LeanFinder: “Exact point sections identify completed pullback on every K-flat representative with the strict Roos cone of the finite pullback section tower”, and “Completed pullback on a K-flat complex is the Roos cone of finite pullbacks and exact point sections commute with both cone coordinates”. Eight generic homological-complex/flat-limit hits, including `HomologicalComplex.coneOfHasLimitEval_pt_d`; no completed-pullback representative theorem.
- Loogle: `CategoryTheory.Functor.mapDerivedCategoryFactors`. Twelve hits, including the canonical exact-functor localization comparison used here; none includes the strict finite quotient tower or both-coordinate normalization.
- Mathlib grep: `[Cc]ompleted[Pp]ullback|[Pp]ullback.*[Rr]oos|[Rr]oos.*[Ss]ection`. Zero hits.
- LeanSearch: “Exact point sections identify derived completed pullback with the Roos complex of finite pullback sections naturally for K-flat representatives”. Eight hits, including generic pullback short-complex exactness and `SheafOfModules.sheafificationCompPullback`; no match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for point/section/Roos constructions found `CompletedStalk.sectionsRoos` and the related completion-cone and point-pullback-localization modules. They require a finite-field datum and specialize the scheme map; they do not assert this node for arbitrary algebraically closed k, arbitrary f, arbitrary ambient K and independent t,u. Their existing strict quotient/Roos constructions are reused. Exact declaration-name searches for the new names and grep of this blueprint ID in `lean/WeilConjectures` found no existing declaration.
- The prescribed `scompile.py --source Sheaf.Paper.IntegralDerivedOperations` confirmed that the live completed pullback and its representative comparison match the inspected source and retain independent universes.

## Dependency modules

`lem-weil-point-proetale-sections-exact`: the old recorded evaluation and theorem
force coefficient size t+1. For this item the coefficient extension lives in an
independent universe u, and module/coefficient size is max u (t+1). The new module
`Sheaf.Paper.PointProEtaleSectionsExactOfUniverses` reexports the original module,
uses exactly Mathlib's module forget/evaluation composite, and states the same
abelian-sheaf surjectivity, exact module sections, quasi-isomorphism preservation,
unbounded derived comparison, shift/triangle compatibility and homology comparison
in the containing universe, with independent localization sizes w,w'. Only this
node's lean record changes. No site is resized and no equality of t and u is assumed.

## Second reading by Q23

This is a separate clause-by-clause reread by the same worker; the dispatcher forbids
starting other agents and explicitly assigns the independent reading to the maintainer.
The table above was checked against the node and both files. The reread required the
exact-sections universe repair, fixed the choice of the standard target localization,
and replaced an elaboration-heavy whole-product condition with the equivalent nth
projection condition on both coordinates. The strict naturality equality is rendered by the generic `RoosNaturality` predicate, avoiding repeated elaboration of the large specialized coefficient category. It checked especially the negative shifted
coordinate, the direction of q inverse and of roof denominators, the relation
Q(u)q'=qh, and the actual section-tower transitions in IsDerivedLimit. It did not
replace c or jmath by an unspecified isomorphism. Every theorem remains sorry.

## Validation

All Lean compilation uses the prescribed `scompile.py`, each file separately in dependency
order against the published live build, with the unchanged 60-second file limit.
Final scompile check: both delivery modules compiled without errors or warnings.
The generalized dependency took 13.3 seconds (8.3 seconds for its sandbox check);
the main module took 7.8 seconds (7.6 seconds for its sandbox check). The finite
comparison is named `ReductionComputedBy`: this is exactly invertibility of the
same canonical reduction counit, and prevents repeated elaboration of its large
derived-category type inside the joint theorem. No limit was increased.
Delivery preflight is run with deliver2.py --no-push before pushing.
