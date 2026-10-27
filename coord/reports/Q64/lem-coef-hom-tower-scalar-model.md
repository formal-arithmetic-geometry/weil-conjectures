## Worker report

Stage 2, group Q64, 2026-10-23. The main module is
`Sheaf.SixFunctors.CoefHomTowerScalarModel`; its main statement is
`WeilConjectures.coefHomTowerScalarModel`. All theorem proofs are `sorry`.
Definitions contain actual functors, maps, and complexes; the choices of section
and derived-composition isomorphisms are uniquely characterized by equations.
The constant sequence equivalence has real forward and inverse functors, with named
additivity and sectionwise characterization theorems. C4’s proved dependency record
and module are unchanged; no dependency node file is delivered.

Read the item, its nine proof steps, all statement-dependency records and relevant
source signatures/docstrings, the current blueprint
`main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/prop-coef-integral-dualizing.proof.md`
(proof paragraph 2), and the stage contract. The blueprint's extension/restriction
calculation is before inverse limit, retains the specified maps, and only takes
degree zero afterwards. The item is a proper subargument, not the unit statement.
No statement correction or disputed mathematical assertion is needed.

The natural-number convention is n = exponent minus one. Thus n=0 means A_1,
not the zero quotient. The coefficient extension and site sizes are independent:
`E : Type u`, `W : Scheme.{t}`, site object universe t+1, arrow universe t,
coefficient/module universe max u (t+1), standard ordinary derived localizations.
The `ULift` is the existing coefficient-size transport, not a different ring.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Prime ell | `l : ℕ` with `[Fact l.Prime]` |
| Finite E/Q_ell | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` |
| Valuation ring, chosen uniformizer, A_n and quotient transitions | Recorded `Padic.coefficientExtensionIntegers`, `coefficientExtensionRing`, `coefficientExtensionTransition`; no new valuation or quotient definition |
| Every scheme, small pro-etale site, size convention | `W : Scheme.{t}`, `Scheme.ProEt.topology W`, independent t,u; existing essentially-small instances |
| Completed ring and ordinary modules/derived categories | `completedIntegralCommRingSheafUnrestricted`, `scalarReductionSource`, `DerivedCategory` with `HasDerivedCategory.standard` |
| Actual vertical sequence ring and finite evaluation | `coefficientSequenceCommRingSheaf`, `coefficientSequenceDerivedEvaluation`; all finite indices use n+1 |
| Constant completed sequence ring | `coefHomConstantRing` is `systemSequenceRing` of the actual constant completed-ring diagram |
| rho_W has the actual completion projections | `coefHomScalarMap`; its component at (n,U) is the recorded completion projection at U; `coefHomScalar_naturality` states compatibility |
| One-point sequence topos, quotient ring, rho_0 | `coefHomPointQuotientRing`, `coefHomQuotientPointModules` (module presheaves on ℕ with trivial topology), `coefHomPointScalarMap` with actual quotient maps |
| Point sections valued in towers, no inverse limit | `coefHomConstantSections`, `coefHomQuotientSections`, and their right derived functors; target is `D(Tow(Mod R))`, never `lim` |
| g_R rho_W = rho_0 g_Q | `coefHomOrdinaryFactorization_exists` is uniquely identity on all underlying section elements; `coefHomFactorizationComplexIso` retains its actual chain map |
| Exact restriction | Existing `scalarRestriction_limits/colimits`; point exactness is `coefHomPointRestriction_exact` and its named instances |
| K,N arbitrary unbounded derived objects | Domain of `coefHomTower`, `coefHomScalarTower`, and main theorem's K,N clauses |
| V = const K | `coefHomDerivedConstant` localizes the exact constant functor through the section-preserving equivalence |
| M = Lrho_W* V, D_N = RHom_Q(M,N), h_N = Rg_Q* D_N | `coefHomScalarTower S` uses `(S.scalar (coefHomScalarMap ...)).derived`, recorded `coefficientSequenceInternalHom`, actual `coefHomQuotientDerivedSections`, then exact `coefHomPointDerivedRestriction` |
| Actual K-flat P with flat terms | `coefHomTower_representative` quantifies over P, `_hP : IsKFlatIndependentCoefficients ... P`, `_hflat : ∀ i, IsFlatOnSite ... (P.X i)` and `_eP : QP ≅ K` |
| Simultaneous K-injective tower I representing rho_*N | The same theorem quantifies over `I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource ...) ℤ`, `[I.IsKInjective]`, and `_eI : Q(coefHomSequenceComplex I) ≅ rho_*N`; it does not resolve components independently |
| Strict global Hom tower with signed differential and postcomposition transitions | `coefHomStrictComplex` reassembles `I.asFunctor` followed by the existing signed `homComplexFunctor` and actual integral-linear sections. Its d is the whiskered existing d; the whole transition functor is retained |
| Actual g_R* Hom(const P,I) representative and level-n formula | `coefHomSequenceHomComplex`, `coefHomSequenceSectionComplex`, and `coefHomSequenceSections_iso` compare whole complexes of towers with their actual differentials; `coefHomTower_representative` states K-injectivity and both localized representative isomorphisms, with their hom maps equal to the explicitly constructed representative maps |
| First whole-tower derived isomorphism | `coefHomTower_representative` identifies localization of strict Hom with the canonical bifunctor `coefHomTower`, defined as Rg_R* RHom_R(const(-),rho_*(-)) |
| Second whole-tower isomorphism | Main theorem's natural iso `α : coefHomTower ≅ coefHomScalarTower S` |
| Canonical second comparison | Its inverse components equal `coefHomDerivedFactorization.hom` followed by actual sections of `A.iso`; `coefHomDerivedFactorization_exists` uniquely fixes the former by the universal derived-comparison equation on every complex |
| Contravariance in K, covariance in N | All displayed global and finite comparisons are natural isomorphisms of actual bifunctors on `(D(R_W))ᵒᵖ × D(Q_W)` |
| Internal comparison is precisely the recorded scalar Hom iso | Main theorem uses `A.iso (coefHomScalarMap ...)` rather than an arbitrary internal isomorphism |
| Three representing bijections for every T | Main theorem's `scalarHomBijection ... T ... f = f ≫ A.iso.hom` clause. This existing composite is scalar adjunction, closed transposition, strong tensor comparison, scalar adjunction, closed transposition; its middle objects are exactly the node's three displayed Hom sets |
| Evaluation after actual scalar-extension unit | Main theorem's sequence `transpose.symm (A.iso.hom) = scalarHomRestrictedEvaluation ...` clause; that definition inserts the scalar unit and restricted quotient evaluation, with the recorded tensor-Hom signs |
| Finite evaluation RHom_R(K,Res_n N_n) | Main theorem's `∀ n, ∃ γ, CoefHomEvaluationNormalization ... n γ`; its equation uses the same strict resolving complex, exact evaluation factors, and finite representative map; `coefHomFiniteIntegral` uses the recorded finite evaluation and restriction, integral internal Hom, and integral-linear derived sections |
| Finite scalar-extension RHom_A(K_n,N_n) as D(R) object | `coefHomFiniteQuotient F n` uses the derived completion-projection scalar extension, finite internal Hom, exact integral restriction, and derived sections. The ringed-topos composition comparison identifies this with rho_0* of quotient-linear sections |
| K_n is the recorded derived reduction | `coefHomFiniteExtensionIso F n` is `Adjunction.leftAdjointUniq` for the normalized scalar pair and recorded `coefficientFiniteAdjunction`; it is unit-compatible and identifies it with `coefficientFiniteDerivedExtension` |
| Finite comparison is actual scalar adjunction, unit-normalized | Main theorem's finite iso β has inverse exactly `coefHomDerivedSections.map (B.iso ...).hom`, followed by the finite `transpose.symm = scalarHomRestrictedEvaluation` equation. `ScalarDerivedPair.normalization` and `ordinaryUnit` retain the actual p ↦ p tensor 1 and p tensor a ↦ a f(p) formulas |
| Isomorphisms of complexes in D(R), not H^0 bijections | All finite codomains are `DerivedCategory (ModuleCat (ULift coefficientExtensionIntegers))`; no cohomology functor is applied |
| No quotient-map flatness, no boundedness | Neither appears among any binders; the sole flatness conditions concern the chosen resolving complex P, as in the node |

The S,μ,A and F,ν,B arguments are presentations of the already recorded canonical
closed tensor/scalar structures, not extra geometric assumptions. Their existence
is `CategoryTheory.scalarInternalHomAdjunction_exists` on each of the two sites.
Their structure fields fix actual scalar-extension objects/maps, left-derived
universal properties, ordinary and derived unit normalization, evaluation and
representing bijections. In particular an arbitrary iso or arbitrary functor
cannot satisfy these presentation interfaces.

### Dependency declarations used

- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` / `Padic.finite_coefficientExtensionRing`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale` / `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-size-convention`: a size metaconvention, with no Lean declaration; the independent universe binders and existing size transports implement it.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` / `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules` / `CategoryTheory.ringedSiteModules`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic` / `DerivedCategory`.
- `def-coef-ringed-sequence-site`: `Sheaf.Paper.CoefficientRingedSequenceSite` / `WeilConjectures.coefficientSequenceCommRingSheaf`.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` / `CategoryTheory.ordinaryModuleDerivedInternalHom`.
- `def-coef-ringed-tensor-hom-model`: `Sheaf.Paper.CoefficientRingedTensorHomModel` / `WeilConjectures.CoefficientTensorModels`.
- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` / `CochainComplex.IsKFlatIndependentCoefficients`.
- `lem-pc-kflat-resolution`: `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` / `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- `def-pur-kinjective-complex`: `Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean` / `CochainComplex.IsKInjective`.
- `def-pur-hom-complex`: `WeilConjectures.Algebra.Homology.HomComplex` / `CategoryTheory.homComplex`.
- `lem-sfb-dc-hom-scalar-adjunction`: `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction` / `CategoryTheory.scalarInternalHomAdjunction_exists`.
- `lem-pur-derived-change-of-rings`: `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` / `ModuleCat.nonempty_ordinaryDerivedChangeOfRings`.
- New `def-coef-constant-sequence-equivalence`: `Sheaf.Paper.ConstantSequenceModuleEquivalenceOfUniverses` / `CategoryTheory.ConstantCompletion.independentConstantSequenceEquivalence`. The original `lem-pur-constant-sequence-module-equivalence` remains a proof dependency, imported from its unchanged, proved C4 module.

Additional proof imports retain the accepted DAG plan: small module diagrams,
functorial K-injective resolutions, tower evaluation on K-injectives, global
Hom cochains, K-flat into K-injective Hom at independent coefficients, the
normalized ringed-topos derived-composition theorem, coefficient adjunction,
and Hom-complex quasi-isomorphism invariance. `homComplexFunctor` and
`HomologicalComplex.asFunctor` supply the actual strict complex construction.

### Edge cases and searches

Checked K=0, N=0 and the empty scheme: sections/complexes have zero underlying
modules, all functors and comparisons remain typed. Checked n=0 (the first
positive quotient) and identity transitions; quotient maps and completion
projections use exactly the existing n+1 convention. A non-flat quotient such
as R→R/varpi is retained: derived extension, not ordinary tensor on K, defines
K_n. Unbounded P,I are allowed; Hom uses product totalization with the existing
integer sign. Choosing E and W in different universes remains allowed.

Searches actually run (the wrapper recorded them in searches.jsonl):

- LeanFinder, `Global Hom tower from a K-flat complex into a K-injective tower computes derived internal Hom with scalar restriction`: eight results, including Ext and scalar adjunction HomEquiv; none is this whole-system theorem.
- Loogle, `CategoryTheory.homComplex, DerivedCategory`: zero hits, unknown Mathlib identifier `CategoryTheory.homComplex` (the project owns it).
- Mathlib grep, `HomTower|homTower|scalarInternalHom|sequence.*[Ss]ections`: two AlgebraTower hits, no match.
- LeanSearch, `Derived global Hom tower K-flat K-injective sequence site scalar restriction`: eight results, including `SheafOfModules.instAdditiveRestrictScalars`, `Sheaf.ΓRes`, and presheaf scalar restriction; none gives the theorem.
- Project `rg` for `HomTower|homTower|coefHom` under `lean/WeilConjectures` and `lean/Sheaf`: existing scalar-Hom tower coherence and adic residue Hom towers concern other constructions; no duplicate of this node. Searching the node id in WeilConjectures found none.
- Read the actual recorded `homComplexFunctor`, independent-universe derived internal Hom, `ScalarDerivedPair`, `ScalarHomModels`, `scalarHomBijection`, `scalarHomRestrictedEvaluation`, and `ScalarInternalHomAdjunction`: these supply the underlying notions, so none was privately redefined.

## New nodes

`def-coef-constant-sequence-equivalence` defines the independent-universe equivalence
as the strict-system realization followed by explicit level/transition functors.
`independentToTower` and `independentFromTower` have real data; the system equivalence
has identity level unit/counit maps. It is composed with the already universe-general
`strictSystemSequenceEquivalence`. Named additivity and forward/inverse section HEq
statements describe these particular functors, with proof plans in their docstrings.
The source is Stacks 03DA/0940, Zheng Construction 4.1 and the blueprint's mapping
complex calculation before limits. The existing C4 theorem is proved but its public
interface only has equal site universes; its private constructors cannot be reused
at independent sizes. Its entire live node record is left untouched.

Searches run for this new node: LeanSearch query "Constant ring sequence sheaves
equivalence ordinary module towers independent universes" returned eight generic
sheaf/constant-sheaf declarations, none this construction; Loogle query
`CategoryTheory.Functor.const, CategoryTheory.Equivalence` returned four comma-category
results; Mathlib grep `constantSequenceModule|systemTowerEquivalence` returned zero.
These exact wrapper results are recorded in searches.jsonl and the new node.
Project rg found only C4's equal-universe module and its presentation consumer;
none under WeilConjectures. DAG rg for independent-universe constant sequence
notions found consumers, not this definition; blueprint_refs.py search
`constant.*sequence` returned zero. The ancestor tool returned
`prop-coef-integral-dualizing`. The item's stmt_deps adds only this new definition
relative to live main, and no theorem dependency record is rebound.

## Second reading by Q64

A separate pass by the same dispatched worker (the dispatch explicitly forbids
starting another agent), with the node and both final source files open.

The first draft omitted the theorem and defined restricted quotient sections
through integral sections. This was repaired: quotient point coefficients,
actual quotient-linear sections, exact rho_0 restriction and the normalized
ordinary/derived composition square now have separate concrete definitions.
Consequently α compares the two stated constructions. I checked every row of
the correspondence table against the signatures, including the all-T representing
formula, evaluation after the unit, simultaneous I, and the n+1 indexing.
The finite iso β is explicitly the image of the recorded internal scalar iso;
it is not an arbitrary existence assertion. `coefHomFiniteExtensionIso` ties its
source to the existing finite reduction through the normalized common right
adjoint. All finite comparisons are objects of D(R); no forgetting to abelian
groups or degree zero occurs. The constructed equivalence has all four forward and inverse sectionwise
characterizations, and its independent sizes include the actual site. The data choices use uniquely normalized comparisons; the equivalence and its
inverse are explicit constructions, and no definition has sorry data.
The theorem helper statements are clauses or required construction laws of this
same node, carry its blueprint id, and have proof plans in their docstrings.
No source statement, proof step, target, or citer was changed.

## Return repairs

R1: removed the dependency-node copy from the delivery. The live C4 record is
byte-identical because it is not touched at all. The new definition node owns the
independent-universe module. `coefHomEquivalence` is the explicit composite, not
`.choose` of an existential theorem. Both directions retain literal sections,
restrictions, transitions and maps. Named additivity and HEq theorems refer to this
constructed object; no pending theorem chooses either functor's data.

R2: `CoefHomSliceNormalization` specifies the degree-i, product-p component over
(n,U), using the recorded `coefficientHomComponent` projections: the map is restriction of the slice morphism to index n, on every U→W.
`coefHomSequenceSections_iso` is now an existence-uniqueness statement with exactly
this formula. The inverse reconstructs earlier indices by postcomposition, so
this equation determines the signed complex isomorphism.
`coefHomInternalComparison` is Q of the actual Hom map induced by the functorial
K-injective augmentation followed by the inverse localization factorization.
`coefHomRepresentativeMap` applies the universal right-derived section comparison,
then sections of that map and the explicit eP/eI transports. Both isomorphisms in
`coefHomTower_representative` have specified hom maps: this map for sequence
sections, and Q of the inverse slice iso followed by this map for the strict tower.
Main clause 2 now quantifies γ with `CoefHomEvaluationNormalization`, an equation
on every flat-term K-flat P and simultaneous K-injective tower I with eP,eI.
Its left side evaluates that same strict representative map and composes γ;
its right side is exact evaluation/localization followed by the finite canonical
representative map. `coefHomFiniteTargetMap` transports eI using the constructed
equivalence counit and the identity-section-normalized restriction/evaluation square.
Thus γ is tied to actual finite RHom, all differentials, scalar maps and transitions.
No condition of mere Nonempty is left for any returned comparison.

The final second reading checked the new node and the enlarged item module against
both return points and all rows above. Independent t,u, arbitrary unbounded P,I,
zero K or N, the empty scheme, the first positive quotient n=0, and nonflat
coefficient maps remain allowed. α.inv and β.inv still use the recorded A.iso and
B.iso; the ordinary/derived factorization normalizations remain unchanged.

### Validation

The prescribed initial dry run on the saved packet returned OK at 2b9cb60350f;
that mechanical success did not repair R1/R2, so it was not pushed. Subsequent
scompile.py checks compiled each actual module separately in dependency order.
The final dry run and push are performed only after all return repairs and a clean
per-file compilation. No live source was edited and no git command was run there.

Final self-check: all postponed declarations are recorded in lean.declarations,
with source/proof docstrings; every variable/universe is explicit. Both modules
compile through scompile.py without errors or non-sorry warnings. The existing
coefficientHomComponent and coefficientHomResolutionIso are used directly; no
second product projection or localization-factorization notion is introduced.
