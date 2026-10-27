## Worker report

This delivery attaches the exact existing theorem
`WeilConjectures.pullbackTensorIntegralTensorModel_existsUnique` in
`Sheaf.Paper.CompletedPullbackTowerRealizations`, line 335. No module is added:
the one-definition rule requires reusing this declaration. Its proof is already
`sorry`; this is a stage-2 statement attachment, not a claim that it is proved.
Only the item's `lean` field changes. No dependency repair or statement correction
is needed. The complete module was also read from the current server using
`scompile.py --source Sheaf.Paper.CompletedPullbackTowerRealizations`; the theorem,
its section binders, and the defining normalization agree with the local source.

Hypotheses and clauses, matched against the declaration and its definitions:

| Node text | Lean rendering |
| --- | --- |
| Prime ell | Section parameter `(l : ℕ) [Fact l.Prime]`. |
| Finite extension E/Q_ell | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. |
| Valuation ring, chosen uniformizer, actual quotients | The coefficient-extension constructions imported through the coefficient framework; finite level `n` uses `finiteCoefficientRing l E (n + 1)`. They are fixed constructions, not extra arbitrary ring data. |
| Scheme W in universe u | Explicit binder `(W : Scheme.{u})`. |
| Small pro-etale sequence site with actual quotient transitions | `coefficientSequenceTopology (ProEt.topology W)` and `coefficientSequenceCommRingSheaf l E W` on `ℕ × W.ProEt`; object/morphism universes are `u+1`/`u`. |
| Completed ring A_W and its modules | `completedIntegralCommRingSheafUnrestricted l E W` and `integralTowerModules l E W`. |
| Sequence modules, evaluation, restriction | `coefficientSequenceModules`, `coefficientSequenceEvaluation`, `scalarReductionRestriction`, and simultaneous `coefficientSequenceRestriction`, all at `l E W`. |
| Ordinary unbounded complexes and three localizations | `CochainComplex _ ℤ`, ordinary `DerivedCategory`, `DerivedCategory.Q`, and the explicitly typed `pullbackTensorTowerQ`. No bounded subcategory occurs. |
| Fixed derived reduction/limit adjunction | `(pullbackTensorCalculus l E W).reduction` and `.adjunction`; `coefficientSequenceLimit` is `coefficientSequenceDerivedRestriction ⋙ coefficientConstantTowerLimit`. |
| Fixed system derived tensor and cochain tensor | `(pullbackTensorCalculus l E W).systemClosed.tensor`, its `.systemTensorModel`, and `coefficientTotalTensor.{u, u + 1, u}`. |
| Good means K-flat with flat terms | `integralOperationsGoodComplex` is precisely `IsKFlatIndependentCoefficients P ∧ ∀ i : ℤ, IsFlatOnSite (P.X i)`; its full subcategory supplies `P Q`. |
| K-flatness tests every acyclic complex | `CochainComplex.IsKFlatIndependentCoefficients` quantifies over all acyclic complexes and uses `mapBifunctor F K (curriedTensor _)`, the direct-sum total tensor. |
| No extra boundedness, constructibility, completeness, or invertibility assumptions | None occurs in the section binders, theorem, good-complex predicate, or normalization. |
| L0 and ordinary reduction with their specified adjunction | `pullbackTensorOrdinaryLimit := coefficientSequenceRestriction ⋙ lim`; `pullbackTensorOrdinaryReduction := ...leftAdjoint`; `pullbackTensorOrdinaryAdjunction := Adjunction.ofIsRightAdjoint _`. |
| Termwise application | `.mapHomologicalComplex (.up ℤ)`. |
| Canonical lambda, including exact-restriction factorization | `pullbackTensorLimitUnit` composes the ordinary-composite complex comparison, `rightDerivedFunctorUnit`, and the inverse `mapDerivedCategoryFactors`. |
| Reordering J and full Roos functor H | `HomologicalComplex.complexOfFunctorsToFunctorToComplex` and `integralOperationsRoosFunctor`; its object is `mappingCocone (towerTransitionEndomorphism ... integralOperationsTowerStep)`. |
| Actual tower transitions in 1-s | `integralOperationsTowerStep C n := C.map (homOfLE (Nat.le_succ n)).op`. |
| j has limit projections and zero shifted coordinate | `pullbackTensorRoosAugmentation` is `Pi.lift` of the termwise `lim.π`; `pullbackTensorRoosUnit` is `mappingCocone.lift` of that augmentation and literal `0`. |
| m is fixed by its derived-adjunction transpose | `pullbackTensorReductionModel` is selected from `pullbackTensorReductionModel_existsUnique`; its equation applies `.adjunction.homEquiv` and equals the localized ordinary adjunction unit followed by `pullbackTensorLimitUnit`. |
| rho is fixed on every K-injective tower | `pullbackTensorRoosModel_existsUnique` specifies `e.hom.app I = (rightDerivedFunctorObjQIso ... I).hom ≫ DerivedCategory.Q.map (pullbackTensorRoosUnit ... I)` for all `[I.IsKInjective]`; `pullbackTensorRoosModel` selects it. |
| Fixed strict tensor tower d | `pullbackTensorTensorTower` selects the unique isomorphism from `pullbackTensorTensorTower_existsUnique`, whose every component is `pullbackTensorTensorTowerLevel`. |
| Ordinary reduction of good P is K-flat | `pullbackTensorReductionGood`; its sequence-site universes are explicitly `u+1, u, u+1`. |
| tau is exactly the fixed coherent K-flat tensor model | `pullbackTensorSystemModel` calls `CoefficientTensorModels.iso` with `.systemClosed` and `.systemTensorModel` of the same chosen calculus. |
| Reference tensor T_ref | `pullbackTensorReferenceTensor` is the product of the two derived reductions, followed by `.systemClosed.tensor` and `coefficientSequenceLimit`. |
| nu first applies L to m_P tensor m_Q | First factor of `pullbackTensorReferenceTensorModel`: `.mapIso` of `.systemClosed.tensor.mapIso (Iso.prod ...reductionModel... ...reductionModel...)`. |
| nu next applies L to inverse tau | Second factor is `.mapIso (pullbackTensorSystemModel ... reductionGood ... reductionGood ...).symm`. |
| nu inserts exact-restriction factorization and rho | Third factor is `pullbackTensorLimitRoos`, whose body is the mapped `mapDerivedCategoryFactors.app C` followed by `pullbackTensorRoosModel.app` of the restricted complex. |
| nu finally applies q H(d) | Final factor is `DerivedCategory.Q.mapIso (integralOperationsRoosFunctor.mapIso (pullbackTensorTensorTower ... P.obj Q.obj))`. Both Roos coordinates are preserved. |
| Actual completed tensor and its fixed epsilon | `integralCompletedTensor` and `integralCompletedTensorComparison` from the existing normalized `IntegralCompletedTensorDescent`, with target `integralOperationsTensorOnGood`. |
| Existence and uniqueness of a natural isomorphism beta | `∃! e : integralCompletedTensor l E W ≅ pullbackTensorReferenceTensor l E W, ...`; these are isomorphisms in the functor category, hence natural isomorphisms. |
| Equation for every good P,Q | `pullbackTensorIntegralTensorNormalization` unfolds to `∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory, e.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) = (integralCompletedTensorComparison l E W).app (P,Q) ≪≫ (pullbackTensorReferenceTensorModel l E W P Q).symm`. |

The equation's orientation is exact: Lean's `epsilon ≪≫ nu.symm` is the node's
`nu⁻¹ ∘ epsilon`. It is equality of full isomorphisms to the specified strict
Roos complex; it does not replace the equation by equality after finite projections.

Dependency declarations read and used by the existing statement:

- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`, preserving the actual coefficient constructions from `CoefficientExtension`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-coef-ringed-sequence-site`: `Sheaf.Paper.CoefficientRingedSequenceSite`, `coefficientSequenceCommRingSheaf`, `coefficientSequenceModules`, `coefficientSequenceEvaluation`, `coefficientSequenceRestriction`, and `coefficientSequenceLimit` in namespace `WeilConjectures`.
- `lem-coef-derived-system-evaluation-calculus`: `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`, `WeilConjectures.coefficientDerivedSystemEvaluationCalculus` and its `CoefficientDerivedSystemCalculus` data. `pullbackTensorCalculus` is the existing selected calculus used throughout the node.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`, `HasDerivedCategory`, and `DerivedCategory.Q`.
- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`, `CochainComplex.IsKFlatIndependentCoefficients`.
- `def-pc-tensor-complex-sheaves`: `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor` with sheaf-module tensor and the usual totalization signs.
- `def-sf-strict-roos-functor`: `Sheaf.Paper.IntegralOperationsWellDefined`, `WeilConjectures.integralOperationsRoosFunctor`.
- `def-pur-integral-derived-operations`: its recorded `Sheaf.Paper.IntegralDerivedOperationsOnSlices`, `WeilConjectures.IntegralOnSlice.completedTensor`, extends the original global interface. The same file retains the original `IntegralDerivedOperations` import and supplies `completedTensor_global_comparison` to the original `integralOperationsTensorOnGood`. This node explicitly names the original actual global `integralCompletedTensor` with its fixed `integralCompletedTensorComparison`, both read in `Sheaf.Paper.IntegralDerivedOperations`; the slice extension is neither substituted for that fixed comparison nor duplicated.
- `lem-pur-coherent-tensor-tower`: `Sheaf.Paper.CompletedPullbackTowerRealizations`, `WeilConjectures.pullbackTensorTensorTower_existsUnique`.
- `lem-pur-coherent-reduction-kflat`: same module, `WeilConjectures.pullbackTensorReductionGood`.
- `def-pur-completed-pullback-tower-core`: `Sheaf.Paper.CompletedPullbackTowerCore`, including the recorded `pullbackTensorFiniteAdjunction`, ordinary adjunction, reduction model, limit unit, restricted tower, Roos unit and Roos model.

Edge cases checked by reading the full signatures and bodies: level `n = 0`
is exponent one, not the zero quotient; zero complexes and the empty scheme
are permitted; complexes can be unbounded in both integer directions; all
scheme characteristics, including characteristic ell, are allowed; neither
input must be derived complete. The good-pair quantifier includes every flat-term
K-flat complex, not only normalized systems. The independent-coefficient K-flat
predicate uses the actual sequence site's object/morphism/module universes
`u+1`/`u`/`u+1`, with no extra size equality imposed.

Searches performed with `msearch.py NJ lem-pur-integral-tensor-roos-realization`:

- `leansearch`: "A unique natural isomorphism of the completed integral derived tensor product with derived coherent reduction tensor followed by derived inverse limit, normalized on K-flat representatives by a strict Roos complex". Eight hits: generic derived-functor comparison, direct-limit tensor and adic-completion results; no exact sequence-site Roos-normalized statement.
- `leanfinder`: "Completed integral tensor has a unique natural isomorphism to derived coherent reduction tensor and inverse limit normalized by the full strict Roos model". Eight hits on ordinary adic-completion tensor lemmas; none states this normalization.
- `loogle`: "CategoryTheory.Functor, CategoryTheory.NatIso". No hits; service reports unknown identifier `CategoryTheory.NatIso`. This is a negative remote query, not evidence about the local declaration.
- `grep`: "pullbackTensorIntegralTensorModel_existsUnique|pullbackTensorIntegralTensorNormalization|Roos". No Mathlib hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for `pullbackTensorIntegralTensorModel_existsUnique|pullbackTensorIntegralTensorNormalization|pullbackTensorReferenceTensor`: exact existing theorem and all its defining comparisons in `CompletedPullbackTowerRealizations.lean`; no upstream duplicate. Searching the item id under `lean/WeilConjectures` returned no match.
- Read the node's `lean_candidates`: it names this very theorem and expressly says the current module is authoritative and the proposed extracted module is only a future extraction. Therefore no extraction or second theorem is appropriate for stage 2.

Sources read: `literature/stacks-project/sites-cohomology.tex`,
`lemma-derived-limit-is-ok` (Tag 0941), and `literature/stacks-project/derived.tex`,
`definition-derived-limit` (Tag 08TC). These justify the sequence-derived-limit
and homotopy-limit comparison used in the node's normalized localization proof.
In particular 08TC notes the nonuniqueness of an unnormalized triangulated
homotopy limit; the existing predicate retains the additional full chain-level
normalization that the present node explicitly requires.

No node fault or disputed statement was found. Validation is by the required
`deliver2.py --no-push`, which invokes `scompile.py` on a module-mode `#check`
probe for the existing declaration, followed by the live server preflight.

## Second reading by NJ

Independent second reading by the maintainer's review (NT-cc, 2026-10-27); the
worker section above states that no worker second reading was made, so this
section replaces that placeholder (H11). The Lean is unchanged.

Node statement, item by item, against `pullbackTensorIntegralTensorModel_existsUnique`
(lean/Sheaf/Paper/CompletedPullbackTowerRealizations.lean:335) and its definitions:

1. ell, E/Q_ell finite, O_E, varpi: section binders `(l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`; quotients via `finiteCoefficientRing l E (n+1)` (n = 0 is O_E/varpi). OK.
2. W : Scheme.{u}: explicit binder. E and W share u, forced by the recorded `def-pur-completed-pullback-tower-core` interface (`integralTowerModules.{t,u}` at t = u); not a new restriction of this node. OK.
3. Sequence site, A_W, S_W, U_W: `coefficientSequenceCommRingSheaf`, `completedIntegralCommRingSheafUnrestricted`, `coefficientSequenceRestriction` (Core). OK.
4. Derived categories / q, q^s, q^t: Mathlib `DerivedCategory.Q`, `pullbackTensorTowerQ`; unbounded. OK.
5. R_W ⊣ L_W, L_W = R lim ∘ D(U_W): `(pullbackTensorCalculus l E W).reduction/.adjunction`, `coefficientSequenceLimit`. OK.
6. Good = K-flat (all acyclic, direct-sum total tensor) with flat terms: `integralOperationsGoodComplex` (IntegralOperationsWellDefined.lean:1776). OK.
7. L^0_W = lim ∘ U_W, r_W = leftAdjoint, η^0: `pullbackTensorOrdinaryLimit` (Core:404), `pullbackTensorOrdinaryReduction` (Core:447), `pullbackTensorOrdinaryAdjunction`. OK.
8. λ_C with exact-restriction factorization: `pullbackTensorLimitUnit` (Core:516). OK.
9. H_W, J_W, s with actual transitions; j_I with limit projections and zero shifted coordinate: `integralOperationsRoosFunctor`, `pullbackTensorRoosAugmentation` (Pi.lift of lim.π), `pullbackTensorRoosUnit` (mappingCocone.lift … 0) (Core:757, 807). OK.
10. m_W fixed by its adjunction transpose λ∘q(η^0): `pullbackTensorReductionModel_existsUnique` (Core:543). OK.
11. ρ_W fixed on every K-injective I as q(j_I)∘rightDerivedFunctorObjQIso.hom: `pullbackTensorRoosModel_existsUnique` (Core:831), Lean order `hom ≫ Q.map unit`. OK.
12. d: `pullbackTensorTensorTower` from `pullbackTensorTensorTower_existsUnique` (lem-pur-coherent-tensor-tower). K-flatness of r^cP: `pullbackTensorReductionGood` (lem-pur-coherent-reduction-kflat), universes u+1,u,u+1. τ: `pullbackTensorSystemModel` = `CoefficientTensorModels.iso` of the same calculus. OK.
13. T^ref = L(R K ⊗^L_s R L): `pullbackTensorReferenceTensor` (line 171). OK.
14. ν in the node's order (L(m_P⊗m_Q), L(τ^{-1}), factorization + ρ via `pullbackTensorLimitRoos`, q H(d)): `pullbackTensorReferenceTensorModel` (line 301). OK.
15. ⊗^ and ε^⊗: `integralCompletedTensor`, `integralCompletedTensorComparison` (IntegralDerivedOperations.lean:148,159), target `integralOperationsTensorOnGood` = q H_W(B^0_⊗(P,Q)). OK.
16. ∃! natural iso β with β_{(qP,qQ)} = ν^{-1}∘ε for every good P,Q: `∃! e : … ≅ …, pullbackTensorIntegralTensorNormalization l E W e`, which unfolds to `∀ P Q, e.app (Q P, Q Q) = ε.app (P,Q) ≪≫ ν.symm`. Orientation and full-isomorphism equality exact. OK.

No extra boundedness, constructibility, completeness, invertibility of ell or
characteristic hypothesis. Edge cases: empty W, zero complexes, unbounded
complexes, characteristic ell, n = 0 (exponent one): all admitted.
One definition per notion: the node's own `lean_candidates` names this theorem;
no duplicate in lean/Sheaf or lean/WeilConjectures. `existing: true` is correct;
the item record changes only its `lean` field (checked against the live node).
Proof remains `sorry`; no new declaration, no compile needed.

Advisories (not faults): the docstrings of this theorem and of ν still tag the
dissolved parent `def-pur-completed-pullback-tower-realizations`; the global
`integralCompletedTensor` is retained publicly behind the recorded slice
interface of `def-pur-integral-derived-operations` (§1(B) note of that node).
