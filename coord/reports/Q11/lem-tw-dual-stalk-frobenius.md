## Worker report

`Sheaf.Paper.DualStalkFrobenius`, `WeilConjectures.dual_stalk_frobenius`, states the node in the actual fixed-pair/common-stage coefficient category. Its only theorem proof is `sorry`. The two supporting definitions contain real predicates, with no chosen data and no postponed theorems. The local-Frobenius dependency is extended by explicit definitions, retaining all its original declarations.

The dual is specified by its internal-Hom universal property, together with invariance of evaluation under the actual Weil structures. This determines the ordinary sheaf dual of a lisse object up to the unique evaluation-preserving isomorphism, and determines its Weil structure as precomposition with theta inverse. The theorem asserts existence of this dual and the stated conclusions for EVERY representing dual. Consequently it applies to the usual named Hom(F,Omega_Y), independently of the representative; it does not substitute an arbitrary object or operator. Representability is tested against every object of the actual constructible derived category, through the actual tensor bifunctor. Naturality in the test object follows from the formula `(f tensor id) >> e`.

Hypothesis and clause correspondence:

| Node text | Lean |
| --- | --- |
| finite field k0=Fq of characteristic p, its algebraic closure k | `D : FiniteFieldDatum.{u}`; the recorded datum includes p, positive extension degree, q, the finite field, and its specified closure |
| prime l different from p | `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)` |
| algebraic closure of Q_l | `(Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]` |
| finite-type k0-scheme Y0 | `Y₀ : Over (Spec (.of D.k₀))`, `[LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]`; these two classes are Mathlib's finite-type condition |
| Y=Y0 base-changed to k | `(D.geometricFiber Y₀).left`, throughout |
| constructible Qbar-Weil sheaf F | `F : sfCommonStageWeilSheaf D l hl Y₀ Ω`, exactly the recorded full subcategory of fixed pairs with carrier in the heart |
| lisse of finite rank | `_hF : IsCommonStageLisse ... F.obj.carrier`, expanded below; this is local rational freeness and imposes no global integral lisse or stable lattice |
| linear dual sheaf with inverse-precomposition Weil structure | `IsCommonStageWeilLinearDual ... F.obj Fv`; its universal pairing represents internal Hom and satisfies `t.hom >> (theta_Fv tensor theta_F) >> e = G.map e >> theta_unit` |
| dual exists | first conjunct `∃ Fv, IsCommonStageWeilLinearDual ...` |
| dual again lisse finite rank | `IsCommonStageLisse ... Fv.carrier`, for every representing dual |
| dual constructible Weil sheaf | `sfCommonStageHeartProperty ... Fv.carrier` together with `Fv : sfCommonStageWeilComplex ...` |
| every closed point y | `y : {y : Y₀.left // y ∈ closedPoints Y₀.left}` |
| every geometric point over y | residue-field embedding `ι : Y₀.left.residueField y.val →+* D.k` and its k0 compatibility `hι`; `localClosedPoint D Y₀ y ι hι` is the recorded geometric lift |
| finite-dimensional original stalk | `FiniteDimensional Ω (localQbarClosedStalk ... F.obj y ι hι)` |
| local geometric Frobenius is an automorphism | `∃ A : stalk ≃ₗ[Ω] stalk, A.toLinearMap = (localQbarClosedFrobeniusStalk ... F.obj ...).hom` |
| Qbar-linear stalk comparison c_y | `∃ c : dualStalk ≃ₗ[Ω] Module.Dual Ω stalk, ...` |
| formula for every lambda and v | `∀ φ v, c (Fdual.hom φ) v = c φ (A.symm v)` |
| inverse-transpose conjugacy | `c.toLinearMap.comp (Fdual.hom.comp c.symm.toLinearMap) = LinearMap.dualMap A.symm.toLinearMap` |

No smoothness, normality, connectedness, positive rank, separatedness, embedding into C, purity, or Frobenius-stable integral lattice is imposed. The site retains object universe u+1 and arrow universe u, and completed module sheaves are in u+1. The theorem uses the recorded point-fibre API's common bound u for geometric fields and algebraic coefficient closure; no site-universe equality is added. The two notion definitions themselves allow an independent coefficient bound v.

Dependency declarations read and used:

* `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilComplex`, `sfCommonStageWeilSheaf`, `sfCommonStageWeilForget`, `sfCommonStageWeilFrobeniusPullback`, and `sfWeilPrimeInvertible`. These are the fixed pairs and heart-carrier notion, not upstream's derived category of Weil sheaves.
* `Sheaf.Paper.LocalFrobeniusTrace`: the original `localPullbackComposition`, `localPositivePower`, `localClosedPoint`, `localClosedPointDegree`, `localClosedPoint_return`, plus this delivery's `localQbar*` constructions. The original finite-stage operators and signatures are preserved verbatim.
* `WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra`: recorded `AlgebraicGeometry.WeilGroup.detLine`, `semisimplification`; read with `scompile.py --source`, since the older source checkout lacks this file. This representation-operations dependency is imported, but it supplies neither the common-stage category nor a linear sheaf dual, so the new definition uses evaluation rather than identifying these distinct categories.
* `Sheaf.Paper.ConstantWeilStructure`: `constantWeilAlgebraicallyClosedComplex`; its explicit least-stage coefficient object and canonical Weil isomorphism are used as the target of evaluation.
* `Sheaf.Paper.CompletedPullbackTensorComparison`: `canonicalCommonStagePullbackTensor`; its finite-stage representative normalization fixes the tensor comparison in the evaluation equation.
* `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`, `commonStageDerivedPullback`, `commonStageDerivedTensor`, and their object specifications. The local-stage comparison is taken from `commonStageDerivedPullback_existsUnique`; finite-stage composition is the original localization of the integral composition comparison.
* `Sheaf.SixFunctors.FrobeniusPointTransport`: `frobeniusPointTransportQbar`, `frobeniusPointQbarPullbackObj`, `frobeniusPointIso`, `frobeniusPointPrimeInvertible`. `Sheaf.Paper.FiniteCoefficientPoint`: `pointQbarFibre`, `pointQbarFibre_existsUnique`, `pointQbarFibreObj`. `Sheaf.Paper.CoefficientCohomologyModules`: `DerivedCategory.coefficientQbarCohomology`.
* Proof imports: `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`, `SheafOfModules.existsUnique_hom_of_cover`; `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback`, `SheafOfModules.finite_free_dual_pullback`; `Sheaf.Paper.PointFibreDerivedTensor`, `pointFibreDerivedTensor`. Their full signatures and proof docstrings were read. `def-pur-sheaf-hom` is the existing `SheafOfModules.homObj` in `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`, imported transitively by the proof modules.
* `lem-tw-lisse-rational-realization` and `lem-weil-frobenius-cohomology-transport-iso` have no Lean records in the read snapshot. They are needed by the later proof, not to type this statement; no unrecorded module import is invented. Their mathematical uses are retained step by step in the theorem docstring.

Edge cases checked before writing and in the second pass:

* Rank zero: `r : ℕ` includes 0, and free on `ULift (Fin 0)` is zero. The unique zero-space endomorphism is a linear equivalence, so the operator/inverse and duality formulas remain meaningful.
* Empty scheme: an empty family can cover its empty terminal pro-etale object; no closed points are quantified. No nonemptiness assumption occurs.
* Different ranks on components: the rank and coefficient stage are quantified inside `∀ i`; a uniform rank is not required.
* A rational lisse object without a global lisse integral lattice: the integral free models are chosen only after restriction to each chart. Neither F nor theta is required to preserve a global integral free model.
* Rank one Frobenius multiplication by a nonzero a: the displayed formula gives a inverse on the dual, not a or a conjugate scalar.
* A nontrivial unipotent 2-by-2 Frobenius block: the formula is inverse transpose, including its sign on the off-diagonal entry.
* Degree r>1 and arbitrary residue embedding: the operator uses r-1 as the positive-power index, hence exponent r, and uses `x >> g_Y^r = g_s^r >> x`; it never uses the false equality `g_Y^r x=x` of scheme maps.
* Finite coefficient fields may be enlarged: all maps use the actual common-stage functors and their literal-stage comparisons. A Weil isomorphism need not be represented over the carrier's initially displayed stage.
* The definition of the dual is unchanged if its representing object is replaced by an isomorphic one: universal evaluation gives the unique isomorphism, and the equivariance equations make it a Weil isomorphism. The theorem deliberately includes every such representative.

Sources opened: the current blueprint's `lem-tw-dual-negation.md` and `.proof.md`; Stacks `sites-modules.tex`, `example-dual` (0FNY) and `remark-pullback-internal-hom` (0GMX); all three statement-dependency records, their source signatures/docstrings, and every available proof-dependency interface listed above. The item is a proof child of the weight-negation statement; no unit statement or natural-language node statement is changed. No statement dispute was found.

Searches for the item: msearch LeanFinder query “The stalk of the dual of a lisse finite rank Weil sheaf is the linear dual stalk with inverse transpose Frobenius” returned eight ordinary stalk/structure-sheaf hits, headed by `ModuleCat.Tilde.stalkIso_hom`. Loogle `"stalk", "dual"` returned zero hits. msearch grep `stalk.*dual|dual.*stalk` returned zero Mathlib hits. Direct rg of WeilConjectures and lean/Sheaf found `WeilSheaf.stalkAtDualEquiv` and `nonempty_equiv_stalk_dual`, the different concrete coefficient model expressly excluded by the node's proof; `SixFunctors/ProEtale/Adic/StalkEvaluation` is likewise that adic model. `AdicLisseCohomologyCalculus` uses a different lisse category and separated schemes. Neither is an exact existing match. Searching the item id in WeilConjectures found no match. Additional three-kind searches for the new notions are recorded in their `mathlib_searches` and summarized below.

## New nodes

`def-real-common-stage-lisse`, module `Sheaf.Paper.CommonStageLocallyFree`: the exact local rational finite-free condition in the recorded common-stage category. It uses pro-etale covers of the terminal object; each chart has a finite coefficient stage and an integral constructible object whose underlying derived module is the actual finite free completed module in degree zero. Only the local objects are integral free. Sources: Bhatt–Scholze 6.8.3, 6.8.14(2), 6.8.15, as used in the source realization lemma and dual argument. The DAG search `blueprint_refs.py search lisse` and direct DAG text searches found `def-a1-common-stage-lisse-lattice`, which requires a GLOBAL lisse integral lattice and is therefore not used on arbitrary nonseparated Y. The realization lemma has no recorded declaration. LeanSearch returned ordinary free modules/linear duals; LeanFinder returned condensed internal-Hom APIs; exact-name rg over Mathlib, WeilConjectures and lean/Sheaf found no predicate. The module contains one real definition and no theorem.

`def-real-common-stage-weil-linear-dual`, module `Sheaf.Paper.CommonStageWeilLinearDual`: the internal-Hom universal pairing with its Weil-equivariance equation, using the published tensor and coefficient-unit structure. Source: the blueprint's dual representation sentence and Stacks 0FNY/0GMX. DAG searches for duality and representable internal Hom found ordinary sheaf Hom, Verdier duality and representation duals, not a dual interface for the repaired common-stage fixed-pair category. LeanFinder “Internal Hom representing linear dual with invariant evaluation for a Weil sheaf” returned eight LightCondensed/FGModuleCat declarations; none concerns common-stage Weil sheaves. LeanSearch returned ordinary free/dual APIs. Loogle `"Hom", "Bijective"` returned unrelated algebra and concrete-category facts. msearch grep and exact-name direct rg found no declaration. This is a real Prop-valued definition, not a chosen dual, and does not assume the desired stalk comparison.

## Dependency modules

`def-weil-local-frobenius-trace`, `Sheaf.Paper.LocalFrobeniusTrace`: the recorded module gives the finite-field-coefficient E operators; the item requires their common-stage algebraic-closure counterpart. The delivery retains the original file verbatim and appends `localQbarPullbackStageIso`, `localQbarPullbackComposition`, `localQbarDerivedStalk`, `localQbarPointComplex`, `localQbarStalk`, `localQbarWeilIterate`, `localQbarFibreObjIso`, `localQbarPointPullbackIso`, `localQbarPointTransport`, `localQbarPointTransportIterate`, `localQbarReturnComparison`, `localQbarClosedFrobenius`, `localQbarClosedFrobeniusStalk`, and `localQbarClosedStalk`. The common-stage composition is the published rational composition at the literal stage with the actual object comparisons. The point transport is exactly the recorded restriction/coprojection map and its prescribed identifications. The return and residue-degree constructions are reused unchanged. There is no new axiom, postponed helper theorem, inverse/operator choice, or strengthened hypothesis. Only the dependency's `lean` record changes.

## Second reading by Q11

This is the author's separate second pass, with the node and all four files open; the dispatcher expressly forbids starting another agent, and the maintainer performs the independent delivery review. I do not claim an independent worker reading.

I checked every row of the correspondence table against the statement and definitions. The relevant distinction is global integral lisse lattice versus local rational freeness: the latter is used, with rank zero and separate local ranks. I checked that the dual predicate represents Hom into the canonical coefficient unit and uses theta_F and theta_Fv on the correct side of the canonical pullback-tensor map. Consequently its action is inverse precomposition, rather than direct transpose. I checked that the local operator definitions use the existing semilinear return, and that A is required to equal that actual operator. The c equation and the final conjugacy equation have the same inverse orientation. I checked that there is no separatedness or positive-rank hypothesis. The old dependency declarations are preserved. The first compile found an unqualified `ProEt.topology`; opening the existing Scheme namespace fixed the name without changing any notion. No mathematical mismatch or node correction was found. Compilation and dry-run results are recorded after the final checks.

Compiler follow-up: Lean reserves λ as a syntax token; renamed the bound functional to φ. This changes no type or formula.

Final scompile verification: all four modules passed together in dependency order through `scompile.py Q11 lem-tw-dual-stalk-frobenius`, exit 0, with no compiler diagnostics. The wrapper checked each separately as sandbox and library modules. The earlier dry run had captured the pre-fix λ binder; its only failure was that same parser diagnostic, and the dry run was restarted on the corrected source. No timeout limit was changed.
