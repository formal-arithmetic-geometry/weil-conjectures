## Worker report

Stage 2 repair, Q142, lem-tw-finite-projective-model-pullback.
The module is `Sheaf.Paper.FiniteProjectiveModelPullback`; its main declaration is
`WeilConjectures.FiniteProjectivePullback.finiteProjectiveModelPullback`.
The accepted mathematical statement and six proof steps are unchanged. The delivery
changes only `lean` and `stmt_deps` relative to the current live node. All theorems
have `sorry` proofs, all definitions have actual data, and `comparison` is chosen
from a named unique-existence characterization, with no arbitrary comparison input.

The return on immutable head ea3fc17b97e6 is repaired as follows:

1. H4: deleted `Scalars`, `Modules`, `finiteDirectMap`, `directMap_existsUnique`,
   `directMap`, `push`, `pull`, `adjunction`, and `pull_additive`. Every signature
   now uses the published `PbcIntegralRing`, `integralTowerModules`,
   `ordinaryIntegralDirectRingMap`, `ordinaryIntegralModulePull`, and
   `ordinaryIntegralModuleAdjunction` directly. The imported construction supplies
   its own right-adjoint and additive instances. The item cites their owning
   definition node `def-sf-ordinary-integral-pullback-construction`. As explicitly
   requested in the return, schemes are `Scheme.{u}` and `E : Type u`. The small
   site still has objects in `Type (u+1)` and morphisms in `Type u`; no equality of
   those two universes is imposed. This is the same ordinary pullback used by the
   sole citer `lem-tw-ordinary-pullback-stratified-models`, whose published
   `perfectModelPullback` uses `PbcIntegralRing` and `integralTowerModules` too.
2. Theorem statement dependency: the two counit expressions now write the actual
   `epsilon.app ((HomotopyCategory.quotient _ (.up ℤ)).obj M)` inline, preceded by
   `LF.map (quotientCompQhIso.inv.app M)` and followed by the pullback homotopy
   factorization and `quotientCompQhIso.hom`. These are precisely the four factors
   in the published ordinary cochain computation counit. No use of
   `ringedPullbackComplexComparison` remains. The strict-perfect theorem is kept
   only as a non-public proof import, as the unchanged proof step 6 requires.
3. H2: the two theorem additions have been removed from `stmt_deps`:
   `lem-weil-pbc-strict-perfect-ringed-pullback-model` and
   `lem-pur-ringed-site-module-pullback-exists-universes`. Only two landed
   DEFINITION nodes are added: the ordinary construction above and
   `def-weil-pbc-strict-perfect-coefficient-package` for its recorded constant
   scalar-extension API. This follows brief-stage2 §5's landed-node rule and the
   return's instruction to cite the ordinary-construction definition. No new
   definition node or dependency repair module is needed.

The earlier saved packet passed the required initial dry run (f25c9cda48a).
That mechanical result did not resolve the independent return; the present Lean
and record contain the actual interface repair described above.

Clause-by-clause correspondence (unqualified names refer to
`WeilConjectures.FiniteProjectivePullback`):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Prime ell, finite E/Q_ell, valuation ring R and chosen uniformizer | `l`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`; the published `PbcIntegralRing l E` lifts the actual integer ring. The coefficient system uses the dependency's chosen uniformizer. |
| Arbitrary schemes and small pro-etale sites | `T : Scheme.{u}`, `T.ProEt` and `ProEt.topology T`; object and Hom universes remain u+1 and u. |
| Positive quotient system, completed B_T and its projections | The imported ordinary construction uses `integralCoefficientSheafSystem`, `completedIntegralCoefficientSheafUnrestricted` and `limit.π`; index n represents exponent n+1. `completedIntegralCommRingSheafUnrestricted.{u,u}` retains the same ring with its commutative structure. |
| Arbitrary v:V→U with constant-section coefficient maps | `{V U : Scheme.{u}} (v : V ⟶ U)` has no geometric restrictions. The published `ordinaryIntegralFiniteDirectRingMap` and `ordinaryIntegralDirectRingMap_existsUnique` give exactly the finite-projection characterization. |
| Specified c_v and ordinary tensor pullback | `ordinaryIntegralDirectRingMap` is its direct-image adjoint. `ordinaryIntegralModulePull` is the published sheafified module Kan-extension left adjoint, with unit from `ordinaryIntegralModuleAdjunction`. No second map, functor or adjunction is defined here. |
| Ordinary module and unbounded derived categories | `integralTowerModules.{u,u}` and Mathlib `DerivedCategory`, `Q`, `Qh`. The main theorem binds `[HasDerivedCategory.{w} ...]` at both endpoints, with arbitrary w. |
| P_v=Lv_B^* with specified computation counit | `LF`, `epsilon`, `[LF.IsLeftDerivedFunctor epsilon (HomotopyCategory.quasiIso ...)]` present the given universal derived functor. The two conclusion arrows use that very epsilon on the quotient, with canonical cochain localization isomorphisms. |
| Bounded scalar cochain complex | `L : CochainComplex (ModuleCat.{u+1} (PbcIntegralRing l E)) ℤ`, `a b : ℤ` and `_hbounded : ∀ q, q<a ∨ b<q → IsZero (L.X q)`. Empty or reversed intervals are allowed. |
| Terms are finite-free direct summands | `hL q : Module.Finite R (L.X q) ∧ Module.Projective R (L.X q)`, the standard equivalent finite-projective property. `Projectives` uses Mathlib's full subcategory on this property. |
| Canonical constant R→B_T with prescribed quotient maps | `scalar` is the commutative preimage of the published `integralConstantToCompletionOfUniverses.{u,u}`, the actual limit lift of the constant quotient cone. |
| M_T=B_T tensor underline L over underline R | `model` uses the recorded `scalarPerfectFunctor` (constant module sheafification, then ordinary extension of scalars); `modelComplex` applies it to the original terms and differentials. `modelSection` uses the two actual sheafification units. |
| Natural isomorphism gamma_L | `comparison_existsUnique` and `comparison` give the uniquely generator-normalized natural isomorphism on all finite projectives and every linear map. `complexComparison` uses its actual degree components and `HomologicalComplex.Hom.isoOfComponents`. |
| Forward free formula b tensor (a e_j) ↦ b c_v(a)e_j | First conjunct of `comparison_free`, for every rank r, coordinate j, source section a and target coefficient b. It explicitly evaluates `ordinaryIntegralDirectRingMap` on a. |
| Inverse free formula b e_j ↦ b tensor e_j | Second conjunct of `comparison_free` uses the same `comparison.inv`, the standard coordinate vector, and `b • generator (... modelSection ... 1 ...)`. |
| Local sections and restriction compatibility | `generator` evaluates the actual published adjunction unit at every source-site object W. Such sections and their restrictions locally generate inverse image and tensor sheafification. The formulas are sheaf formulas, not just global-section identities. |
| Every specified finite-free splitting and same scalar idempotent | `comparison_retract` quantifies over P,r,i,p with `i ≫ p = 𝟙`. Its two retract formulas and inclusion identity use precisely the given scalar i,p and their images under `model` and `ordinaryIntegralModulePull`. |
| Splitting independence and naturality in every linear map | `comparison` takes no splitting argument and is a natural isomorphism on the full finite-projective subcategory. `comparison_retract` holds for every splitting, including two different ones on the same P. |
| Compatibility with specified differentials | `comparison_differential` applies naturality to `L.d i j`; this equation supplies the actual chain-map compatibility in `complexComparison`. No free chain splitting is assumed. |
| Every M_U term flat | First conjunct of `finiteProjectiveModelPullback`: `∀ q, SheafOfModules.IsFlatOnSite` of the actual realized term. |
| M_U K-flat | Second conjunct: `CochainComplex.IsKFlatIndependentCoefficients` for the actual realized complex. |
| Specified ordinary computation counit invertible | Third conjunct: `IsIso` of the supplied epsilon at the quotient, transported between the canonical Q and Qh presentations by the three displayed isomorphisms. |
| Derived comparison epsilon followed by [gamma_L] | Fourth conjunct is exactly the preceding four-factor cochain counit followed by `DerivedCategory.Q.map (complexComparison ...).hom`. |
| No scalar-ring flatness, structural-map flatness or completion | No such hypotheses occur. All realization tensors, pullbacks, quotients and comparison arrows are ordinary; the ring B itself is the completed coefficient ring. |

Dependency declarations read and reused:

- `Sheaf.Paper.OrdinaryCompletedIntegralPullback`:
  `ordinaryIntegralFiniteDirectRingMap`, `ordinaryIntegralDirectRingMap_existsUnique`,
  `ordinaryIntegralDirectRingMap`, `ordinaryIntegralModulePush_isRightAdjoint`,
  `ordinaryIntegralModulePull`, `ordinaryIntegralModuleAdjunction`, and
  `ordinaryIntegralModulePull_additive`, owned by
  `def-sf-ordinary-integral-pullback-construction`.
- `Sheaf.Paper.BoundedConstructibleComplete`: `AlgebraicGeometry.Scheme.PbcIntegralRing`.
- `Sheaf.Paper.IntegralReductionTowerUnrestricted`: `integralTowerModules`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: coefficient extension
  definitions and the positive quotient finiteness interface.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and the completed/finite coefficient
  sheaves it imports, with their actual constant quotient cone.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` and
  `Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses`:
  `proEtaleBaseChange` and `coefficientProEtaleDirectRingMap`, used by the
  ordinary coefficient construction.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, the unchanged
  Mathlib `SheafOfModules` encoding underlying `integralTowerModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `Q`, `Qh`, `quotientCompQhIso`;
  Mathlib's `mapHomotopyCategoryFactors` gives the canonical middle transport.
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`:
  `SheafOfModules.ringedTopoiDerivedPullbackIndependent`, whose LF/epsilon
  presentation and quotient-evaluated computation map are used here.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  sheaf and cochain tensor interface.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`, through the
  recorded scalar-perfect constant functor.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`: `scalarPerfectRing`,
  `scalarPerfectFunctor`, `scalarPerfectConstantFunctor`,
  `scalarPerfectConstantSection` and `scalarExtensionSection`.
- The proof-only imports are `StrictPerfectRingedPullbackModel`,
  `ConstantLeftModuleInverseImage` and `SiteInverseImageTensor`, matching the
  unchanged proof's strict-perfect, constant inverse-image and exactness steps.
- `def-weil-scheme-morphism-properties` is the convention node; its maps are
  ordinary Mathlib scheme morphisms.

Searches made using the prescribed msearch wrapper with Q142 and this item:

1. LeanFinder: "Bounded constant finite projective module complexes under ringed
   topos pullback normalized on bases and direct summands with K-flat computation
   counit". Eight hits concern internal projectivity of light condensed free
   modules, ordinary Module.Flat.of_projective and finite-presentation flatness.
   None supplies the requested coefficient limit, normalization and counit.
2. Loogle: `SheafOfModules.pullbackObjFreeIso`. Five free-pullback and naturality
   hits. Read the declarations and docstrings in PullbackFree.lean:100-143.
   These concern free sheaves and do not state this bounded scalar-projective
   comparison, its arbitrary splitting normalization or its derived counit.
3. Grep: `pullbackObjFreeIso|KFlat|scalarPerfect` in
   `Algebra/Category/ModuleCat/Sheaf`. Five PullbackFree hits; same distinction.
4. LeanSearch: "Ordinary derived pullback of a bounded constant finite projective
   sheaf complex preserves the scalar idempotents and is computed by its K flat
   counit". Eight hits provide sheaf inverse-image left exactness, free sheaf
   naturality, identity pullback comparisons and scheme module additivity.
   None states the requested comparison with all normalizations.
5. Read-only rg searches in both `lean/WeilConjectures` and `lean/Sheaf`:
   the exact item id; `finiteProjectiveModel|FiniteProjectiveModel|modelPullback`;
   `finiteProjectiveModelPullback|FiniteProjectivePullback|normalized.*[Pp]rojective`.
   The exact item has no upstream declaration. The existing
   `OrdinaryPullbackStratifiedModels.modelPullback_existsUnique` and
   `perfectModelPullback` were read in full. They fix the scheme and coefficient
   universes together and omit flatness/K-flatness from the latter signature.
   They do not state every flatness, K-flatness and normalized-retract clause.
   The repaired module reuses their ordinary module category and pullback;
   it introduces no alternate tensor, constant sheaf, ring or derived category.


Repair search/read checks: inspected the full published ordinary construction and
its owning node, the sole citer's `perfectModelPullback`, the definition of
`PbcIntegralRing`, and `integralTowerModules`. The returned copies were removed
rather than rebound or generalized. No additional mathematical notion is introduced.
Read the source text in `literature/stacks-project/sites-cohomology.tex` at
`lemma-bounded-flat-K-flat` (06YQ), `lemma-derived-base-change` (06YY), and
`lemma-strictly-perfect-pullback` (08H3). The six proof steps and their sources are
retained verbatim in the DAG; the main theorem docstring gives their full argument.

Edge cases: rank zero and zero L; empty schemes; identity v and arbitrary nonflat
structural maps; complexes with one term; empty/reversed bounds forcing the zero
complex; zero/identity idempotents; distinct splittings of the same P; arbitrary
rectangular scalar maps and a differential that does not preserve chosen free
splittings. None is excluded. These are the edge cases already checked in the
accepted mathematical reading, and the repair changes none of those hypotheses.
There is no statement correction or unresolved dispute.

## Second reading by Q142

This is the dispatcher's worker self-check, not a claim that another agent read
the packet. No sub-agent was started; the maintainer supplies independent review.

With the repaired file and live node open, I checked every table row above. In
particular, both the comparison and generator now contain the published ordinary
pullback and its published unit, and the basis formula evaluates the published
coefficient map. `PbcIntegralRing` is the same ULift of the actual integer ring
used by the sole citer. Both small-site universes retain their distinct sizes.
The three factors surrounding epsilon are canonical isomorphisms, and the final
factor is precisely localized gamma. The retract inclusion equation still uses
the specified i,p; every linear map and every differential is covered. The main
statement still has four conjuncts (flat terms, K-flat, counit invertible, composite
invertible), with no extra flatness/completeness hypotheses.

The changes from the returned head are substantive: all nine redundant declarations
are gone, two theorem statement dependencies are gone, the ordinary owning definition
is cited, and both cochain counit expressions are inline. The strict-perfect theorem
is proof-only. The inherited comment about independent scheme/coefficient universes
was corrected to the explicitly requested published common-u convention. No new
node, dependency module or mathematical statement change was required.

Validation: the repaired module passed `scompile.py` in both sandbox and actual-module
passes (11.4 s / 11.2 s), with no errors or warnings. Generic imported coefficient
sheafification and essentially-small instances whose coefficient universe occurs
only in a max were disabled for this module, allowing the existing canonical
small-site instances to elaborate at u+1. No new instance, local notation, private
notion, typeclass hypothesis or universe constraint was introduced.

Consumer validation: a scratch application specialized the repaired theorem to
`ordinaryIntegralDerivedPull` and `ordinaryIntegralPullCounit`, using Mathlib's
existing total-left-derived universal property after unfolding those two wrappers.
Its third conjunct elaborated directly as
`IsIso (ordinaryIntegralPullComplexCounit ... ((modelComplex ...).obj L))`.
This verifies that the result applies to the published ordinary construction used
by the sole citer, without a second pullback or a coefficient-map equality premise.
The scratch file is not part of the delivery.
