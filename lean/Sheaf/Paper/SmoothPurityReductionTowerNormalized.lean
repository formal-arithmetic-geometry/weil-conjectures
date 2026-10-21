/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.ProEtaleConstructibleSheaf
import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.Paper.CompletedConstantSheafReduction
import WeilConjectures.ConstructibleSheaf.Refinement
import Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.Paper.CondensedConstantConstructibility
import Sheaf.Paper.SmoothPurityCoefficientTowers

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
/-!
# The reduction tower is normalized

Source: blueprint main-20261015, sec-smooth-purity,
`sk-def-sp-normalized-towers/sk-def-sp-normalized-towers-reduction.md`
(blueprint: det-sp-reduction-tower-normalized).

The source is the sectionwise realization of the pulled-back condensed integer ring.
Its comparison with the completed ring is fixed on the underlying abelian sheaf by
`sfb_integral_coefficient_limit`. Positive exponent n+1 is represented by n : ℕ.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The existing condensed integral coefficients, as an abelian sheaf on the point.
Source: blueprint, completed integral coefficients
(blueprint: det-sp-reduction-tower-normalized). -/
abbrev spIntegralCondensed := (sfbCondensedIntegers l E).X

/-- Commutativity of the continuous-function integral coefficients, with their existing
ring-object structure. Source: blueprint, integral coefficients
(blueprint: det-sp-reduction-tower-normalized). -/
instance spIntegralCondensedComm : IsCommMonObj (spIntegralCondensed l E) :=
  letI := spectralNorm.normedField (Padic l) E
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse
    (Padic.coefficientExtensionIntegers l E)

/-- The section-ring realization of the actual pulled-back integral coefficient sheaf.
Source: blueprint, R_T; Stacks 00YV
(blueprint: det-sp-reduction-tower-normalized). -/
abbrev spIntegralSectionRing :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
    (condensedRingObj (spIntegralCondensed l E) T)

/-- Modules over R_T, using the recorded sectionwise/internal equivalence.
Source: blueprint, ordinary unbounded derived source
(blueprint: det-sp-reduction-tower-normalized). -/
abbrev spIntegralSectionModules :=
  ringedSiteModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (spIntegralSectionRing l E T))

/-- The standard localization of integral section-module complexes.
Source: blueprint, D(R_T) (blueprint: det-sp-reduction-tower-normalized). -/
instance spIntegralSectionHasDerived : HasDerivedCategory (spIntegralSectionModules l E T) :=
  HasDerivedCategory.standard _

/-- The recorded equivalence, with unchanged underlying sections and linear maps.
Source: blueprint, identification of coefficient-module presentations; Stacks 00YV
(blueprint: det-sp-reduction-tower-normalized). -/
abbrev spIntegralModuleEquivalence :=
  InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
    (condensedRingObj (spIntegralCondensed l E) T)

/-- The exact inverse equivalence on ordinary unbounded derived categories.
Source: blueprint, Dbc and Tor amplitude over the pulled-back integral ring
(blueprint: det-sp-reduction-tower-normalized). -/
def spIntegralInternalization :
    DerivedCategory (spIntegralSectionModules l E T) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (spIntegralCondensed l E) T)) :=
  letI := Functor.additive_of_preserves_binary_products
    (spIntegralModuleEquivalence l E T).inverse
  (spIntegralModuleEquivalence l E T).inverse.mapDerivedCategory

/-- The canonical integral comparison selected by its projection normalization on
profinite test objects. The existence theorem determines this object uniquely after
its finite-label representation is chosen; it is not a choice of an arbitrary map.
Source: blueprint, completed integral sheaf; integral-limit clause (3)
(blueprint: det-sp-reduction-tower-normalized). -/
def spIntegralAbComparison :
    (condensedRingObj (spIntegralCondensed l E) T) ≅ sfbCompletedIntegersAb l E T :=
  (sfb_integral_coefficient_limit l E T).choose_spec.choose_spec.choose_spec.2.2.2.2.2.choose

/-- The canonical ell-power projection, retaining the commutative ring structure.
Source: blueprint, R_T -> R_(T,n+1), coefficient-limit normalization
(blueprint: det-sp-reduction-tower-normalized). -/
def spIntegralEllProjection (n : ℕ) :
    WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T ⟶
      (spCoefficientCommRings l E T).obj (op n) :=
  (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).preimage
    ((sp_completed_coefficient_limit l E T).exists.choose.hom ≫
      limit.π (spCoefficientRings l E T) (op n))

/-- The actual scalar map defining M/ell^(n+1), in the section-ring presentation.
Source: blueprint, derived reduction formula
(blueprint: det-sp-reduction-tower-normalized). -/
abbrev spIntegralReductionScalar
    (e : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T) (n : ℕ) :=
  e.hom ≫ spIntegralEllProjection l E T n

/-- The ordinary localization of strict tower complexes in the localization chosen
by the recorded coefficient-tower lemma.
Source: blueprint, D(Tow) (blueprint: det-sp-reduction-tower-normalized). -/
abbrev spTowerLocalization (D : SpCoefficientTowersAbelian l E T) :
    CochainComplex (spCoefficientTowers l E T) ℤ ⥤ spDerivedCoefficientTowers l E T D :=
  @DerivedCategory.Q (spCoefficientTowers l E T) _ _ D.hasDerived

/-- The level condition of the canonical reduction construction.
Source: blueprint, normalized-towers-reduction
(blueprint: det-sp-reduction-tower-normalized). -/
def spReductionOrdinaryLevels (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (ordinary : spIntegralSectionModules l E T ⥤ spCoefficientTowers l E T) :=
  ∀ n : ℕ, ordinary ⋙ spCoefficientEvaluation l E T D.equivalence n ≅
    (D.scalar (spIntegralReductionScalar l E T coefficient n)).model.E

/-- The local tensor generator transported to the strict ordinary reduction tower.
Naming this map keeps the kernel from repeatedly comparing the sectionwise scalar-model
presentations in the transition predicate. It is the same scalar-first pure tensor.
Source: blueprint, quotient-induced transition formula
(blueprint: det-sp-reduction-tower-normalized). -/
def spReductionGenerator (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (ordinary : spIntegralSectionModules l E T ⥤ spCoefficientTowers l E T)
    (level : spReductionOrdinaryLevels l E T D coefficient ordinary)
    (M : spIntegralSectionModules l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (c : ((spCoefficientCommRings l E T).obj (op n)).obj.obj U)
    (x : M.val.obj U) :
    ((D.equivalence.functor.obj (ordinary.obj M)).level n).val.obj U :=
  ((level n).inv.app M).val.app U
    (systemModelTmul (D.scalar
      (spIntegralReductionScalar l E T coefficient n)).model M U c x)

/-- The section function of the actual strict transition, after forgetting restriction
of scalars. Its underlying additive sections are unchanged. Keeping the ring tower
abstract here avoids unfolding its concrete constant quotient rings in kernel conversion.
Source: blueprint, quotient-induced transitions
(blueprint: det-sp-reduction-tower-normalized). -/
def spStrictTransitionSection
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (C : StrictRingSystem.{u + 1, u, u + 1} B) {m n : ℕ} (h : m ≤ n)
    (U : T.ProEtᵒᵖ) (x : (C.level n).val.obj U) : (C.level m).val.obj U :=
  (C.transition h).val.app U x

/-- The transition condition of the canonical reduction construction.
Source: blueprint, normalized-towers-reduction
(blueprint: det-sp-reduction-tower-normalized). -/
def IsSpReductionTransition (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (ordinary : spIntegralSectionModules l E T ⥤ spCoefficientTowers l E T)
    (level : spReductionOrdinaryLevels l E T D coefficient ordinary) : Prop :=
  ∀ (M : spIntegralSectionModules l E T) {m n : ℕ} (h : m ≤ n)
    (U : T.ProEtᵒᵖ) (c : ((spCoefficientCommRings l E T).obj (op n)).obj.obj U)
    (x : M.val.obj U),
    spStrictTransitionSection T (spCoefficientCommRings l E T)
      (D.equivalence.functor.obj (ordinary.obj M)) h U
      (spReductionGenerator l E T D coefficient ordinary level M n U c x) =
    spReductionGenerator l E T D coefficient ordinary level M m U
      (((spCoefficientCommRings l E T).map (homOfLE h).op).hom.app U c) x

/-- The evaluation condition of the canonical reduction construction.
Source: blueprint, normalized-towers-reduction
(blueprint: det-sp-reduction-tower-normalized). -/
def spReductionDerivedEvaluations (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (red : DerivedCategory (spIntegralSectionModules l E T) ⥤
      spDerivedCoefficientTowers l E T D) :=
  ∀ n : ℕ, red ⋙ spDerivedCoefficientEvaluation l E T D n ≅
    (D.scalar (spIntegralReductionScalar l E T coefficient n)).model.T

/-- The constructible condition of the canonical reduction construction.
Source: blueprint, normalized-towers-reduction
(blueprint: det-sp-reduction-tower-normalized). -/
def IsSpReductionConstructible (D : SpCoefficientTowersAbelian l E T)
    (red : DerivedCategory (spIntegralSectionModules l E T) ⥤
      spDerivedCoefficientTowers l E T D) : Prop :=
  CompactSpace T → QuasiSeparatedSpace T →
    ∀ M : DerivedCategory (spIntegralSectionModules l E T),
      constantModelBoundedConstructible (spIntegralCondensed l E) T
        ((spIntegralInternalization l E T).obj M) →
      DerivedCategory.finiteTorAmplitude _ ((spIntegralInternalization l E T).obj M) ∧
      spNormalizedConstructibleTorTowers l E T D (red.obj M) ∧
      ∀ (a b : ℤ), a ≤ b →
        DerivedCategory.torAmplitudeIn _ a b ((spIntegralInternalization l E T).obj M) →
        ∀ n : ℕ,
          Scheme.HasProEtaleTorAmplitude T
            (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
            ((spDerivedCoefficientEvaluation l E T D n).obj (red.obj M)) a b ∧
          ∀ i : ℤ, (i < a ∨ b < i) → IsZero
            ((@DerivedCategory.homologyFunctor
              (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T
                (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))
              _ _ (HasDerivedCategory.standard _) i).obj
              ((spDerivedCoefficientEvaluation l E T D n).obj (red.obj M)))

/-- The reduction construction and its assertions. The ordinary functor is fixed by
its level tensor identifications and by its quotient formula on local tensor generators.
The derived functor is its universal left derived functor, computing on K-flat complexes.
This specifies a strict object of D(Tow), rather than only an inverse system in D(R_T).
Source: blueprint, construction, normalization, and final Tor-bound sentence
(blueprint: det-sp-reduction-tower-normalized). -/
structure SpReductionTower (D : SpCoefficientTowersAbelian l E T) where
  /-- The integral ring identification, with its underlying sheaf map fixed below. -/
  coefficient : spIntegralSectionRing l E T ≅
    WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T
  /-- It is precisely the canonical pulled-back/completed coefficient comparison. -/
  coefficient_normalized : ∀ (U : T.ProEtᵒᵖ)
    (x : (condensedRingObj (spIntegralCondensed l E) T).obj.obj U),
    coefficient.hom.hom.app U x = (spIntegralAbComparison l E T).hom.hom.app U x
  /-- Degreewise reduction, with genuine module-sheaf tower values. -/
  ordinary : spIntegralSectionModules l E T ⥤ spCoefficientTowers l E T
  /-- The ordinary reduction functor is additive. -/
  [additive : ordinary.Additive]
  /-- At every positive level it is the existing sheafified scalar extension. -/
  level : spReductionOrdinaryLevels l E T D coefficient ordinary

  /-- The strict transition is induced by the quotient of coefficients, on every
  local tensor generator; tensor generation and sheafification determine the map. -/
  transition : IsSpReductionTransition l E T D coefficient ordinary level

  /-- Functorial reduction on the ordinary unbounded derived categories. -/
  red : DerivedCategory (spIntegralSectionModules l E T) ⥤
    spDerivedCoefficientTowers l E T D
  /-- The universal comparison to degreewise reduction. -/
  counit : DerivedCategory.Q ⋙ red ⟶
    ordinary.mapHomologicalComplex (.up ℤ) ⋙ spTowerLocalization l E T D
  /-- Localization makes this the derived reduction of the specified strict functor. -/
  universal : red.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso (spIntegralSectionModules l E T) (.up ℤ))
  /-- K-flat representatives compute the strict reduction tower. -/
  computes : ∀ P : CochainComplex (spIntegralSectionModules l E T) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T) P →
      IsIso (counit.app P)
  /-- The evaluated functors are exactly derived extension to the quotient coefficients. -/
  evaluation : spReductionDerivedEvaluations l E T D coefficient red

  /-- Every actual transition-adjoint reduction map is an isomorphism, without qcqs. -/
  normalized : ∀ M : DerivedCategory (spIntegralSectionModules l E T),
    IsSpNormalizedTower l E T D (red.obj M)
  /-- On qcqs schemes bounded constructible integral objects give normalized finite-Tor
  constructible towers and themselves have finite Tor amplitude. Every Tor interval of
  M bounds both Tor amplitude and cohomological support at every positive level. -/
  constructible : IsSpReductionConstructible l E T D red
/-- Reduction is functorial into the ordinary derived category of strict coefficient
 towers, all its reduction maps are isomorphisms, and on qcqs schemes it carries
 bounded constructible integral complexes to normalized constructible finite-Tor towers,
 preserving every Tor interval, also as a cohomological interval at every level.
Source: blueprint main-20261015, normalized-towers-reduction; Stacks 06YS, 06YY, 0G7E
(blueprint: det-sp-reduction-tower-normalized).

Proof:
1. Resolve M by a flat-term K-flat complex P (lem-pc-kflat-resolution). In each degree
form P^q tensor_R R_n, with differential d tensor 1 and transition x tensor c maps to
x tensor its quotient. These are strict semilinear towers (coefficient-towers-abelian).
Chain maps and homotopies tensor componentwise.
2. Quasi-isomorphisms between these K-flat complexes induce levelwise quasi-isomorphisms
(derived-change-of-rings). Exact tower evaluations detect them, so localization of the
K-flat resolving class descends the functor to D(R_T), with its universal comparison.
This uses site-derived-tensor-descent and localization-universal-property; it gives
strict derived tower objects, not just derived level systems.
3. Pullback along R -> R_n preserves flat-term K-flat complexes (ringed-topos-kflat-
pullback). Therefore double reduction is computed by ordinary double tensor. Its map
sends (x tensor c) tensor d to x tensor quotient(c)*d; the inverse inserts 1. Balancing
and sheafification give mutually inverse chain maps. These are the specified transition
adjuncts. Equal indices give the tensor unitor, and three indices give the same product.
4. For qcqs T, the integral clause of localizing-closure-ctf-equals-bc applies directly
to bounded constructible M on T and supplies finite Tor amplitude, with bound [r-1,s]
for any cohomological support interval [r,s].
5. For any R_n-module N in degree zero, single-factor K-flat computation from ringed-
projection-mate-exact identifies (M tensor_R R_n) tensor_(R_n) N with M tensor_R Res N.
The ordinary balancing isomorphism sends (x tensor c) tensor y to x tensor cy. Thus
every Tor interval of M works for every finite reduction; R -> R_n need not be flat.
6. Refine the finitely many cohomology stratifications using constructible-stratification-
intersection. On a refined stratum every cohomology module has a finite constant model
R_S tensor_A N. The DVR A=O_E has a two-term finite free resolution of N: its finite
presentation kernel is finite torsion-free, hence free (dvr-fg-torsionfree-free). The
completed coefficient sheaf is flat over constant A (completed-constant-sheaf-reduction).
Exact pullback and tensor compatibility (alpha-iso, site-pullback-abelian-exact, ringed-
topoi-derived-tensor-pullback) preserve these models. Bounded-above-flat-kflat-site and
derived-change-of-rings compute their reductions by the same two-term finite matrices.
The quotient scalar ring is finite by coefficient cofinality and coefficient-extension
finiteness; its matrix kernels and cokernels are finite modules.
7. The finite truncation triangles build M from its cohomology sheaves. Derived scalar
extension and restriction preserve these triangles. The long exact cohomology sequence
(derived-homology-long-exact) and locally-constant-derived-serre close their finite-type
locally constant cohomology under kernels, cokernels and extensions. The common global
finite stratification therefore proves constructibility of all finite-level cohomology,
including finite geometric stalks, exactly as proetale-constructible-sheaf requires.
8. Take N=R_n in step 5. Tensor with the unit returns the reduction itself, so its
cohomology lies in the same Tor interval. Together with steps 3, 5 and 7 these are
precisely the normalized-constructible-tower conditions. Zero M and empty T are included.
-/
theorem sp_reduction_tower_normalized (D : SpCoefficientTowersAbelian l E T) :
    Nonempty (SpReductionTower l E T D) := by
  sorry

end AlgebraicGeometry.ProEtale
