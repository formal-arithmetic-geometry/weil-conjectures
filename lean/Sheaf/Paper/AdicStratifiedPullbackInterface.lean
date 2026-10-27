/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.AdicNormalizedFibreExactness
public import Sheaf.Paper.PerAdicCommonStageTruncations
public import Sheaf.Paper.CondensedERealization
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
public import Sheaf.Paper.IntrinsicQbarCategory
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # The standard-heart interface of actual completed pullback

Source: Bhatt--Scholze, Remark 6.8.15 and Proposition 6.8.14
(blueprint: lem-per-adic-stratified-pullback-texact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.AdicFibreComparison
open ContinuousRational

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [hl : Fact (IsUnit (l : k))]

/-- Reuse the existing separated finite-type base without introducing another bundle.
Source: BS 6.8.14 (blueprint: lem-per-adic-stratified-pullback-texact). -/
abbrev FiniteTypeBase := WeilConjectures.CondensedERealization.Base

/-- The geometric consequences of the stated finite-type hypotheses.
Source: BS 6.8.14 (blueprint: lem-per-adic-stratified-pullback-texact).
Proof: finite type over Spec k gives noetherianity. The finite-type fibre-dimension theorem
on its unique fibre bounds dimension. -/
theorem finiteTypeBaseGeometry (X : FiniteTypeBase k) :
    IsNoetherian X.scheme ∧ (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n) := by
  sorry

include hl in
/-- Invertibility of the coefficient prime follows from the stated base-field hypothesis.
Source: BS 6.8.14 (blueprint: lem-per-adic-stratified-pullback-texact).
Proof: the structure morphism sends the unit l in k to a unit in every local ring. -/
theorem finiteTypeBasePrime (X : FiniteTypeBase k) :
    ∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x) := by
  sorry

/-- Noetherianity is a consequence, not additional base data.
Source: BS 6.8.14 (blueprint: lem-per-adic-stratified-pullback-texact). -/
instance finiteTypeBaseNoetherian (X : FiniteTypeBase k) : IsNoetherian X.scheme :=
  (finiteTypeBaseGeometry X).1

/-- The dimension hypothesis is a consequence of finite type over the base field.
Source: BS 6.8.14 (blueprint: lem-per-adic-stratified-pullback-texact). -/
instance finiteTypeBaseDimension (X : FiniteTypeBase k) :
    Fact (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n) :=
  ⟨(finiteTypeBaseGeometry X).2⟩

/-- The coefficient prime stays invertible in each local ring.
Source: BS 6.8.14 (blueprint: lem-per-adic-stratified-pullback-texact). -/
instance finiteTypeBasePrimeUnit (X : FiniteTypeBase k) :
    Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x)) :=
  ⟨finiteTypeBasePrime l X⟩

/-- The existing finite-type base, viewed in the continuous realization interface.
Source: BS 6.8.14 (blueprint: lem-per-adic-stratified-pullback-texact). -/
def base (X : FiniteTypeBase k) : ContinuousRational.Base.{u} l where
  scheme := X.scheme
  dimension := (finiteTypeBaseDimension X).out
  prime_unit := (finiteTypeBasePrimeUnit l X).out

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (R : ContinuousRational.Family.{u} l)

/-- Actual completed pullback preserves heart membership.
Source: BS 6.8.15 (blueprint: lem-per-adic-stratified-pullback-texact).
Proof: on a lisse stratification the local finite-free complexes are K-flat and pull back
in degree zero. Stratum detection kills all other cohomology. -/
theorem pullHeart {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme)
    (F : NormalizedFibre.Heart l E (base l X)) :
    (localizedT l E (base l Y)).heart
      (((R.along E (X := base l Y) (Y := base l X) g).raw l E).obj F.obj) := by
  sorry

/-- Literal restriction of actual completed pullback to the full standard heart.
Source: BS 6.8.15 (blueprint: lem-per-adic-stratified-pullback-texact). -/
def heartPull {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme) :
    NormalizedFibre.Heart l E (base l X) ⥤ NormalizedFibre.Heart l E (base l Y) :=
  ObjectProperty.lift (localizedT l E (base l Y)).heart
    ((localizedT l E (base l X)).heart.ι ⋙
      (R.along E (X := base l Y) (Y := base l X) g).raw l E)
    (pullHeart l E R g)

/-- Common-stage completed pullback preserves heart membership.
Source: BS 6.8.14--6.8.15 (blueprint: lem-per-adic-stratified-pullback-texact).
Proof: descend each object to a finite stage, apply pullHeart, and use the recorded common
standard classes, which are precisely the finite-stage classes. -/
theorem commonPullHeart (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme)
    (F : (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory) :
    (pbcQbarStandardT l Ω Y.scheme).heart ((pbcQbarCompletedPull l Ω g).obj F.obj) := by
  sorry

/-- Literal restriction of the recorded pair-category pullback.
Source: BS 6.8.15 (blueprint: lem-per-adic-stratified-pullback-texact). -/
def commonHeartPull (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme) :
    (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory ⥤
      (pbcQbarStandardT l Ω Y.scheme).heart.FullSubcategory :=
  ObjectProperty.lift (pbcQbarStandardT l Ω Y.scheme).heart
    ((pbcQbarStandardT l Ω X.scheme).heart.ι ⋙ pbcQbarCompletedPull l Ω g)
    (commonPullHeart l Ω g)

/-- Finite free continuous coefficients, placed in degree zero.
Source: BS 6.8.3 (blueprint: lem-per-adic-stratified-pullback-texact). -/
def free (T : Scheme.{u}) (n : ℕ) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.free (R := (adicLisseForget T).obj (rationalCoefficientSheaf l T E))
      (ULift.{u + 1} (Fin n)))

/-- All local models of actual completed pullback; neither flatness of the coefficient map
nor nonemptiness of the pulled stratum is imposed.
Source: BS 6.8.15 (blueprint: lem-per-adic-stratified-pullback-texact). -/
def LocalModels {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme) : Prop :=
  ∀ (F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
    (s : FiniteLocallyClosedStratification X.scheme)
    (_hs : ∀ i : Fin s.n,
      ((proEtaleModuleInverseImage (s.immersion i)
        (rationalCoefficientSheaf l X.scheme E)).obj F).IsFiniteLocallyFree)
    (i : Fin s.n),
    ∃ h : (adicTowerInverseImage (pullback.fst g (s.immersion i))).obj
        (rationalCoefficientSheaf l Y.scheme E) ⟶
      rationalCoefficientSheaf l (pullback g (s.immersion i)) E,
      rationalCoefficientRestrictionNormalized l E (pullback.fst g (s.immersion i)) h ∧
      ∀ (K : PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E))
        (_e : (R.realization E (base l X)).J.obj K ≅
          (DerivedCategory.singleFunctor _ 0).obj F),
        ((derivedPull (pullback.fst g (s.immersion i)) h).obj
          ((R.realization E (base l Y)).J.obj
            (((R.along E (X := base l Y) (Y := base l X) g).raw l E).obj K))).IsLE 0 ∧
        ((derivedPull (pullback.fst g (s.immersion i)) h).obj
          ((R.realization E (base l Y)).J.obj
            (((R.along E (X := base l Y) (Y := base l X) g).raw l E).obj K))).IsGE 0

/-- The pulled-back trivializing charts carry exactly the same finite free rank.
Source: BS 6.8.15 (blueprint: lem-per-adic-stratified-pullback-texact). -/
def FreeModels {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme) : Prop :=
  ∀ (F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
    (s : FiniteLocallyClosedStratification X.scheme) (i : Fin s.n)
    (U : (s.domain i).ProEt) (r : ℕ)
    (_φ : (modulePull (U.hom ≫ s.immersion i)
      (NormalizedFibre.coefficient l E (U.hom ≫ s.immersion i))).obj F ≅
        SheafOfModules.free (R := (adicLisseForget U.left).obj
          (rationalCoefficientSheaf l U.left E)) (ULift.{u + 1} (Fin r)))
    (K : PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E))
    (_e : (R.realization E (base l X)).J.obj K ≅
      (DerivedCategory.singleFunctor _ 0).obj F),
    Nonempty (((derivedPull (pullback.fst g (U.hom ≫ s.immersion i))
      (NormalizedFibre.coefficient l E (pullback.fst g (U.hom ≫ s.immersion i)))).obj
        ((R.realization E (base l Y)).J.obj
          (((R.along E (X := base l Y) (Y := base l X) g).raw l E).obj K))) ≅
      free l E (pullback g (U.hom ≫ s.immersion i)) r)

/-- The finite shift comparison is uniquely pinned by the universal derived counit and J.
Source: BS 6.8.15 (blueprint: lem-per-adic-stratified-pullback-texact). -/
structure ShiftData {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme) where
  finite_shift : ((R.along E (X := base l Y) (Y := base l X) g).raw l E).CommShift ℤ
  ambient_shift : (derivedPull g
    (R.along E (X := base l Y) (Y := base l X) g).coefficient).CommShift ℤ
  ambient_shift_counit :
    letI := ambient_shift
    letI : (modulePull g
      (R.along E (X := base l Y) (Y := base l X) g).coefficient).Additive :=
        (R.along E (X := base l Y) (Y := base l X) g).ordinaryAdditive
    NatTrans.CommShift (R.along E (X := base l Y) (Y := base l X) g).counit ℤ
  finite_shift_normalized :
    letI := finite_shift
    letI := ambient_shift
    letI : (rawPull l E (X := base l Y) (Y := base l X) g
      (R.along E (X := base l Y) (Y := base l X) g).integral_mem).CommShift ℤ :=
        finite_shift
    letI : (R.realization E (base l Y)).J.CommShift ℤ :=
      (R.realization E (base l Y)).shift
    letI : (R.realization E (base l X)).J.CommShift ℤ :=
      (R.realization E (base l X)).shift
    NatTrans.CommShift
      (R.along E (X := base l Y) (Y := base l X) g).comparison.hom ℤ

/-- The finite shift component with the localized shift instances fixed at its owner.
Source: BS 6.8.15 (blueprint: lem-per-adic-stratified-pullback-texact). -/
def ShiftData.component {X Y : FiniteTypeBase k} {g : Y.scheme ⟶ X.scheme}
    (d : ShiftData l E R g) (n : ℤ)
    (K : PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)) :=
  letI := d.finite_shift
  (((R.along E (X := base l Y) (Y := base l X) g).raw l E).commShiftIso n).hom.app K

/-- The balanced ordinary pullback of a free module, normalized on each standard generator.
Source: BS 6.8.15 (blueprint: lem-per-adic-stratified-pullback-texact). -/
def FreeBalance : Prop :=
  ∀ (U V : Scheme.{u}) (f : V ⟶ U) (r : ℕ),
    ∃ e : (modulePull f (NormalizedFibre.coefficient l E f)).obj
        (SheafOfModules.free (R := (adicLisseForget U).obj
          (rationalCoefficientSheaf l U E)) (ULift.{u + 1} (Fin r))) ≅
      SheafOfModules.free (R := (adicLisseForget V).obj
        (rationalCoefficientSheaf l V E)) (ULift.{u + 1} (Fin r)),
      ∀ (W : U.ProEt) (j : ULift.{u + 1} (Fin r)),
        (e.hom.val.app (op ((proEtaleBaseChange f).obj W)))
          (moduleUnit f (NormalizedFibre.coefficient l E f) _ W
            ((SheafOfModules.ιFree (R := (adicLisseForget U).obj
              (rationalCoefficientSheaf l U E)) j).val.app (op W)
                (1 : (rationalCoefficientSheaf l U E).obj.obj (op W)))) =
          (SheafOfModules.ιFree (R := (adicLisseForget V).obj
            (rationalCoefficientSheaf l V E)) j).val.app
              (op ((proEtaleBaseChange f).obj W))
                (1 : (rationalCoefficientSheaf l V E).obj.obj
                  (op ((proEtaleBaseChange f).obj W)))

/-- The complete finite and common-stage t-exactness assertions on the published functors.
Source: BS 6.8.14--6.8.15 (blueprint: lem-per-adic-stratified-pullback-texact). -/
structure PullbackAssertions (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (X Y : FiniteTypeBase k) (g : Y.scheme ⟶ X.scheme) where
  finite_tExact : ((R.along E (X := base l Y) (Y := base l X) g).raw l E).IsTExact
    (localizedT l E (base l X)) (localizedT l E (base l Y))
  finite_shift : ((R.along E (X := base l Y) (Y := base l X) g).raw l E).CommShift ℤ
  ambient_shift : (derivedPull g
    (R.along E (X := base l Y) (Y := base l X) g).coefficient).CommShift ℤ
  ambient_shift_counit :
    letI := ambient_shift
    letI : (modulePull g
      (R.along E (X := base l Y) (Y := base l X) g).coefficient).Additive :=
        (R.along E (X := base l Y) (Y := base l X) g).ordinaryAdditive
    NatTrans.CommShift (R.along E (X := base l Y) (Y := base l X) g).counit ℤ
  finite_shift_normalized :
    letI := finite_shift
    letI := ambient_shift
    letI : (rawPull l E (X := base l Y) (Y := base l X) g
      (R.along E (X := base l Y) (Y := base l X) g).integral_mem).CommShift ℤ :=
        finite_shift
    letI : (R.realization E (base l Y)).J.CommShift ℤ :=
      (R.realization E (base l Y)).shift
    letI : (R.realization E (base l X)).J.CommShift ℤ :=
      (R.realization E (base l X)).shift
    NatTrans.CommShift
      (R.along E (X := base l Y) (Y := base l X) g).comparison.hom ℤ
  finite_triangulated : (fun [_s : ((R.along E (X := base l Y) (Y := base l X) g).raw
    l E).CommShift ℤ] ↦
      ((R.along E (X := base l Y) (Y := base l X) g).raw l E).IsTriangulated)
        (_s := finite_shift)
  finite_upper : ∀ n : ℤ,
    (localizedT l E (base l X)).truncLE n ⋙
        (R.along E (X := base l Y) (Y := base l X) g).raw l E ≅
      (R.along E (X := base l Y) (Y := base l X) g).raw l E ⋙
        (localizedT l E (base l Y)).truncLE n
  finite_upper_counit : ∀ (n : ℤ) K,
    (finite_upper n).hom.app K ≫ ((localizedT l E (base l Y)).truncLEι n).app
        (((R.along E (X := base l Y) (Y := base l X) g).raw l E).obj K) =
      ((R.along E (X := base l Y) (Y := base l X) g).raw l E).map
        (((localizedT l E (base l X)).truncLEι n).app K)
  finite_lower : ∀ n : ℤ,
    (localizedT l E (base l X)).truncGE n ⋙
        (R.along E (X := base l Y) (Y := base l X) g).raw l E ≅
      (R.along E (X := base l Y) (Y := base l X) g).raw l E ⋙
        (localizedT l E (base l Y)).truncGE n
  finite_lower_unit : ∀ (n : ℤ) K,
    ((R.along E (X := base l Y) (Y := base l X) g).raw l E).map
        (((localizedT l E (base l X)).truncGEπ n).app K) ≫
          (finite_lower n).hom.app K =
      ((localizedT l E (base l Y)).truncGEπ n).app
        (((R.along E (X := base l Y) (Y := base l X) g).raw l E).obj K)
  finite_cohomology : ∀ n : ℤ,
    Nonempty (localizedCohomology l E (base l X) n ⋙
      (R.along E (X := base l Y) (Y := base l X) g).raw l E ≅
        (R.along E (X := base l Y) (Y := base l X) g).raw l E ⋙
          localizedCohomology l E (base l Y) n)
  finite_inclusion : heartPull l E R g ⋙ (localizedT l E (base l Y)).heart.ι ≅
    (localizedT l E (base l X)).heart.ι ⋙
      (R.along E (X := base l Y) (Y := base l X) g).raw l E
  [finite_zero : (heartPull l E R g).PreservesZeroMorphisms]
  finite_exact : ∀ S : ShortComplex (NormalizedFibre.Heart l E (base l X)),
    S.ShortExact → (S.map (heartPull l E R g)).ShortExact
  local_models : LocalModels l E R g
  free_models : FreeModels l E R g
  free_balance : FreeBalance l E
  common_tExact : (pbcQbarCompletedPull l Ω g).IsTExact
    (pbcQbarStandardT l Ω X.scheme) (pbcQbarStandardT l Ω Y.scheme)
  common_shift : (pbcQbarCompletedPull l Ω g).CommShift ℤ
  stage_shifts : ∀ A : Padic.FiniteCoefficientFields l Ω,
    ShiftData l (pbcFiniteField.{u} l Ω A) R g
  common_shift_finite :
    letI := common_shift
    ∀ (A : Padic.FiniteCoefficientFields l Ω) (n : ℤ)
    (K : pbcStageCategory l Ω X.scheme A),
    ∃ f : ((shiftFunctor (pbcStageCategory l Ω X.scheme A) n) ⋙
        (pbcQbarPullFamily l Ω g).Φ A).obj K ⟶
      ((pbcQbarPullFamily l Ω g).Φ A ⋙
        shiftFunctor (pbcStageCategory l Ω Y.scheme A) n).obj K,
      HEq f ((stage_shifts A).component l (pbcFiniteField.{u} l Ω A) R n K) ∧
      HEq (((pbcQbarCompletedPull l Ω g).commShiftIso n).hom.app
        (((pbcScalarSystem l Ω X.scheme (base l X).dimension
          (base l X).prime_unit).ι A).obj K))
        (((pbcScalarSystem l Ω Y.scheme (base l Y).dimension
          (base l Y).prime_unit).ι A).map f)
  common_triangulated : (fun [_s : (pbcQbarCompletedPull l Ω g).CommShift ℤ] ↦
    (pbcQbarCompletedPull l Ω g).IsTriangulated) (_s := common_shift)
  common_upper : ∀ n : ℤ,
    (pbcQbarStandardT l Ω X.scheme).truncLE n ⋙ pbcQbarCompletedPull l Ω g ≅
      pbcQbarCompletedPull l Ω g ⋙ (pbcQbarStandardT l Ω Y.scheme).truncLE n
  common_upper_counit : ∀ (n : ℤ) K,
    (common_upper n).hom.app K ≫ ((pbcQbarStandardT l Ω Y.scheme).truncLEι n).app
        ((pbcQbarCompletedPull l Ω g).obj K) =
      (pbcQbarCompletedPull l Ω g).map
        (((pbcQbarStandardT l Ω X.scheme).truncLEι n).app K)
  common_lower : ∀ n : ℤ,
    (pbcQbarStandardT l Ω X.scheme).truncGE n ⋙ pbcQbarCompletedPull l Ω g ≅
      pbcQbarCompletedPull l Ω g ⋙ (pbcQbarStandardT l Ω Y.scheme).truncGE n
  common_lower_unit : ∀ (n : ℤ) K,
    (pbcQbarCompletedPull l Ω g).map
        (((pbcQbarStandardT l Ω X.scheme).truncGEπ n).app K) ≫
          (common_lower n).hom.app K =
      ((pbcQbarStandardT l Ω Y.scheme).truncGEπ n).app
        ((pbcQbarCompletedPull l Ω g).obj K)
  common_cohomology : ∀ n : ℤ,
    Nonempty (((pbcQbarStandardT l Ω X.scheme).truncLE n ⋙
      (pbcQbarStandardT l Ω X.scheme).truncGE n ⋙
        shiftFunctor (pbcQbarCategory l Ω X.scheme) n) ⋙
      pbcQbarCompletedPull l Ω g ≅ pbcQbarCompletedPull l Ω g ⋙
        ((pbcQbarStandardT l Ω Y.scheme).truncLE n ⋙
          (pbcQbarStandardT l Ω Y.scheme).truncGE n ⋙
            shiftFunctor (pbcQbarCategory l Ω Y.scheme) n))
  common_inclusion : commonHeartPull l Ω g ⋙ (pbcQbarStandardT l Ω Y.scheme).heart.ι ≅
    (pbcQbarStandardT l Ω X.scheme).heart.ι ⋙ pbcQbarCompletedPull l Ω g
  [common_zero : (commonHeartPull l Ω g).PreservesZeroMorphisms]
  common_exact : ∀ S : ShortComplex (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory,
    S.ShortExact → (S.map (commonHeartPull l Ω g)).ShortExact

/-- Source: BS 6.8.14--6.8.15 (blueprint: lem-per-adic-stratified-pullback-texact).
Proof: pull back a lisse stratification and its trivializing pro-etale covers. Finite free
modules are K-flat, and balanced tensor sends a free module of rank r to one of rank r,
including r=0 and empty strata. Stratum detection kills all other cohomology. Apply bounded
truncation devissage to obtain preservation of every standard bound. The raw pullback is the
localization of actual completed integral pullback, whose reductions retain their etale
origins. Its normalized scalar comparisons and shift comparisons descend to the pair category.
Common-stage truncations reduce every bound and cohomology comparison to a finite stage.
A t-exact triangulated functor restricts to an exact functor on the heart, giving both exactness
assertions and the canonical inclusion isomorphisms. -/
theorem pullbackAssertions (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (X Y : FiniteTypeBase k) (g : Y.scheme ⟶ X.scheme) :
    Nonempty (PullbackAssertions l E R Ω X Y g) := by
  sorry

end AlgebraicGeometry.Scheme.AdicFibreComparison
