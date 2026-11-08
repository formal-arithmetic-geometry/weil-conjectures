/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.Principal.PrincipalPowerQuotients
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Adjunction.Additive

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Flat-term successive quotient tensor sequences

Source: blueprint main-20261015, integral criterion reductions, second paragraph;
Stacks Project, Modules on Sites, Tags 03DA, 03EK, 03ER.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v r wB wR wS wPrev wN wOne
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules

section SheafificationAPI

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}] {R : Sheaf J RingCat.{r}}

end SheafificationAPI

section

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}]

section Models
variable {B S : Sheaf J CommRingCat.{r}} {φ : B ⟶ S}
  [HasDerivedCategory.{wB} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J B))]
  [HasDerivedCategory.{wS} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J S))]

end Models

section FlatTensorData

variable {B SPrev SN SOne : Sheaf J CommRingCat.{r}}
  [HasDerivedCategory.{wB} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J B))]
  [HasDerivedCategory.{wPrev} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SPrev))]
  [HasDerivedCategory.{wN} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SN))]
  [HasDerivedCategory.{wOne} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SOne))]

end FlatTensorData

end

namespace SuccessiveQuotientCoefficients

variable {R : Type*} [CommRing R] (t : R) (n : ℕ) (hn : 1 ≤ n)
private abbrev I (k : ℕ) : Ideal R := Ideal.span {t ^ k}
include hn
private theorem mul_mem (x : R) (hx : x ∈ I t (n - 1)) : t * x ∈ I t n := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.1 hx
  apply Ideal.mem_span_singleton.2
  refine ⟨y, ?_⟩
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn]
private def a : R ⧸ I t (n - 1) →ₗ[R] R ⧸ I t n :=
  (I t (n - 1)).mapQ (I t n) (LinearMap.mulLeft R t) (mul_mem t n hn)
private theorem ideal_le : I t n ≤ I t 1 := by
  apply Ideal.span_le.2
  intro x hx
  obtain rfl := Set.mem_singleton_iff.1 hx
  exact Ideal.mem_span_singleton.2 (pow_dvd_pow t hn)
private def b : R ⧸ I t n →ₗ[R] R ⧸ I t 1 :=
  (I t n).mapQ (I t 1) LinearMap.id (ideal_le t n hn)
private theorem zero_comp : (b t n hn).comp (a t n hn) = 0 := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro x
  change Ideal.Quotient.mk (I t 1) (t * x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton.2 (by simp)
end SuccessiveQuotientCoefficients

section LeftTensorAuxiliary

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  {B : Sheaf J CommRingCat.{r}}

private def leftTensorPresheaf
    (N : PresheafOfModules.{r} (B.obj ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{r} (B.obj ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{r} (B.obj ⋙ forget₂ CommRingCat RingCat) where
  obj M := siteTensorPresheaf N M
  map f := siteTensorSecondMap N f
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl

end LeftTensorAuxiliary

section RestrictedTensorAuxiliary

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]

private def restrictedTensorPresheafIso {R S : Sheaf J CommRingCat.{r}}
    (φ : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    siteTensorPresheaf
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val M.val ≅
      (PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
          (changeOfRingsPresheaf φ M) := by
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · let e :
        (siteTensorPresheaf
          ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
            (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val M.val).obj V ≃ₗ[
              R.obj.obj V]
          ((PresheafOfModules.restrictScalars
            ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
              (changeOfRingsPresheaf φ M)).obj V :=
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := by
          intro b z
          induction z using TensorProduct.inductionOn with
          | tmul s x => rfl
          | add z z' hz hz' => simpa only [smul_add] using congrArg₂ (· + ·) hz hz' }
    exact e.toModuleIso
  · intro V W f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul s m =>
      let : Module (R.obj.obj W)
          ((ModuleCat.restrictScalars
            (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.map f).hom).obj
              (M.val.obj W)) := inferInstanceAs (Module (R.obj.obj W) (M.val.obj W))
      change S.obj.map f s ⊗ₜ[R.obj.obj W, (φ.hom.app W).hom] M.val.map f m =
        changeOfRingsMap φ M f (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)
      exact (Classical.choose_spec (exists_changeOfRingsMap φ M f) s m).symm

end RestrictedTensorAuxiliary

section OrdinaryExtensionAuxiliary

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}

private def ordinaryExtensionPresheaf (a : R ⟶ S) :
    ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R) ⥤
      PresheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S).obj where
  obj := changeOfRingsPresheaf a
  map f :=
    { app U := (ModuleCat.extendScalars (a.hom.app U).hom).map (f.val.app U)
      naturality := changeOfRingsHom_naturality a _ f }
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    simp
    rfl
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    simp

private def ordinaryExtension (a : R ⟶ S) :
    ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R) ⥤
      ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S) :=
  ordinaryExtensionPresheaf a ⋙ PresheafOfModules.sheafification.{r}
    (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)

variable [HasSheafify J AddCommGrpCat.{r}]

end OrdinaryExtensionAuxiliary

section TensorExtensionNaturalityAuxiliary

variable {C : Type u} [Category.{v} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]

private def tensorExtensionUnit {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    forget ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⋙
        leftTensorPresheaf
          ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
            (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val ⟶
      (ordinaryExtension a ⋙
        restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)) ⋙
          forget ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) where
  app M := (restrictedTensorPresheafIso a M).hom ≫
    (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map a).hom).map
      ((PresheafOfModules.sheafificationAdjunction.{r}
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).unit.app
          (changeOfRingsPresheaf a M))
  naturality {M N} f := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro s x
    change S.obj.obj U at s
    exact (congrArg (fun k ↦ (k.app U)
      (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x))
        ((PresheafOfModules.sheafificationAdjunction.{r}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).unit.naturality
            ((ordinaryExtensionPresheaf a).map f)))

private instance tensorExtensionUnit_injective {R S : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    PresheafOfModules.IsLocallyInjective J ((tensorExtensionUnit a).app M) := by
  change Presheaf.IsLocallyInjective J
    ((PresheafOfModules.toPresheaf _).map (restrictedTensorPresheafIso a M).hom ≫
      toSheafify J (changeOfRingsPresheaf a M).presheaf)
  have : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map (restrictedTensorPresheafIso a M).hom) :=
    inferInstance
  have : Presheaf.IsLocallyInjective J
      (toSheafify J (changeOfRingsPresheaf a M).presheaf) := inferInstance
  infer_instance

private instance tensorExtensionUnit_surjective {R S : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    PresheafOfModules.IsLocallySurjective J ((tensorExtensionUnit a).app M) := by
  change Presheaf.IsLocallySurjective J
    ((PresheafOfModules.toPresheaf _).map (restrictedTensorPresheafIso a M).hom ≫
      toSheafify J (changeOfRingsPresheaf a M).presheaf)
  have : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map (restrictedTensorPresheafIso a M).hom) :=
    inferInstance
  have : Presheaf.IsLocallySurjective J
      (toSheafify J (changeOfRingsPresheaf a M).presheaf) := inferInstance
  infer_instance

variable [EssentiallySmall.{r} C]

variable [HasSheafify J AddCommGrpCat.{r}]

end TensorExtensionNaturalityAuxiliary

section ExactRestrictionAuxiliary

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

-- This is the general-ring version of systemScalarRestriction_exact. Both composites
-- with toSheaf retain the same underlying abelian sheaf and every morphism.
end ExactRestrictionAuxiliary

section EndpointModelAuxiliary

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]

end EndpointModelAuxiliary

section CochainAuxiliary

variable {A : Type*} [Category A] [Abelian A]
  {D : Type*} [Category D] [Abelian D]
  (E₁ E₂ E₃ : A ⥤ D) [E₁.Additive] [E₂.Additive] [E₃.Additive]
  (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (wab : a ≫ b = 0)
  (P : CochainComplex A ℤ)

end CochainAuxiliary

section FlatTensorAssembly

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {B SPrev SN SOne : Sheaf J CommRingCat.{r}}
  [HasDerivedCategory.{wB} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J B))]
  [HasDerivedCategory.{wPrev} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SPrev))]
  [HasDerivedCategory.{wN} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SN))]
  [HasDerivedCategory.{wOne} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SOne))]

end FlatTensorAssembly

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}]
  (B : Sheaf J CommRingCat.{r})
  (t : (B.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections)

private instance quotientLocallyBijectiveCommRing :
    J.WEqualsLocallyBijective CommRingCat.{r} := by
  let : PreservesFilteredColimitsOfSize.{r, r}
      (CategoryTheory.forget CommRingCat.{r}) := preservesFilteredColimitsOfSize_shrink _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J

end SheafOfModules
