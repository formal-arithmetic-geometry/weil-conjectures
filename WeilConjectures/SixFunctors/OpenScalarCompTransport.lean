/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenScalarTensorData
public import WeilConjectures.SecSmoothPurity.ScalarExtensionFunctor
import WeilConjectures.SixFunctors.OpenScalarConjugateComparison
import WeilConjectures.SecSmoothPurity.ScalarAssociatorConjugate
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-! Transport of the scalar compositor through a chosen presentation.

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 07A6 and 0D6D.
(blueprint: lem-sp-open-scalar-coefficient-compositor-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules WeilConjectures
attribute [local instance 100000] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local instance 200000] SheafOfModules.instAbelian
private noncomputable instance (priority := 200000) fixedStalk (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
    u + 1, u + 2, u + 1} _
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor

private theorem leftAdjointUniq_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L₁ L₂ : C ⥤ D} {R : D ⥤ C} {F₁ F₂ : D ⥤ E} {G : E ⥤ D}
    (a₁ : L₁ ⊣ R) (a₂ : L₂ ⊣ R) (b₁ : F₁ ⊣ G) (b₂ : F₂ ⊣ G) :
    ((a₁.comp b₁).leftAdjointUniq (a₂.comp b₂)).hom =
      Functor.whiskerRight (a₁.leftAdjointUniq a₂).hom F₁ ≫
        Functor.whiskerLeft L₂ (b₁.leftAdjointUniq b₂).hom := by
  apply (conjugateEquiv (a₂.comp b₂) (a₁.comp b₁)).injective
  rw [← conjugateEquiv_comp (a₂.comp b₂) (a₂.comp b₁) (a₁.comp b₁)]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight]
  simp [Adjunction.leftAdjointUniq]

private theorem leftAdjointUniq_ofNatIsoRightLeft
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : G ≅ G') :
    ((a.ofNatIsoRight e).leftAdjointUniq b).hom =
      (conjugateEquiv b a).symm e.inv := by
  ext M
  simp [Adjunction.leftAdjointUniq, conjugateIsoEquiv, conjugateEquiv,
    Functor.comp_obj, Functor.id_obj,
    Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoRight_counit]

private theorem leftAdjointUniq_ofNatIsoRight
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : G' ≅ G) :
    (a.leftAdjointUniq (b.ofNatIsoRight e)).hom =
      (conjugateEquiv b a).symm e.hom := by
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateIsoEquiv, conjugateEquiv,
    Functor.comp_obj, Functor.id_obj,
    Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoRight_counit]

private theorem leftAdjointUniq_ofNatIsoRight_inv
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : G ≅ G') :
    (b.leftAdjointUniq (a.ofNatIsoRight e)).inv =
      (conjugateEquiv b a).symm e.inv := by
  apply NatTrans.ext
  funext X
  rw [Adjunction.leftAdjointUniq_inv_app]
  exact congr_app (leftAdjointUniq_ofNatIsoRightLeft a b e) X

/-- The canonical compositor after transporting the published scalar extensions through
`scalarIso`. -/
def transportedScalarComp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (m : Models.{u}) (φ : A →+* B) (ψ : B →+* C) (T : Scheme.{u}) :
    scalar m φ T ⋙ scalar m ψ T ≅ scalar m (ψ.comp φ) T :=
  Functor.isoWhiskerLeft (scalar m φ T) (scalarIso m ψ T) ≪≫
    Functor.isoWhiskerRight (scalarIso m φ T) (scalarExtensionFunctor ψ T) ≪≫
    scalarExtensionFunctor_composition φ ψ T ≪≫
    (scalarIso m (ψ.comp φ) T).symm

/-- Transporting the canonical scalar compositor through the selected presentations gives
`transportedScalarComp`.
Source: Stacks 07A6 and 0D6D (adjoint uniqueness of extension of scalars).
Proof: both sides are isomorphisms between left adjoints of derived scalar restriction.
`scalarComp` is the `leftAdjointUniq` comparison of the composite presentation adjunction with
the presentation adjunction of `ψ ∘ φ` transported by restriction composition, followed by the
constant-sheaf equality. Each `scalarIso` is `leftAdjointUniq` with the published adjunction,
and `scalarAssociatorConjugate` identifies the conjugate of the canonical compositor with
restriction composition. So the right conjugates of both sides are the same restriction
composition comparison, and `conjugateEquiv` is injective. Equivalently, the adjuncts under
the common restriction adjunction are equal by the defining unit equations of
`leftAdjointUniq`.
This is the presentation-normalization step and is independent of the geometric morphism.
(blueprint: lem-sp-open-scalar-coefficient-compositor-transport).
-/
theorem scalarComp_transport
    (m : Models.{u}) {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (T : Scheme.{u}) :
    scalarComp m φ ψ T = transportedScalarComp m φ ψ T := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    fixedStalk T
  let pφ : scalarExtensionFunctor φ T ⊣ scalarRestriction φ T := by
    change scalarExtension φ T ⊣ scalarRestriction φ T
    exact proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := T) φ)
  let pψ : scalarExtensionFunctor ψ T ⊣ scalarRestriction ψ T := by
    change scalarExtension ψ T ⊣ scalarRestriction ψ T
    exact proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := T) ψ)
  let pc : scalarExtensionFunctor (ψ.comp φ) T ⊣ scalarRestriction (ψ.comp φ) T := by
    change scalarExtension (ψ.comp φ) T ⊣ scalarRestriction (ψ.comp φ) T
    exact proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := T) (ψ.comp φ))
  let sψ : scalar m ψ T ≅ scalarExtensionFunctor ψ T := by
    change scalar m ψ T ≅ scalarExtension ψ T
    exact scalarIso m ψ T
  let sφ : scalar m φ T ≅ scalarExtensionFunctor φ T := by
    change scalar m φ T ≅ scalarExtension φ T
    exact scalarIso m φ T
  let scomp : scalar m (ψ.comp φ) T ≅ scalarExtensionFunctor (ψ.comp φ) T := by
    change scalar m (ψ.comp φ) T ≅ scalarExtension (ψ.comp φ) T
    exact scalarIso m (ψ.comp φ) T
  let sc : scalarExtensionFunctor φ T ⋙ scalarExtensionFunctor ψ T ≅
      scalarExtensionFunctor (ψ.comp φ) T := scalarExtensionFunctor_composition φ ψ T
  let tr : scalar m φ T ⋙ scalar m ψ T ≅ scalar m (ψ.comp φ) T :=
    Functor.isoWhiskerLeft (scalar m φ T) sψ ≪≫
      Functor.isoWhiskerRight sφ (scalarExtensionFunctor ψ T) ≪≫ sc ≪≫ scomp.symm
  change scalarComp m φ ψ T = tr
  apply Iso.ext_inv
  apply (conjugateEquiv
    ((scalarPair m φ T).adjunction.comp (scalarPair m ψ T).adjunction)
    (scalarPair m (ψ.comp φ) T).adjunction).injective
  simp only [scalarComp, tr, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv]
  rw [← conjugateEquiv_comp
    ((scalarPair m φ T).adjunction.comp (scalarPair m ψ T).adjunction)
    ((m T).scalar (proEtaleConstantRingMap φ ≫ proEtaleConstantRingMap ψ)).adjunction
    (scalarPair m (ψ.comp φ) T).adjunction]
  conv_rhs =>
    rw [← conjugateEquiv_comp
      ((scalarPair m φ T).adjunction.comp (scalarPair m ψ T).adjunction)
      ((scalarPair m φ T).adjunction.comp
        pψ)
      (scalarPair m (ψ.comp φ) T).adjunction]
  conv_rhs =>
    rw [← conjugateEquiv_comp
      ((scalarPair m φ T).adjunction.comp
        pψ)
      (pφ.comp pψ)
      (scalarPair m (ψ.comp φ) T).adjunction]
  conv_rhs =>
    rw [← conjugateEquiv_comp
      (pφ.comp pψ)
      pc
      (scalarPair m (ψ.comp φ) T).adjunction]
  simp only [scalarHomExtensionComp]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight]
  rw [leftAdjointUniq_ofNatIsoRight_inv]
  simp only [Equiv.apply_symm_apply]
  have hψ : conjugateEquiv (scalarPair m ψ T).adjunction pψ sψ.inv = 𝟙 _ := by
    change conjugateEquiv (scalarPair m ψ T).adjunction pψ
      ((scalarPair m ψ T).adjunction.leftAdjointUniq pψ).inv = 𝟙 _
    exact conjugateEquiv_leftAdjointUniq_inv _ _
  have hφ : conjugateEquiv (scalarPair m φ T).adjunction pφ sφ.inv = 𝟙 _ := by
    change conjugateEquiv (scalarPair m φ T).adjunction pφ
      ((scalarPair m φ T).adjunction.leftAdjointUniq pφ).inv = 𝟙 _
    exact conjugateEquiv_leftAdjointUniq_inv _ _
  have hc : conjugateEquiv pc (scalarPair m (ψ.comp φ) T).adjunction
      scomp.symm.inv = 𝟙 _ := by
    change conjugateEquiv pc (scalarPair m (ψ.comp φ) T).adjunction
      ((scalarPair m (ψ.comp φ) T).adjunction.leftAdjointUniq pc).hom = 𝟙 _
    exact conjugateEquiv_leftAdjointUniq_hom _ _
  have hsc : conjugateEquiv (pφ.comp pψ) pc sc.inv =
      (pbcDerivedRestrictComp _ _ _ (scalarExtensionFunctor_ringMap_comp φ ψ T)).hom := by
    change conjugateEquiv
        ((proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := T) φ)).comp
          (proEtaleRingDerivedExtensionAdjunction
            (proEtaleConstantRingMap (T := T) ψ)))
        (proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := T) (ψ.comp φ)))
        (scalarExtensionFunctor_composition φ ψ T).inv = _
    exact scalarAssociatorConjugate φ ψ T
  rw [hψ, hφ, hsc, hc]
  simpa only [Functor.whiskerRight_id', Functor.whiskerLeft_id', Category.comp_id,
    Category.id_comp, eqToIso.inv] using
    (scalarRestrictionConjugateComparison (T := T) m φ ψ)


end AlgebraicGeometry.ProEtale.OpenScalarTensor
