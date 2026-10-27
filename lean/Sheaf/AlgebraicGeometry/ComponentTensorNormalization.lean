/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W5
-/
module

public import Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel
public import Mathlib.CategoryTheory.Functor.Flat
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Sheaf.AlgebraicGeometry.ComponentFreeTensorDetection
import Mathlib.CategoryTheory.Generator.Sheaf
import Mathlib.CategoryTheory.Monoidal.Multifunctor
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

/-! # Unit normalization of the component inverse image

Source: Hemo--Richarz--Scholbach, Construction (4.1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Prod
private theorem leftAdjoint_hom_ext
    {C D : Type*} [Category* C] [Category* D]
    {P : ObjectProperty C} (hP : P.IsSeparating)
    (F : C ⥤ D) [F.IsLeftAdjoint] {X : C} {Y : D}
    (f g : F.obj X ⟶ Y)
    (h : ∀ (A : C), P A → ∀ a : A ⟶ X, F.map a ≫ f = F.map a ≫ g) : f = g := by
  let adj := Adjunction.ofIsLeftAdjoint F
  apply (adj.homEquiv X Y).injective
  apply hP
  intro A hA a
  simpa only [← adj.homEquiv_naturality_left] using
    congrArg (adj.homEquiv A Y) (h A hA a)

private theorem leftAdjoint_natTrans_ext
    {C D : Type*} [Category* C] [Category* D]
    {P : ObjectProperty C} (hP : P.IsSeparating)
    {F G : C ⥤ D} [F.IsLeftAdjoint] (α β : F ⟶ G)
    (h : ∀ A, P A → α.app A = β.app A) : α = β := by
  ext X
  apply leftAdjoint_hom_ext hP F
  intro A hA a
  rw [α.naturality, β.naturality, h A hA]

private theorem tensor_naturality
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (α : curriedTensorPre F ⟶ curriedTensorPost F)
    {X Y X' Y' : C} (a : X ⟶ X') (b : Y ⟶ Y') :
    (F.map a ⊗ₘ F.map b) ≫ (α.app X').app Y' =
      (α.app X).app Y ≫ F.map (a ⊗ₘ b) := by
  have h := (Functor.uncurry.map α).naturality (a ×ₘ b)
  change (F.map a ▷ F.obj Y ≫ F.obj X' ◁ F.map b) ≫ _ =
    _ ≫ (F.map (a ▷ Y) ≫ F.map (X' ◁ b)) at h
  dsimp only [Functor.uncurry] at h
  simpa only [← MonoidalCategory.tensorHom_def, ← F.map_comp] using h

private theorem unit_tensor_compatibility
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (l : F.LaxMonoidal) (m₀ : F.Monoidal) (γ : F ⟶ F) [IsIso l.ε]
    (hγ : l.ε ≫ γ.app (𝟙_ C) = m₀.toLaxMonoidal.ε)
    (X : C) :
    l.μ (𝟙_ C) X ≫ γ.app ((𝟙_ C) ⊗ X) =
      (γ.app (𝟙_ C) ⊗ₘ γ.app X) ≫ m₀.toLaxMonoidal.μ (𝟙_ C) X := by
  apply (cancel_epi (l.ε ▷ F.obj X)).1
  apply (cancel_mono (F.map (λ_ X).hom)).1
  simp only [Category.assoc]
  calc
    _ = (λ_ (F.obj X)).hom ≫ γ.app X := by
      rw [← γ.naturality]
      simpa only [Category.assoc] using
        congrArg (fun f ↦ f ≫ γ.app X) (l.left_unitality X).symm
    _ = (𝟙_ D) ◁ γ.app X ≫ (λ_ (F.obj X)).hom :=
      (leftUnitor_naturality (γ.app X)).symm
    _ = (𝟙_ D) ◁ γ.app X ≫ m₀.toLaxMonoidal.ε ▷ F.obj X ≫
        m₀.toLaxMonoidal.μ (𝟙_ C) X ≫ F.map (λ_ X).hom := by
      rw [← m₀.toLaxMonoidal.left_unitality X]
    _ = _ := by
      conv_lhs => rw [← hγ]
      simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
        Category.id_comp, Category.comp_id]

private theorem freeSheaf_separating
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u + 1}] :
    ObjectProperty.IsSeparating
      (.ofObj (fun E : C ↦ Sheaf.freeYoneda J E (𝟙_ Ab.{u + 1}))) := by
  have h : ObjectProperty.IsSeparating
      (.ofObj (fun _ : Unit ↦ (𝟙_ Ab.{u + 1}))) := by
    intro X Y f g hfg
    apply AddCommGrpCat.isSeparator_tensorUnit.def
    exact fun a ↦ hfg _ (ObjectProperty.ofObj_apply _ ()) a
  apply (Sheaf.isSeparating J h).of_le
  intro X hX
  obtain ⟨⟨E, i⟩⟩ := hX
  exact ObjectProperty.ofObj_apply _ E

private theorem tensor_bifunctor_ext
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory D]
    [BraidedCategory D] [MonoidalClosed D]
    {P : ObjectProperty C} (hP : P.IsSeparating)
    (F : C ⥤ D) [F.IsLeftAdjoint] {G : C ⥤ C ⥤ D}
    (α β : curriedTensorPre F ⟶ G)
    (h : ∀ X, P X → ∀ Y, P Y → (α.app X).app Y = (β.app X).app Y) : α = β := by
  have hx (X : C) (hX : P X) : α.app X = β.app X := by
    let : ((curriedTensorPre F).obj X).IsLeftAdjoint :=
      inferInstanceAs (F ⋙ tensorLeft (F.obj X)).IsLeftAdjoint
    exact leftAdjoint_natTrans_ext hP (α.app X) (β.app X) (h X hX)
  ext X Y
  let : ((curriedTensorPre F).flip.obj Y).IsLeftAdjoint :=
    inferInstanceAs (F ⋙ tensorRight (F.obj Y)).IsLeftAdjoint
  let αf : F ⋙ tensorRight (F.obj Y) ⟶ G.flip.obj Y :=
    ((flipFunctor C C D).map α).app Y
  let βf : F ⋙ tensorRight (F.obj Y) ⟶ G.flip.obj Y :=
    ((flipFunctor C C D).map β).app Y
  have hy := leftAdjoint_natTrans_ext hP αf βf
    (fun A hA ↦ NatTrans.congr_app (hx A hA) Y)
  exact NatTrans.congr_app hy X

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (T : Scheme.{u}) [IsAffine T]
  [(componentTests T).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)]

/-- The canonical tensor structure from the sheafified Kan-extension adjunction.
Source: HRS (4.1), the inverse image of the relative component site. -/
@[instance_reducible] def componentCanonicalMonoidal : (componentInverse T).Monoidal := by
  let : PreservesFiniteLimits (componentTests T) :=
    (Classical.choose_spec (component_relative_profinite_site T)).2.2.2.2.2.1
  let : RepresentablyFlat (componentTests T) := flat_of_preservesFiniteLimits _
  exact Functor.sheafPullbackConstruction.sheafPullbackMonoidal
    (componentTests T) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)

variable [(componentInverse T).Braided]

/-- The ratio of the canonical and supplied unit comparisons, as a scalar isomorphism.
Source: the unit normalization in the monoidal inverse-image comparison, HRS (4.1). -/
def componentUnitRatio :
    𝟙_ (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ≅
      𝟙_ (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) :=
  let e₀ : 𝟙_ _ ≅ (componentInverse T).obj (𝟙_ _) := by
    let := componentCanonicalMonoidal T
    exact Functor.Monoidal.εIso _
  e₀ ≪≫ (Functor.Monoidal.εIso (componentInverse T)).symm

/-- Scalar action of the unit ratio on every value of the inverse image.
Source: HRS (4.1), monoidal unit normalization. This is an explicit natural isomorphism. -/
def componentUnitCorrection : componentInverse T ≅ componentInverse T :=
  (componentInverse T).rightUnitor.symm ≪≫
    Functor.isoWhiskerLeft (componentInverse T)
      ((leftUnitorNatIso _).symm ≪≫ (curriedTensor _).mapIso (componentUnitRatio T) ≪≫
        leftUnitorNatIso _) ≪≫ (componentInverse T).rightUnitor

private theorem correction_unit :
    Functor.LaxMonoidal.ε (componentInverse T) ≫
      (componentUnitCorrection T).hom.app (𝟙_ _) =
        (componentCanonicalMonoidal T).toLaxMonoidal.ε := by
  let e := componentUnitRatio T
  let ε₁ := Functor.LaxMonoidal.ε (componentInverse T)
  let s : 𝟭 (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ≅ 𝟭 _ :=
    (MonoidalCategory.leftUnitorNatIso _).symm ≪≫
      (MonoidalCategory.curriedTensor _).mapIso e ≪≫ MonoidalCategory.leftUnitorNatIso _
  have hs : s.hom.app (𝟙_ _) = e.hom := by
    change (λ_ _).inv ≫ e.hom ▷ (𝟙_ _) ≫ (λ_ _).hom = e.hom
    rw [MonoidalCategory.unitors_inv_equal, MonoidalCategory.unitors_equal,
      MonoidalCategory.rightUnitor_naturality]
    simp
  change ε₁ ≫ s.hom.app _ = _
  have hn := s.hom.naturality ε₁
  change ε₁ ≫ s.hom.app _ = s.hom.app _ ≫ ε₁ at hn
  refine hn.trans ?_
  change s.hom.app (𝟙_ _) ≫ ε₁ = _
  rw [hs]
  simp [e, componentUnitRatio, ε₁]

/-- After correcting the unit, the supplied tensor comparison agrees with the
canonical inverse-image comparison.

Source: Hemo--Richarz--Scholbach, Construction (4.1), monoidal inverse image;
(blueprint: lem-zl-component-unit-normalized-tensor).

Proof: present abelian sheaves by free sheaves on profinite tests. Tensor products
of free test sheaves are free on products of tests. The two bilinear maps are natural
in both tests. On finite tests, coproduct inclusions reduce their values to the unit
comparison; the ratio in `componentUnitCorrection` makes these values equal.
For general profinite tests, use their finite clopen quotients. The sectionwise free
abelian generators are detected by these quotients: any finite collection of distinct
points is separated by a finite clopen partition. Thus the two bilinear maps agree on
free test generators. Sheafification preserves the coequalizer presentations and the
inverse image and tensor preserve colimits, so the identity descends to arbitrary
abelian sheaves. The empty test has zero free sheaf and contributes the zero equation.
Only the tensor equation remains here; the correction is explicitly invertible and
its unit equation follows from naturality of the unitors. -/
theorem component_unit_normalized_tensor
    (X Y : Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      Ab.{u + 1}) :
    Functor.LaxMonoidal.μ (componentInverse T) X Y ≫
        (componentUnitCorrection T).hom.app (X ⊗ Y) =
      ((componentUnitCorrection T).hom.app X ⊗ₘ
        (componentUnitCorrection T).hom.app Y) ≫
          (componentCanonicalMonoidal T).toLaxMonoidal.μ X Y := by
  let F := componentInverse T
  let J := (coherentTopology Profinite.{u}).over (affineComponentSpace T)
  let γ := (componentUnitCorrection T).hom
  let e₁ := MonoidalCategory.Functor.curriedTensorPreIsoPost F
  let e₀ : curriedTensorPre F ≅ curriedTensorPost F := by
    let := componentCanonicalMonoidal T
    exact MonoidalCategory.Functor.curriedTensorPreIsoPost F
  let α := e₁.hom ≫ curriedTensorPostFunctor.map γ
  let β := curriedTensorPreFunctor.map γ ≫ e₀.hom
  have hunit : (α.app (𝟙_ _)).app (𝟙_ _) = (β.app (𝟙_ _)).app (𝟙_ _) :=
    unit_tensor_compatibility F (inferInstance : F.LaxMonoidal)
      (componentCanonicalMonoidal T) γ (correction_unit T) _
  let : F.IsLeftAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (componentTests T) Ab.{u + 1} J (Scheme.ProEt.topology T)).isLeftAdjoint
  have hfree (E E' : Over (affineComponentSpace T)) :
      (α.app (Sheaf.freeYoneda J E (𝟙_ Ab.{u + 1}))).app
          (Sheaf.freeYoneda J E' (𝟙_ Ab.{u + 1})) =
        (β.app (Sheaf.freeYoneda J E (𝟙_ Ab.{u + 1}))).app
          (Sheaf.freeYoneda J E' (𝟙_ Ab.{u + 1})) := by
    let A := Sheaf.freeYoneda J E (𝟙_ Ab.{u + 1})
    let B := Sheaf.freeYoneda J E' (𝟙_ Ab.{u + 1})
    apply (cancel_mono ((e₀.inv.app A).app B)).1
    apply component_free_tensor_detection T E E'
    intro a b
    have hd : (e₀.inv.app A).app B ≫ (F.map a ⊗ₘ F.map b) =
        F.map (a ⊗ₘ b) ≫ (e₀.inv.app (𝟙_ _)).app (𝟙_ _) := by
      let := componentCanonicalMonoidal T
      exact Functor.OplaxMonoidal.δ_natural F a b
    change ((α.app A).app B ≫ (e₀.inv.app A).app B) ≫
        (F.map a ⊗ₘ F.map b) =
      ((β.app A).app B ≫ (e₀.inv.app A).app B) ≫ (F.map a ⊗ₘ F.map b)
    simp only [Category.assoc]
    rw [hd]
    simp only [← Category.assoc]
    rw [← tensor_naturality F α a b, ← tensor_naturality F β a b, hunit]
  have heq : α = β := by
    apply tensor_bifunctor_ext (freeSheaf_separating J) F α β
    intro A hA B hB
    obtain ⟨E⟩ := hA
    obtain ⟨E'⟩ := hB
    exact hfree E E'
  exact NatTrans.congr_app (NatTrans.congr_app heq X) Y

end AlgebraicGeometry.ProEtale.CondensedRing
