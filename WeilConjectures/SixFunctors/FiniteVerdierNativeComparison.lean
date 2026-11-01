/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientVerdierData
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDualitySiteComparison
import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual

/-! # Shared native comparison calculus for finite Verdier diagrams

Source: current blueprint cor-coef-finite-verdier.proof.md, the Hom comparison,
evaluation, double-dual and quotient cocycle sentences.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.style.haveILetI false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

attribute [local implicit_reducible]
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.monoidalClosed_sheaf_of_essentiallySmall
  Etale.sheafMonoidalCategory Etale.sheafBraidedCategory Etale.sheafMonoidalClosed
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory
  ProEtale.sheafSymmetricCategory ProEtale.sheafMonoidalClosed
  Sheaf.symmetricCategory Sheaf.braidedCategory


attribute [local implicit_reducible] CategoryTheory.catToReflQuiver
  Etale.derivedTensorHomAdjunction Etale.derivedTensorHomAdjunction₂
  finiteVerdierEtaleTensorAt finiteVerdierEtaleHomAt
  finiteVerdierProEtaleTensorAt finiteVerdierProEtaleHomAt

attribute [local irreducible]
  CategoryTheory.Functor.LaxMonoidal.ihomComparison
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution
  pbcFixedScalarExtension Functor.mapDerivedCategory

section NativeComparison
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
variable {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]
  {B : Type*} [Category B] [MonoidalCategory B] [MonoidalClosed B]


def finiteVerdier_nativeTargetArrow (F : C ⥤ B) [F.LaxMonoidal]
    {W : C} {W' : B} (uMap : F.obj W ⟶ W') (K : C) :
    F.obj ((ihom K).obj W) ⟶ (ihom (F.obj K)).obj W' :=
  (Functor.LaxMonoidal.ihomComparison F K).natTrans.app W ≫
    (ihom (F.obj K)).map uMap



def finiteVerdier_nativeTargetComparison (F : C ⥤ B) [F.LaxMonoidal]
    {W : C} {W' : B} (uMap : F.obj W ⟶ W') :
    internalHom.flip.obj W ⋙ F ⟶ F.op ⋙ internalHom.flip.obj W' where
  app K := finiteVerdier_nativeTargetArrow F uMap K.unop
  naturality {K L} f := by
    change F.map ((pre f.unop).app W) ≫ finiteVerdier_nativeTargetArrow F uMap L.unop =
      finiteVerdier_nativeTargetArrow F uMap K.unop ≫ (pre (F.map f.unop)).app W'
    dsimp only [finiteVerdier_nativeTargetArrow]
    rw [Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app_assoc]
    simp only [Category.assoc]
    rw [← (pre (F.map f.unop)).naturality]



theorem finiteVerdier_nativeTargetArrow_ev (F : C ⥤ B) [F.LaxMonoidal]
    {W : C} {W' : B} (uMap : F.obj W ⟶ W') (K : C) :
    F.obj K ◁ finiteVerdier_nativeTargetArrow F uMap K ≫ (ihom.ev (F.obj K)).app W' =
      Functor.LaxMonoidal.μ F K _ ≫ F.map ((ihom.ev K).app W) ≫ uMap := by
  dsimp only [finiteVerdier_nativeTargetArrow]
  rw [← uncurry_eq, uncurry_natural_right, uncurry_eq,
    Functor.LaxMonoidal.ihomComparison_ev, Category.assoc]



theorem finiteVerdier_nativeTargetArrow_right_ev [SymmetricCategory C] [SymmetricCategory B]
    (F : C ⥤ B) [F.Braided] {W : C} {W' : B} (uMap : F.obj W ⟶ W') (K : C) :
    finiteVerdier_nativeTargetArrow F uMap K ▷ F.obj K ≫
        (β_ ((ihom (F.obj K)).obj W') (F.obj K)).hom ≫
          (ihom.ev (F.obj K)).app W' =
      Functor.LaxMonoidal.μ F ((ihom K).obj W) K ≫
        F.map ((β_ ((ihom K).obj W) K).hom ≫ (ihom.ev K).app W) ≫ uMap := by
  rw [BraidedCategory.braiding_naturality_left_assoc, finiteVerdier_nativeTargetArrow_ev,
    ← Functor.LaxBraided.braided_assoc, F.map_comp, Category.assoc]



theorem finiteVerdier_nativeTargetArrow_bidual [SymmetricCategory C] [SymmetricCategory B]
    (F : C ⥤ B) [F.Braided] {W : C} {W' : B} (uMap : F.obj W ⟶ W') (K : C) :
    F.map (toIhomIhom W K) ≫ finiteVerdier_nativeTargetArrow F uMap ((ihom K).obj W) =
      toIhomIhom W' (F.obj K) ≫
        (internalHom.flip.obj W').map ((finiteVerdier_nativeTargetArrow F uMap K).op) := by
  exact map_toIhomIhom_comp_dualComparison F uMap K



theorem finiteVerdier_nativeTargetArrow_unit (F : C ⥤ C) [F.LaxMonoidal]
    (ε : F ≅ 𝟭 C) [NatTrans.IsMonoidal ε.hom] (W K : C) :
    finiteVerdier_nativeTargetArrow F (ε.hom.app W) K =
      ε.hom.app ((ihom K).obj W) ≫ (internalHom.flip.obj W).map ((ε.hom.app K).op) := by
  change finiteVerdier_nativeTargetArrow F (ε.hom.app W) K =
    ε.hom.app ((ihom K).obj W) ≫ (pre (ε.hom.app K)).app W
  have hi : (Functor.LaxMonoidal.ihomComparison (𝟭 C) K).natTrans.app W = 𝟙 _ := by
    rw [Functor.LaxMonoidal.ihomComparison_app_eq_curry]
    change curry (𝟙 _ ≫ (ihom.ev K).app W) = 𝟙 _
    rw [Category.id_comp, curry_eq_iff]
    exact (uncurry_id_eq_ev K W).symm
  have hh := Functor.LaxMonoidal.ihomComparison_app_comp_map_app ε.hom K W
  exact hh.trans ((congrArg
    (fun f ↦ ε.hom.app ((ihom K).obj W) ≫ f ≫ (pre (ε.hom.app K)).app W) hi).trans
      (congrArg (fun f ↦ ε.hom.app ((ihom K).obj W) ≫ f)
        (Category.id_comp ((pre (ε.hom.app K)).app W))))



theorem finiteVerdier_nativeTargetArrow_cocycle
    {A : Type*} [Category A] [MonoidalCategory A] [MonoidalClosed A]
    (F : C ⥤ B) (G : B ⥤ A) (J : C ⥤ A)
    [F.LaxMonoidal] [G.LaxMonoidal] [J.LaxMonoidal]
    (α : F ⋙ G ≅ J) [NatTrans.IsMonoidal α.hom]
    {W : C} {W' : B} {W'' : A}
    (uMap : F.obj W ⟶ W') (vMap : G.obj W' ⟶ W'') (wMap : J.obj W ⟶ W'')
    (huv : G.map uMap ≫ vMap = α.hom.app W ≫ wMap) (K : C) :
    G.map (finiteVerdier_nativeTargetArrow F uMap K) ≫
        finiteVerdier_nativeTargetArrow G vMap (F.obj K) ≫
          (internalHom.flip.obj W'').map ((α.inv.app K).op) =
      α.hom.app ((ihom K).obj W) ≫ finiteVerdier_nativeTargetArrow J wMap K := by
  change G.map (finiteVerdier_nativeTargetArrow F uMap K) ≫
    finiteVerdier_nativeTargetArrow G vMap (F.obj K) ≫ (pre (α.inv.app K)).app W'' = _
  dsimp only [finiteVerdier_nativeTargetArrow]
  simp only [G.map_comp, Category.assoc]
  rw [
    reassoc_of% (Functor.LaxMonoidal.ihomComparison G (F.obj K)).natTrans.naturality uMap,
    ← Category.assoc (G.map _) _,
    ← Functor.LaxMonoidal.ihomComparison_comp_app,
    ← (ihom (G.obj (F.obj K))).map_comp_assoc, huv,
    (ihom (G.obj (F.obj K))).map_comp]
  simp only [Category.assoc]
  have hh := Functor.LaxMonoidal.ihomComparison_app_comp_map_app α.hom K W
  dsimp only [Functor.comp_obj] at hh
  rw [← Category.assoc _ ((ihom (G.obj (F.obj K))).map (α.hom.app W)) _, hh,
    Category.assoc, Category.assoc]
  have hp := (pre (α.hom.app K)).naturality wMap
  dsimp only [Functor.comp_obj] at hp
  rw [← reassoc_of% hp]
  have hcancel : (pre (α.hom.app K)).app W'' ≫ (pre (α.inv.app K)).app W'' = 𝟙 _ := by
    change ((internalHom.map (α.hom.app K).op).app W'') ≫
      ((internalHom.map (α.inv.app K).op).app W'') = _
    rw [← NatTrans.comp_app, ← internalHom.map_comp, ← op_comp,
      α.inv_hom_id_app, op_id, internalHom.map_id, NatTrans.id_app]
    rfl
  rw [hcancel, Category.comp_id]

end NativeComparison


theorem finiteVerdier_etalePairing_normalized
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})
    (W : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (h : Etale.AmbientDualityPairing A X W)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    letI := DerivedCategory.symmetricCategory (Sheaf X.smallEtaleTopology A)
    h.choose_spec.2.choose K =
        (β_ ((CategoryTheory.ihom K).obj W) K).hom ≫
          (CategoryTheory.ihom.ev K).app W ∧
      h.choose_spec.2.choose_spec.2.choose K = MonoidalClosed.toIhomIhom W K := by
  letI := DerivedCategory.symmetricCategory (Sheaf X.smallEtaleTopology A)
  have he (L) : (ihom.adjunction L).homEquiv _ W
      (((h.choose.hom.app L).app ((ihom L).obj W)) ≫ h.choose_spec.2.choose L) = 𝟙 _ :=
    h.choose_spec.2.choose_spec.1 L
  have hd (L) : h.choose_spec.2.choose_spec.2.choose L =
      (ihom.adjunction ((ihom L).obj W)).homEquiv L W (h.choose_spec.2.choose L) :=
    h.choose_spec.2.choose_spec.2.choose_spec.1 L
  have hb (L M) := (h.choose_spec.1 L M).trans (CategoryTheory.native_braiding L M)
  exact CategoryTheory.normalized_pairing W h.choose hb
    h.choose_spec.2.choose he h.choose_spec.2.choose_spec.2.choose hd K



section EtaleAbstractPairing
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
variable (A B : Type (u + 2))
  [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
  [Abelian.HasFunctorialFlatResolution B]
  (X : Scheme.{u})
local instance etaleAmbientSymmetric :
    SymmetricCategory (DerivedCategory (Sheaf (X.smallEtaleTopology) A)) :=
  DerivedCategory.symmetricCategory _
variable
  (F : DerivedCategory (Sheaf (X.smallEtaleTopology) A) ⥤
    DerivedCategory (Sheaf (X.smallEtaleTopology) B)) [F.Braided]
  {W : DerivedCategory (Sheaf (X.smallEtaleTopology) A)}
  {W' : DerivedCategory (Sheaf (X.smallEtaleTopology) B)}
  (uMap : F.obj W ⟶ W')
  (hR : Etale.AmbientDualityPairing A X W)
  (hS : Etale.AmbientDualityPairing B X W')
  (K : DerivedCategory (Sheaf (X.smallEtaleTopology) A))
def finiteVerdier_etaleAmbientArrow :
    F.obj (((Etale.derivedHom A X).obj (op K)).obj W) ⟶
      (((Etale.derivedHom B X).obj (op (F.obj K))).obj W') :=
  finiteVerdier_nativeTargetArrow F uMap K

def finiteVerdier_etaleAmbientComparison :
    (Etale.derivedHom A X).flip.obj W ⋙ F ⟶
      F.op ⋙ (Etale.derivedHom B X).flip.obj W' where
  app L := finiteVerdier_etaleAmbientArrow A B X F uMap L.unop
  naturality {L M} f := by
    exact (finiteVerdier_nativeTargetComparison F uMap).naturality f

attribute [local implicit_reducible] finiteVerdier_etaleAmbientArrow

theorem finiteVerdier_etaleAmbientArrow_isIso
    (hHom : IsIso ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app W))
    (hU : IsIso uMap) : IsIso (finiteVerdier_etaleAmbientArrow A B X F uMap K) := by
  unfold finiteVerdier_etaleAmbientArrow finiteVerdier_nativeTargetArrow
  letI := hU
  exact IsIso.comp_isIso' hHom (Functor.map_isIso (ihom (F.obj K)) uMap)

theorem finiteVerdier_etalePairing_evaluation :
    ((Etale.derivedTensor B X).map (finiteVerdier_etaleAmbientArrow A B X F uMap K)).app
        (F.obj K) ≫ finiteVerdierEtaleEvaluation B X hS (F.obj K) =
      Functor.LaxMonoidal.μ F (((Etale.derivedHom A X).obj (op K)).obj W) K ≫
        F.map (finiteVerdierEtaleEvaluation A X hR K) ≫ uMap := by
  have eR := (finiteVerdier_etalePairing_normalized A X W hR K).1
  have eS := (finiteVerdier_etalePairing_normalized B X W' hS (F.obj K)).1
  exact (congrArg (fun f ↦ finiteVerdier_etaleAmbientArrow A B X F uMap K ▷ F.obj K ≫ f) eS).trans
    ((finiteVerdier_nativeTargetArrow_right_ev F uMap K).trans
      (congrArg
        (fun f ↦ Functor.LaxMonoidal.μ F (((Etale.derivedHom A X).obj (op K)).obj W) K ≫
          F.map f ≫ uMap)
        eR.symm))
theorem finiteVerdier_etalePairing_biduality :
    F.map (Etale.AmbientDualityPairing.bidualityMap A X hR K) ≫
        finiteVerdier_etaleAmbientArrow A B X F uMap (((Etale.derivedHom A X).obj (op K)).obj W) =
      Etale.AmbientDualityPairing.bidualityMap B X hS (F.obj K) ≫
        ((Etale.derivedHom B X).flip.obj W').map
          ((finiteVerdier_etaleAmbientArrow A B X F uMap K).op) := by
  have dR := (finiteVerdier_etalePairing_normalized A X W hR K).2
  have dS := (finiteVerdier_etalePairing_normalized B X W' hS (F.obj K)).2
  exact (congrArg
    (fun f ↦ F.map f ≫ finiteVerdier_etaleAmbientArrow A B X F uMap
      (((Etale.derivedHom A X).obj (op K)).obj W)) dR).trans
    ((finiteVerdier_nativeTargetArrow_bidual F uMap K).trans
      (congrArg (fun f ↦ f ≫ (internalHom.flip.obj W').map
        ((finiteVerdier_etaleAmbientArrow A B X F uMap K).op)) dS.symm))
theorem finiteVerdier_etalePairing_unit
    (G : DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A))
    [G.Braided] (ε : G ≅ 𝟭 _) [NatTrans.IsMonoidal ε.hom]
    (V L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    finiteVerdier_etaleAmbientArrow A A X G (ε.hom.app V) L =
      ε.hom.app (((Etale.derivedHom A X).obj (op L)).obj V) ≫
        ((Etale.derivedHom A X).flip.obj V).map ((ε.hom.app L).op) := by
  exact finiteVerdier_nativeTargetArrow_unit G ε V L

theorem finiteVerdier_etalePairing_cocycle
    (T : Type (u + 2)) [Category.{u + 1} T] [Abelian T]
    [IsGrothendieckAbelian.{u + 1} T] [MonoidalCategory T]
    [MonoidalPreadditive T] [SymmetricCategory T] [MonoidalClosed T]
    [Abelian.HasFunctorialFlatResolution T]
    (G : DerivedCategory (Sheaf X.smallEtaleTopology B) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology T))
    (H : DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology T))
    [G.Braided] [H.Braided] (α : F ⋙ G ≅ H) [NatTrans.IsMonoidal α.hom]
    {W'' : DerivedCategory (Sheaf X.smallEtaleTopology T)}
    (vMap : G.obj W' ⟶ W'') (wMap : H.obj W ⟶ W'')
    (huv : G.map uMap ≫ vMap = α.hom.app W ≫ wMap) :
    G.map (finiteVerdier_etaleAmbientArrow A B X F uMap K) ≫
        finiteVerdier_etaleAmbientArrow B T X G vMap (F.obj K) ≫
          ((Etale.derivedHom T X).flip.obj W'').map ((α.inv.app K).op) =
      α.hom.app (((Etale.derivedHom A X).obj (op K)).obj W) ≫
        finiteVerdier_etaleAmbientArrow A T X H wMap K := by
  exact finiteVerdier_nativeTargetArrow_cocycle F G H α uMap vMap wMap huv K

end EtaleAbstractPairing
attribute [local irreducible] finiteVerdier_etaleAmbientArrow


section ProAbstractPairing
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
variable (A B : Type (u + 2))
  [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
  [Abelian.HasFunctorialFlatResolution B]
  (X : Scheme.{u})
local instance proAmbientSymmetric :
    SymmetricCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  DerivedCategory.symmetricCategory _
variable
  (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) B)) [F.Braided]
  {W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
  {W' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B)}
  (uMap : F.obj W ⟶ W')
  (hR : ProEtale.AmbientDualityPairing A X W)
  (hS : ProEtale.AmbientDualityPairing B X W')
  (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
def finiteVerdier_proAmbientArrow :
    F.obj (((ProEtale.derivedHom A X).obj (op K)).obj W) ⟶
      (((ProEtale.derivedHom B X).obj (op (F.obj K))).obj W') :=
  finiteVerdier_nativeTargetArrow F uMap K

def finiteVerdier_proAmbientComparison :
    (ProEtale.derivedHom A X).flip.obj W ⋙ F ⟶
      F.op ⋙ (ProEtale.derivedHom B X).flip.obj W' where
  app L := finiteVerdier_proAmbientArrow A B X F uMap L.unop
  naturality {L M} f := by
    exact (finiteVerdier_nativeTargetComparison F uMap).naturality f

attribute [local implicit_reducible] finiteVerdier_proAmbientArrow

theorem finiteVerdier_proAmbientArrow_isIso
    (hHom : IsIso ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app W))
    (hU : IsIso uMap) : IsIso (finiteVerdier_proAmbientArrow A B X F uMap K) := by
  unfold finiteVerdier_proAmbientArrow finiteVerdier_nativeTargetArrow
  letI := hU
  exact IsIso.comp_isIso' hHom (Functor.map_isIso (ihom (F.obj K)) uMap)

theorem finiteVerdier_proPairing_evaluation :
    ((ProEtale.derivedTensor B X).map (finiteVerdier_proAmbientArrow A B X F uMap K)).app
        (F.obj K) ≫ finiteVerdierProEtaleEvaluation B X hS (F.obj K) =
      Functor.LaxMonoidal.μ F (((ProEtale.derivedHom A X).obj (op K)).obj W) K ≫
        F.map (finiteVerdierProEtaleEvaluation A X hR K) ≫ uMap := by
  have eR := (ProEtale.pairing_normalized A X W hR K).1
  have eS := (ProEtale.pairing_normalized B X W' hS (F.obj K)).1
  exact (congrArg (fun f ↦ finiteVerdier_proAmbientArrow A B X F uMap K ▷ F.obj K ≫ f) eS).trans
    ((finiteVerdier_nativeTargetArrow_right_ev F uMap K).trans
      (congrArg
        (fun f ↦ Functor.LaxMonoidal.μ F (((ProEtale.derivedHom A X).obj (op K)).obj W) K ≫
          F.map f ≫ uMap)
        eR.symm))
theorem finiteVerdier_proPairing_biduality :
    F.map (finiteVerdierProEtaleBiduality A X hR K) ≫
        finiteVerdier_proAmbientArrow A B X F uMap (((ProEtale.derivedHom A X).obj (op K)).obj W) =
      finiteVerdierProEtaleBiduality B X hS (F.obj K) ≫
        ((ProEtale.derivedHom B X).flip.obj W').map
          ((finiteVerdier_proAmbientArrow A B X F uMap K).op) := by
  have dR := (ProEtale.pairing_normalized A X W hR K).2
  have dS := (ProEtale.pairing_normalized B X W' hS (F.obj K)).2
  exact (congrArg
    (fun f ↦ F.map f ≫ finiteVerdier_proAmbientArrow A B X F uMap
      (((ProEtale.derivedHom A X).obj (op K)).obj W)) dR).trans
    ((finiteVerdier_nativeTargetArrow_bidual F uMap K).trans
      (congrArg (fun f ↦ f ≫ (internalHom.flip.obj W').map
        ((finiteVerdier_proAmbientArrow A B X F uMap K).op)) dS.symm))
theorem finiteVerdier_proPairing_unit
    (G : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    [G.Braided] (ε : G ≅ 𝟭 _) [NatTrans.IsMonoidal ε.hom]
    (V L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    finiteVerdier_proAmbientArrow A A X G (ε.hom.app V) L =
      ε.hom.app (((ProEtale.derivedHom A X).obj (op L)).obj V) ≫
        ((ProEtale.derivedHom A X).flip.obj V).map ((ε.hom.app L).op) := by
  exact finiteVerdier_nativeTargetArrow_unit G ε V L

theorem finiteVerdier_proPairing_cocycle
    (T : Type (u + 2)) [Category.{u + 1} T] [Abelian T]
    [IsGrothendieckAbelian.{u + 1} T] [MonoidalCategory T]
    [MonoidalPreadditive T] [SymmetricCategory T] [MonoidalClosed T]
    [Abelian.HasFunctorialFlatResolution T]
    (G : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) T))
    (H : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) T))
    [G.Braided] [H.Braided] (α : F ⋙ G ≅ H) [NatTrans.IsMonoidal α.hom]
    {W'' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) T)}
    (vMap : G.obj W' ⟶ W'') (wMap : H.obj W ⟶ W'')
    (huv : G.map uMap ≫ vMap = α.hom.app W ≫ wMap) :
    G.map (finiteVerdier_proAmbientArrow A B X F uMap K) ≫
        finiteVerdier_proAmbientArrow B T X G vMap (F.obj K) ≫
          ((ProEtale.derivedHom T X).flip.obj W'').map ((α.inv.app K).op) =
      α.hom.app (((ProEtale.derivedHom A X).obj (op K)).obj W) ≫
        finiteVerdier_proAmbientArrow A T X H wMap K := by
  exact finiteVerdier_nativeTargetArrow_cocycle F G H α uMap vMap wMap huv K

end ProAbstractPairing
attribute [local irreducible] finiteVerdier_proAmbientArrow



section EtaleCoherentAssembly
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
variable (A : ℕ → Type (u + 2))
  [∀ n, Category.{u + 1} (A n)] [∀ n, Abelian (A n)]
  [∀ n, IsGrothendieckAbelian.{u + 1} (A n)] [∀ n, MonoidalCategory (A n)]
  [∀ n, MonoidalPreadditive (A n)] [∀ n, SymmetricCategory (A n)]
  [∀ n, MonoidalClosed (A n)] [∀ n, Abelian.HasFunctorialFlatResolution (A n)]
  (X : Scheme.{u})
local instance etaleTowerSymmetric (n : ℕ) :
    SymmetricCategory (DerivedCategory (Sheaf X.smallEtaleTopology (A n))) :=
  DerivedCategory.symmetricCategory _

/-- Assemble coherent Verdier diagrams from the native tensor-Hom comparison.
The hypothesis about Hom is only invertibility; the evaluation, biduality, unit
and quotient cocycle conclusions follow from the monoidal structures and target maps.
(blueprint: lem-coef-verdier-native-comparison-calculus). -/
theorem finiteVerdier_etale_coherent_assembly
    (W : ∀ n, DerivedCategory (Sheaf X.smallEtaleTopology (A n)))
    (P : ∀ n, ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (A n))))
    (F : ∀ {n m : ℕ}, m ≤ n → DerivedCategory (Sheaf X.smallEtaleTopology (A n)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (A m)))
    [∀ {n m : ℕ} (h : m ≤ n), (F h).Braided]
    (unit : ∀ n, F (le_refl n) ≅ 𝟭 _)
    (comp : ∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m), F h ⋙ F g ≅ F (g.trans h))
    (hunit : ∀ n, NatTrans.IsMonoidal (unit n).hom)
    (hcomp : ∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m),
      NatTrans.IsMonoidal (comp h g).hom)
    (μ : ∀ {n m : ℕ} (h : m ≤ n),
      tensor (C := DerivedCategory (Sheaf X.smallEtaleTopology (A n))) ⋙ F h ≅
        (F h).prod (F h) ⋙
          tensor (C := DerivedCategory (Sheaf X.smallEtaleTopology (A m))))
    (hμ : ∀ {n m : ℕ} (h : m ≤ n) K L,
      (μ h).inv.app (K, L) = Functor.LaxMonoidal.μ (F h) K L)
    (pairing : ∀ n, Etale.AmbientDualityPairing (A n) X (W n))
    (uMap : ∀ {n m : ℕ} (h : m ≤ n), (F h).obj (W n) ⟶ W m)
    (hpres : ∀ {n m : ℕ} (h : m ≤ n) K, P n K → P m ((F h).obj K))
    (hHom : ∀ {n m : ℕ} (h : m ≤ n) K, P n K →
      IsIso ((Functor.LaxMonoidal.ihomComparison (F h) K).natTrans.app (W n)))
    (huIso : ∀ {n m : ℕ} (h : m ≤ n), IsIso (uMap h))
    (huUnit : ∀ n, uMap (le_refl n) = (unit n).hom.app (W n))
    (huComp : ∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m),
      (F g).map (uMap h) ≫ uMap g = (comp h g).hom.app (W n) ≫ uMap (g.trans h)) :
    @FiniteVerdierCoherentComparison
      (fun n ↦ DerivedCategory (Sheaf X.smallEtaleTopology (A n)))
      (fun _n ↦ inferInstance)
      (fun n ↦ Etale.derivedTensor (A n) X) (fun n ↦ Etale.derivedHom (A n) X)
      W P (fun _ _ _ _ ↦ True) (fun {_ _} h ↦ F h) unit
      (fun {_ _ _} h g ↦ comp h g) (fun {_ _} h ↦ μ h)
      (fun n K ↦ finiteVerdierEtaleEvaluation (A n) X (pairing n) K)
      (fun n K ↦ Etale.AmbientDualityPairing.bidualityMap (A n) X (pairing n) K)
      (fun {_ _} h ↦ uMap h) 0 := by
  let τ {n m : ℕ} (h : m ≤ n) :=
    finiteVerdier_etaleAmbientComparison (A n) (A m) X (F h) (uMap h)
  refine ⟨fun {_ _} h ↦ τ h, ?_, ?_, ?_⟩
  · intro n m h K hK
    refine ⟨hpres h K hK, ?_, ?_, ?_, ?_⟩
    · exact finiteVerdier_etaleAmbientArrow_isIso (A n) (A m) X (F h)
        (uMap h) K (hHom h K hK) (huIso h)
    · have he := finiteVerdier_etalePairing_evaluation (A n) (A m) X (F h)
        (uMap h) (pairing n) (pairing m) K
      exact he.trans (congrArg
        (fun f ↦ f ≫ (F h).map (finiteVerdierEtaleEvaluation (A n) X (pairing n) K) ≫
          uMap h) (hμ h _ _).symm)
    · exact finiteVerdier_etalePairing_biduality (A n) (A m) X (F h)
        (uMap h) (pairing n) (pairing m) K
    · intro a b hab hTor
      trivial
  · intro n K hK
    letI := hunit n
    exact (congrArg
      (fun v ↦ finiteVerdier_etaleAmbientArrow (A n) (A n) X (F (le_refl n)) v K)
      (huUnit n)).trans
      (finiteVerdier_etalePairing_unit (A n) X (F (le_refl n)) (unit n) (W n) K)
  · intro n m r h g K hK
    letI := hcomp h g
    exact finiteVerdier_etalePairing_cocycle
      (A := A n) (B := A m) (X := X) (F := F h) (uMap := uMap h) (K := K)
      (T := A r) (G := F g) (H := F (g.trans h)) (α := comp h g)
      (vMap := uMap g) (wMap := uMap (g.trans h)) (huv := huComp h g)

end EtaleCoherentAssembly

section ProEtaleCoherentAssembly
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
variable (A : ℕ → Type (u + 2))
  [∀ n, Category.{u + 1} (A n)] [∀ n, Abelian (A n)]
  [∀ n, IsGrothendieckAbelian.{u + 1} (A n)] [∀ n, MonoidalCategory (A n)]
  [∀ n, MonoidalPreadditive (A n)] [∀ n, SymmetricCategory (A n)]
  [∀ n, MonoidalClosed (A n)] [∀ n, Abelian.HasFunctorialFlatResolution (A n)]
  (X : Scheme.{u})
local instance proEtaleTowerSymmetric (n : ℕ) :
    SymmetricCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (A n))) :=
  DerivedCategory.symmetricCategory _

/-- Assemble coherent Verdier diagrams from the native tensor-Hom comparison.
The hypothesis about Hom is only invertibility; the evaluation, biduality, unit
and quotient cocycle conclusions follow from the monoidal structures and target maps.
(blueprint: lem-coef-verdier-native-comparison-calculus). -/
theorem finiteVerdier_pro_coherent_assembly
    (W : ∀ n, DerivedCategory (Sheaf (Scheme.ProEt.topology X) (A n)))
    (P : ∀ n, ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (A n))))
    (F : ∀ {n m : ℕ}, m ≤ n → DerivedCategory (Sheaf (Scheme.ProEt.topology X) (A n)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (A m)))
    [∀ {n m : ℕ} (h : m ≤ n), (F h).Braided]
    (unit : ∀ n, F (le_refl n) ≅ 𝟭 _)
    (comp : ∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m), F h ⋙ F g ≅ F (g.trans h))
    (hunit : ∀ n, NatTrans.IsMonoidal (unit n).hom)
    (hcomp : ∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m),
      NatTrans.IsMonoidal (comp h g).hom)
    (μ : ∀ {n m : ℕ} (h : m ≤ n),
      tensor (C := DerivedCategory (Sheaf (Scheme.ProEt.topology X) (A n))) ⋙ F h ≅
        (F h).prod (F h) ⋙
          tensor (C := DerivedCategory (Sheaf (Scheme.ProEt.topology X) (A m))))
    (hμ : ∀ {n m : ℕ} (h : m ≤ n) K L,
      (μ h).inv.app (K, L) = Functor.LaxMonoidal.μ (F h) K L)
    (pairing : ∀ n, ProEtale.AmbientDualityPairing (A n) X (W n))
    (uMap : ∀ {n m : ℕ} (h : m ≤ n), (F h).obj (W n) ⟶ W m)
    (hpres : ∀ {n m : ℕ} (h : m ≤ n) K, P n K → P m ((F h).obj K))
    (hHom : ∀ {n m : ℕ} (h : m ≤ n) K, P n K →
      IsIso ((Functor.LaxMonoidal.ihomComparison (F h) K).natTrans.app (W n)))
    (huIso : ∀ {n m : ℕ} (h : m ≤ n), IsIso (uMap h))
    (huUnit : ∀ n, uMap (le_refl n) = (unit n).hom.app (W n))
    (huComp : ∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m),
      (F g).map (uMap h) ≫ uMap g = (comp h g).hom.app (W n) ≫ uMap (g.trans h)) :
    @FiniteVerdierCoherentComparison
      (fun n ↦ DerivedCategory (Sheaf (Scheme.ProEt.topology X) (A n)))
      (fun _n ↦ inferInstance)
      (fun n ↦ ProEtale.derivedTensor (A n) X) (fun n ↦ ProEtale.derivedHom (A n) X)
      W P (fun _ _ _ _ ↦ True) (fun {_ _} h ↦ F h) unit
      (fun {_ _ _} h g ↦ comp h g) (fun {_ _} h ↦ μ h)
      (fun n K ↦ finiteVerdierProEtaleEvaluation (A n) X (pairing n) K)
      (fun n K ↦ ProEtale.AmbientDualityPairing.bidualityMap (A n) X (pairing n) K)
      (fun {_ _} h ↦ uMap h) 0 := by
  let τ {n m : ℕ} (h : m ≤ n) :=
    finiteVerdier_proAmbientComparison (A n) (A m) X (F h) (uMap h)
  refine ⟨fun {_ _} h ↦ τ h, ?_, ?_, ?_⟩
  · intro n m h K hK
    refine ⟨hpres h K hK, ?_, ?_, ?_, ?_⟩
    · exact finiteVerdier_proAmbientArrow_isIso (A n) (A m) X (F h)
        (uMap h) K (hHom h K hK) (huIso h)
    · have he := finiteVerdier_proPairing_evaluation (A n) (A m) X (F h)
        (uMap h) (pairing n) (pairing m) K
      exact he.trans (congrArg
        (fun f ↦ f ≫ (F h).map (finiteVerdierProEtaleEvaluation (A n) X (pairing n) K) ≫
          uMap h) (hμ h _ _).symm)
    · exact finiteVerdier_proPairing_biduality (A n) (A m) X (F h)
        (uMap h) (pairing n) (pairing m) K
    · intro a b hab hTor
      trivial
  · intro n K hK
    letI := hunit n
    exact (congrArg
      (fun v ↦ finiteVerdier_proAmbientArrow (A n) (A n) X (F (le_refl n)) v K)
      (huUnit n)).trans
      (finiteVerdier_proPairing_unit (A n) X (F (le_refl n)) (unit n) (W n) K)
  · intro n m r h g K hK
    letI := hcomp h g
    exact finiteVerdier_proPairing_cocycle
      (A := A n) (B := A m) (X := X) (F := F h) (uMap := uMap h) (K := K)
      (T := A r) (G := F g) (H := F (g.trans h)) (α := comp h g)
      (vMap := uMap g) (wMap := uMap (g.trans h)) (huv := huComp h g)

end ProEtaleCoherentAssembly

end WeilConjectures
