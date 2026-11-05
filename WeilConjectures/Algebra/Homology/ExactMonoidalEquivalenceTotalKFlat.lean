/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.CountableTensorStructures
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

import WeilConjectures.Algebra.Homology.AdditiveTotalTensorConeComparison
import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Functor
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Exact symmetric monoidal equivalences and signed total K-flatness

Source: Stacks Project, Tag 06YP, `lemma-K-flat-quasi-isomorphism`, and the
explicit exact-equivalence and signed-total extension in the blueprint
(auxiliary; not a blueprint node).

The comparison is specified by its action on every summand, together with
naturality, associativity, unit, and Koszul symmetry equations. The inverse
comparison is specified relative to the termwise equivalence's unit and counit.
The final clauses compare the acyclic and arbitrary-endpoint quasi-isomorphism
K-flat tests, without requiring exactness of countable coproducts.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe uM vM uA vA

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open ZeroObject

namespace CategoryTheory.Equivalence

variable {M : Type uM} {A : Type uA} [Category.{vM} M] [Category.{vA} A]
  [Abelian M] [Abelian A] [MonoidalCategory M] [MonoidalCategory A]
  [MonoidalPreadditive M] [MonoidalPreadditive A]
  [SymmetricCategory M] [SymmetricCategory A]
  [HasCountableCoproducts M] [HasCountableCoproducts A]
  [TensorPreservesCountableCoproducts M] [TensorPreservesCountableCoproducts A]

private noncomputable def tensorComparison (F : M ⥤ A) [F.Additive] [F.Monoidal]
    [F.IsEquivalence] (P Q : CochainComplex M ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
      (F.mapHomologicalComplex (.up ℤ)).obj P ⊗
        (F.mapHomologicalComplex (.up ℤ)).obj Q :=
  asIso (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q)

private noncomputable def unitComparison (F : M ⥤ A) [F.Additive] [F.Monoidal] :
    (F.mapHomologicalComplex (.up ℤ)).obj (𝟙_ (CochainComplex M ℤ)) ≅
      𝟙_ (CochainComplex A ℤ) :=
  (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app (𝟙_ M) ≪≫
    (HomologicalComplex.single A (.up ℤ) 0).mapIso (Functor.Monoidal.εIso F).symm

omit [SymmetricCategory M] [SymmetricCategory A] in
@[reassoc]
private theorem tensorComparison_ι (F : M ⥤ A) [F.Additive] [F.Monoidal]
    [F.IsEquivalence] (P Q : CochainComplex M ℤ) (p q n : ℤ) (h : p + q = n) :
    F.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
        (tensorComparison F P Q).hom.f n =
      Functor.OplaxMonoidal.δ F (P.X p) (Q.X q) ≫
        HomologicalComplex.ιTensorObj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q n h := by
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) P Q p q n h

omit [MonoidalCategory M] [MonoidalCategory A] [MonoidalPreadditive M]
  [MonoidalPreadditive A] [SymmetricCategory M] [SymmetricCategory A]
  [HasCountableCoproducts M] [HasCountableCoproducts A]
  [TensorPreservesCountableCoproducts M] [TensorPreservesCountableCoproducts A] in
private theorem acyclic_map_iff (F : M ⥤ A) [F.Additive] [F.IsEquivalence]
    (P : CochainComplex M ℤ) :
    P.Acyclic ↔ ((F.mapHomologicalComplex (.up ℤ)).obj P).Acyclic := by
  constructor
  · intro h n
    exact (P.sc n).exact_map_iff_of_faithful F |>.2 (h n)
  · intro h n
    exact (P.sc n).exact_map_iff_of_faithful F |>.1 (h n)

omit [SymmetricCategory M] [SymmetricCategory A] in
private theorem tensorComparison_naturality (F : M ⥤ A) [F.Additive] [F.Monoidal]
    [F.IsEquivalence] (P Q P' Q' : CochainComplex M ℤ) (a : P ⟶ P') (b : Q ⟶ Q') :
    (F.mapHomologicalComplex (.up ℤ)).map (a ⊗ₘ b) ≫
        (tensorComparison F P' Q').hom =
      (tensorComparison F P Q).hom ≫
        ((F.mapHomologicalComplex (.up ℤ)).map a ⊗ₘ
          (F.mapHomologicalComplex (.up ℤ)).map b) := by
  exact HomologicalComplex.mapBifunctorComparison_naturality
    (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) a b

omit [SymmetricCategory M] [SymmetricCategory A] in
private theorem unitComparison_zero (F : M ⥤ A) [F.Additive] [F.Monoidal] :
    F.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ M)).hom ≫
        (Functor.Monoidal.εIso F).inv =
      (unitComparison F).hom.f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ A)).hom := by
  simp [unitComparison, HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self]

omit [SymmetricCategory M] [SymmetricCategory A] in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorComparison_associativity (F : M ⥤ A) [F.Additive] [F.Monoidal]
    [F.IsEquivalence] (P Q R : CochainComplex M ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (α_ P Q R).hom ≫
        (tensorComparison F P (Q ⊗ R)).hom ≫
        (F.mapHomologicalComplex (.up ℤ)).obj P ◁ (tensorComparison F Q R).hom =
      (tensorComparison F (P ⊗ Q) R).hom ≫
        (tensorComparison F P Q).hom ▷ (F.mapHomologicalComplex (.up ℤ)).obj R ≫
        (α_ ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q)
          ((F.mapHomologicalComplex (.up ℤ)).obj R)).hom := by
  ext n
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map F
  intro s r hsr
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map (tensorRight (R.X r) ⋙ F)
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  change F.map (HomologicalComplex.ιTensorObj P Q p q s hpq ▷ R.X r) ≫ _ =
    F.map (HomologicalComplex.ιTensorObj P Q p q s hpq ▷ R.X r) ≫ _
  have ha : (HomologicalComplex.ιTensorObj P Q p q s hpq ▷ R.X r) ≫
      HomologicalComplex.ιTensorObj (P ⊗ Q) R s r n hsr ≫ (α_ P Q R).hom.f n =
      (α_ (P.X p) (Q.X q) (R.X r)).hom ≫
        (P.X p ◁ HomologicalComplex.ιTensorObj Q R q r (q + r) rfl) ≫
        HomologicalComplex.ιTensorObj P (Q ⊗ R) p (q + r) n
          (by change p + q = s at hpq; change s + r = n at hsr; omega) := by
    rw [← Category.assoc, ← CochainComplex.Monoidal.ι₁₂_eq P Q R p q r s n hpq hsr,
      CochainComplex.Monoidal.ι₁₂_associator_hom,
      CochainComplex.Monoidal.ι₂₃_eq P Q R p q r (q + r) n rfl]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, ha,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    tensorComparison_ι_assoc]
  erw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
  erw [CochainComplex.ιTensorObj_whiskerLeft_f,
    ← whiskerLeft_comp_assoc, tensorComparison_ι]
  erw [tensorComparison_ι_assoc, ← Functor.OplaxMonoidal.δ_natural_left_assoc,
    CochainComplex.Monoidal.ι_whiskerRight_assoc, ← comp_whiskerRight_assoc,
    tensorComparison_ι]
  simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  erw [← Category.assoc _ _ ((α_ ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q)
      ((F.mapHomologicalComplex (.up ℤ)).obj R)).hom.f n),
    ← CochainComplex.Monoidal.ι₁₂_eq
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q)
      ((F.mapHomologicalComplex (.up ℤ)).obj R) p q r s n hpq hsr,
    CochainComplex.Monoidal.ι₁₂_associator_hom,
    CochainComplex.Monoidal.ι₂₃_eq
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q)
      ((F.mapHomologicalComplex (.up ℤ)).obj R) p q r (q + r) n rfl]
  · rw [← Functor.OplaxMonoidal.associativity_assoc]
    rfl

omit [SymmetricCategory M] [SymmetricCategory A] in
private theorem unitComparison_inv_zero (F : M ⥤ A) [F.Additive] [F.Monoidal] :
    F.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ M)).inv ≫
        (unitComparison F).hom.f 0 =
      Functor.OplaxMonoidal.η F ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ A)).inv := by
  apply (cancel_mono (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ A)).hom).mp
  simp only [Category.assoc, ← unitComparison_zero, ← F.map_comp_assoc,
    Iso.inv_hom_id, F.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  rfl

omit [SymmetricCategory M] [SymmetricCategory A] in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorComparison_leftUnitor (F : M ⥤ A) [F.Additive] [F.Monoidal]
    [F.IsEquivalence] (P : CochainComplex M ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (λ_ P).hom =
      (tensorComparison F (𝟙_ (CochainComplex M ℤ)) P).hom ≫
        (unitComparison F).hom ▷ (F.mapHomologicalComplex (.up ℤ)).obj P ≫
        (λ_ ((F.mapHomologicalComplex (.up ℤ)).obj P)).hom := by
  apply (cancel_epi ((F.mapHomologicalComplex (.up ℤ)).map (λ_ P).inv)).mp
  ext n
  simp only [← Functor.map_comp, Iso.inv_hom_id, Functor.map_id,
    HomologicalComplex.comp_f, HomologicalComplex.id_f,
    Functor.mapHomologicalComplex_map_f]
  change 𝟙 _ = F.map ((HomologicalComplex.leftUnitor P).inv.f n) ≫ _
  rw [show (HomologicalComplex.leftUnitor P).inv.f n =
      (λ_ (P.X n)).inv ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ M)).inv ▷ P.X n ≫
        HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex M ℤ)) P 0 n n
          (zero_add n) from HomologicalComplex.leftUnitor'_inv P n]
  simp only [Functor.map_comp, Category.assoc]
  rw [tensorComparison_ι_assoc, CochainComplex.Monoidal.ι_whiskerRight_assoc]
  erw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
  erw [← comp_whiskerRight_assoc, unitComparison_inv_zero]
  simp only [comp_whiskerRight, Category.assoc]
  have hi :
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ A)).inv ▷ F.obj (P.X n) ≫
        HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex A ℤ))
          ((F.mapHomologicalComplex (.up ℤ)).obj P) 0 n n (zero_add n) =
      (λ_ (F.obj (P.X n))).hom ≫
        (λ_ ((F.mapHomologicalComplex (.up ℤ)).obj P)).inv.f n := by
    change _ = (λ_ (F.obj (P.X n))).hom ≫
      (HomologicalComplex.leftUnitor ((F.mapHomologicalComplex (.up ℤ)).obj P)).inv.f n
    rw [show (HomologicalComplex.leftUnitor
        ((F.mapHomologicalComplex (.up ℤ)).obj P)).inv.f n = _ from
      HomologicalComplex.leftUnitor'_inv ((F.mapHomologicalComplex (.up ℤ)).obj P) n]
    erw [Iso.hom_inv_id_assoc]
    rfl
  rw [← Category.assoc _ _ ((λ_ ((F.mapHomologicalComplex (.up ℤ)).obj P)).hom.f n), hi]
  simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    HomologicalComplex.id_f]
  change 𝟙 _ = F.map (λ_ (P.X n)).inv ≫
    Functor.OplaxMonoidal.δ F (𝟙_ M) (P.X n) ≫
      Functor.OplaxMonoidal.η F ▷ F.obj (P.X n) ≫ (λ_ (F.obj (P.X n))).hom ≫ 𝟙 _
  rw [Category.comp_id, Functor.OplaxMonoidal.left_unitality_hom,
    ← F.map_comp, Iso.inv_hom_id, F.map_id]

omit [SymmetricCategory M] [SymmetricCategory A] in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorComparison_rightUnitor (F : M ⥤ A) [F.Additive] [F.Monoidal]
    [F.IsEquivalence] (P : CochainComplex M ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (ρ_ P).hom =
      (tensorComparison F P (𝟙_ (CochainComplex M ℤ))).hom ≫
        (F.mapHomologicalComplex (.up ℤ)).obj P ◁ (unitComparison F).hom ≫
        (ρ_ ((F.mapHomologicalComplex (.up ℤ)).obj P)).hom := by
  apply (cancel_epi ((F.mapHomologicalComplex (.up ℤ)).map (ρ_ P).inv)).mp
  ext n
  simp only [← Functor.map_comp, Iso.inv_hom_id, Functor.map_id,
    HomologicalComplex.comp_f, HomologicalComplex.id_f,
    Functor.mapHomologicalComplex_map_f]
  change 𝟙 _ = F.map ((HomologicalComplex.rightUnitor P).inv.f n) ≫ _
  rw [show (HomologicalComplex.rightUnitor P).inv.f n =
      (ρ_ (P.X n)).inv ≫
        P.X n ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ M)).inv ≫
        HomologicalComplex.ιTensorObj P (𝟙_ (CochainComplex M ℤ)) n 0 n
          (add_zero n) from HomologicalComplex.rightUnitor'_inv P n]
  simp only [Functor.map_comp, Category.assoc]
  rw [tensorComparison_ι_assoc]
  erw [CochainComplex.ιTensorObj_whiskerLeft_f_assoc,
    ← Functor.OplaxMonoidal.δ_natural_right_assoc]
  erw [← whiskerLeft_comp_assoc, unitComparison_inv_zero]
  simp only [whiskerLeft_comp, Category.assoc]
  have hi :
      F.obj (P.X n) ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ A)).inv ≫
        HomologicalComplex.ιTensorObj ((F.mapHomologicalComplex (.up ℤ)).obj P)
          (𝟙_ (CochainComplex A ℤ)) n 0 n (add_zero n) =
      (ρ_ (F.obj (P.X n))).hom ≫
        (ρ_ ((F.mapHomologicalComplex (.up ℤ)).obj P)).inv.f n := by
    change _ = (ρ_ (F.obj (P.X n))).hom ≫
      (HomologicalComplex.rightUnitor ((F.mapHomologicalComplex (.up ℤ)).obj P)).inv.f n
    rw [show (HomologicalComplex.rightUnitor
        ((F.mapHomologicalComplex (.up ℤ)).obj P)).inv.f n = _ from
      HomologicalComplex.rightUnitor'_inv ((F.mapHomologicalComplex (.up ℤ)).obj P) n]
    erw [Iso.hom_inv_id_assoc]
    rfl
  rw [← Category.assoc _ _ ((ρ_ ((F.mapHomologicalComplex (.up ℤ)).obj P)).hom.f n), hi]
  simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    HomologicalComplex.id_f]
  change 𝟙 _ = F.map (ρ_ (P.X n)).inv ≫
    Functor.OplaxMonoidal.δ F (P.X n) (𝟙_ M) ≫
      F.obj (P.X n) ◁ Functor.OplaxMonoidal.η F ≫ (ρ_ (F.obj (P.X n))).hom ≫ 𝟙 _
  rw [Category.comp_id, Functor.OplaxMonoidal.right_unitality_hom,
    ← F.map_comp, Iso.inv_hom_id, F.map_id]

private theorem acyclic_of_iso {C : Type*} [Category C] [Abelian C]
    {P Q : CochainComplex C ℤ} (e : P ≅ Q) (h : P.Acyclic) : Q.Acyclic :=
  fun n ↦ (h n).of_iso e

omit [SymmetricCategory M] [SymmetricCategory A] in
private theorem acyclic_tensor_map_iff (E : M ≌ A)
    [E.functor.Additive] [E.inverse.Additive] [E.functor.Monoidal]
    (P : CochainComplex M ℤ) :
    (∀ N : CochainComplex M ℤ, N.Acyclic → (P ⊗ N).Acyclic) ↔
      (∀ N : CochainComplex A ℤ, N.Acyclic →
        ((E.functor.mapHomologicalComplex (.up ℤ)).obj P ⊗ N).Acyclic) := by
  let F := E.functor.mapHomologicalComplex (.up ℤ)
  let G := E.inverse.mapHomologicalComplex (.up ℤ)
  constructor
  · intro h N hN
    have hG := (acyclic_map_iff E.inverse N).mp hN
    have hF := (acyclic_map_iff E.functor (P ⊗ G.obj N)).mp (h _ hG)
    exact acyclic_of_iso (tensorComparison E.functor P (G.obj N) ≪≫
      (tensorLeft (F.obj P)).mapIso ((E.mapHomologicalComplex (.up ℤ)).counitIso.app N)) hF
  · intro h N hN
    have hF := h (F.obj N) ((acyclic_map_iff E.functor N).mp hN)
    exact (acyclic_map_iff E.functor (P ⊗ N)).mpr
      (acyclic_of_iso (tensorComparison E.functor P N).symm hF)

private theorem acyclic_tensor_swap (P : CochainComplex M ℤ) :
    (∀ N : CochainComplex M ℤ, N.Acyclic → (P ⊗ N).Acyclic) ↔
      (∀ N : CochainComplex M ℤ, N.Acyclic → (N ⊗ P).Acyclic) := by
  constructor <;> intro h N hN
  · exact acyclic_of_iso (CochainComplex.Monoidal.braiding P N) (h N hN)
  · exact acyclic_of_iso (CochainComplex.Monoidal.braiding N P) (h N hN)

private theorem acyclic_tensor_iff_kFlat (P : CochainComplex M ℤ) :
    (∀ N : CochainComplex M ℤ, N.Acyclic → (P ⊗ N).Acyclic) ↔
      (HomologicalComplex.quasiIso M (.up ℤ)).kFlat P := by
  constructor
  · intro h
    have hleft : ∀ {X Y : CochainComplex M ℤ} (s : X ⟶ Y), QuasiIso s →
        QuasiIso (HomologicalComplex.tensorHom (𝟙 P) s) := by
      intro X Y s hs
      let := HasDerivedCategory.standard M
      obtain ⟨φ, _⟩ := CochainComplex.exists_totalTensorConeComparison M
      apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).mpr
      exact acyclic_of_iso (φ P X Y s)
        (h _ ((CochainComplex.mappingCone.quasiIso_iff_acyclic s).mp hs))
    refine ⟨fun _ _ s hs ↦ hleft s hs, ?_⟩
    intro X Y s hs
    change QuasiIso (HomologicalComplex.tensorHom s (𝟙 P))
    have := hleft s hs
    have he : HomologicalComplex.tensorHom s (𝟙 P) =
        (CochainComplex.Monoidal.braiding P X).inv ≫
          HomologicalComplex.tensorHom (𝟙 P) s ≫
          (CochainComplex.Monoidal.braiding P Y).hom := by
      change s ▷ P = (CochainComplex.Monoidal.braiding P X).inv ≫ P ◁ s ≫
        (CochainComplex.Monoidal.braiding P Y).hom
      rw [CochainComplex.Monoidal.braiding_naturality_right,
        Iso.inv_hom_id_assoc]
    rw [he]
    infer_instance
  · intro h N hN
    let Z : CochainComplex M ℤ := 0
    have hZ : Z.Acyclic := HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)
    have hs : QuasiIso (0 : Z ⟶ N) := by
      rw [quasiIso_iff]
      intro n
      exact (quasiIsoAt_iff_exactAt _ n (hZ n)).mpr (hN n)
    have ht : QuasiIso (HomologicalComplex.tensorHom (𝟙 P) (0 : Z ⟶ N)) := h.1 _ hs
    have hz : (P ⊗ Z).Acyclic := by
      have : (tensorLeft P).Additive :=
        inferInstanceAs (((curriedTensor M).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ)).obj P).Additive
      exact HomologicalComplex.acyclic_of_isZero _
        ((tensorLeft P).map_isZero (isZero_zero _))
    intro n
    have : QuasiIsoAt
        (HomologicalComplex.tensorHom (𝟙 P) (0 : Z ⟶ N)) n :=
      (quasiIso_iff _).mp ht n
    exact (quasiIsoAt_iff_exactAt _ n (hz n)).mp this

omit [SymmetricCategory M] [SymmetricCategory A] in
@[instance_reducible]
private noncomputable def complexOplax (F : M ⥤ A) [F.Additive] [F.Monoidal]
    [F.IsEquivalence] : (F.mapHomologicalComplex (.up ℤ)).OplaxMonoidal where
  η := (unitComparison F).hom
  δ P Q := (tensorComparison F P Q).hom
  δ_natural_left f Q := by
    simpa using (tensorComparison_naturality F _ Q _ Q f (𝟙 Q)).symm
  δ_natural_right P g := by
    simpa using (tensorComparison_naturality F P _ P _ (𝟙 P) g).symm
  oplax_associativity P Q R := (tensorComparison_associativity F P Q R).symm
  oplax_left_unitality P := by
    apply (cancel_epi ((F.mapHomologicalComplex (.up ℤ)).map (λ_ P).hom)).mp
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp]
    rw [tensorComparison_leftUnitor]
    simp
  oplax_right_unitality P := by
    apply (cancel_epi ((F.mapHomologicalComplex (.up ℤ)).map (ρ_ P).hom)).mp
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp]
    rw [tensorComparison_rightUnitor]
    simp

omit [SymmetricCategory M] [SymmetricCategory A] in
@[instance_reducible]
private noncomputable def complexMonoidal (F : M ⥤ A) [F.Additive] [F.Monoidal]
    [F.IsEquivalence] : (F.mapHomologicalComplex (.up ℤ)).Monoidal := by
  letI := complexOplax F
  have : IsIso (Functor.OplaxMonoidal.η (F.mapHomologicalComplex (.up ℤ))) :=
    inferInstanceAs (IsIso (unitComparison F).hom)
  have (P Q : CochainComplex M ℤ) :
      IsIso (Functor.OplaxMonoidal.δ (F.mapHomologicalComplex (.up ℤ)) P Q) :=
    inferInstanceAs (IsIso (tensorComparison F P Q).hom)
  exact Functor.Monoidal.ofOplaxMonoidal _

end CategoryTheory.Equivalence
