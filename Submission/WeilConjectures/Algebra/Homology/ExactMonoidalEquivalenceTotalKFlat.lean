/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Submission.WeilConjectures.Algebra.Homology.CountableTensorStructures
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

import Submission.WeilConjectures.Algebra.Homology.AdditiveTotalTensorConeComparison
import Submission.WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Functor
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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

end CategoryTheory.Equivalence
