/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.Paper.ModuleCupHomologyRepresentability
public import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-! # The normalized ordinary tensor of two shifted free modules

Source: Stacks Project, Tag 068G, the tensor-of-cocycles construction.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable (k : Type u) [CommRing k]

private lemma tensor_term_zero (p q a b : ℤ) (h : a ≠ p ∨ b ≠ q) :
    IsZero ((cupSingleModule k p).X a ⊗ (cupSingleModule k q).X b) := by
  rcases h with h | h
  · exact (tensorRight _).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)
  · exact (tensorLeft _).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)

private lemma tensor_support_zero (p q n : ℤ) (h : n ≠ p + q) :
    IsZero ((cupSingleModule k p ⊗ cupSingleModule k q).X n) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  apply (tensor_term_zero k p q a b ?_).eq_of_src
  by_cases ha : a = p
  · right
    intro hb
    subst a
    subst b
    exact h hab.symm
  · exact Or.inl ha

private def tensor_support_iso (p q : ℤ) :
    (cupSingleModule k p).X p ⊗ (cupSingleModule k q).X q ≅
      (cupSingleModule k p ⊗ cupSingleModule k q).X (p + q) where
  hom := HomologicalComplex.ιTensorObj _ _ p q (p + q) rfl
  inv := HomologicalComplex.mapBifunctorDesc (fun a b _ ↦
    if h : a = p ∧ b = q then
      (HomologicalComplex.XIsoOfEq _ h.1).hom ⊗ₘ
        (HomologicalComplex.XIsoOfEq _ h.2).hom
    else 0)
  hom_inv_id := by
    erw [HomologicalComplex.ι_mapBifunctorDesc]
    simp
  inv_hom_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b hab
    by_cases ha : a = p
    · subst a
      have hb : b = q := by change p + b = p + q at hab; omega
      subst b
      erw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
      simp
      rfl
    · apply (tensor_term_zero k p q a b (Or.inl ha)).eq_of_src

/-- A normalized ordinary tensor isomorphism of shifted free rank-one complexes.
Source: Stacks Project, Tag 068G, equation-simple-tor-product.
(blueprint: lem-sc-module-cup-shifted-unit-chain-tensor)
Proof: both single complexes have zero terms outside their named degrees. Hence their
ordinary total tensor has a unique nonzero summand, in degree p+q. On that summand use
multiplication k tensor k to k, whose inverse sends 1 to 1 tensor 1. All differentials
are zero; these degreewise maps therefore define inverse chain maps. Under the
singleObjXSelf identifications, inverse multiplication followed by the (p,q) summand
inclusion sends 1 to 1 tensor 1, giving the displayed equality. No interchange of
shifts occurs, so there is no sign. Negative p,q, p=0, q=0 and the zero ring are
included: the single support degree and multiplication isomorphism work in each case. -/
theorem exists_cupShiftedUnitChainTensor (p q : ℤ) :
    ∃ i : cupSingleModule k (p + q) ≅
      cupSingleModule k p ⊗ cupSingleModule k q,
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (p + q)
          (ModuleCat.of k k)).inv ≫ i.hom.f (p + q)) (1 : k) =
        (HomologicalComplex.ιTensorObj (cupSingleModule k p) (cupSingleModule k q)
          p q (p + q) rfl)
          (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p
              (ModuleCat.of k k)).inv (1 : k)) ⊗ₜ[k]
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q
              (ModuleCat.of k k)).inv (1 : k))) := by
  let S := cupSingleModule k (p + q)
  let T := cupSingleModule k p ⊗ cupSingleModule k q
  let e : ModuleCat.of k k ≅ T.X (p + q) :=
    (λ_ (ModuleCat.of k k)).symm ≪≫
      tensorIso (HomologicalComplex.singleObjXSelf (.up ℤ) p (ModuleCat.of k k)).symm
        (HomologicalComplex.singleObjXSelf (.up ℤ) q (ModuleCat.of k k)).symm ≪≫
      tensor_support_iso k p q
  have hz (n : ℤ) (hn : n ≠ p + q) : IsZero (T.X n) :=
    tensor_support_zero k p q n hn
  let f : S ⟶ T := HomologicalComplex.mkHomFromSingle e.hom (by
    intro n hn
    apply (hz n (by change p + q + 1 = n at hn; omega)).eq_of_tgt)
  have hf (n : ℤ) : IsIso (f.f n) := by
    by_cases hn : n = p + q
    · subst n
      dsimp only [f]
      rw [HomologicalComplex.mkHomFromSingle_f]
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) (p + q)
        (ModuleCat.of k k) n hn).isIso (hz n hn) _
  let : ∀ n, IsIso (f.f n) := hf
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  refine ⟨asIso f, ?_⟩
  dsimp only [asIso_hom, f]
  rw [HomologicalComplex.mkHomFromSingle_f, Iso.inv_hom_id_assoc]
  dsimp only [e, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, tensor_support_iso]
  simp only [ConcreteCategory.comp_apply]
  congr 1

end
end AlgebraicGeometry.Scheme.Modules
