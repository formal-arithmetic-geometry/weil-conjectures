/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# Morphisms out of a projective object in the derived category

For a projective object `P` of an abelian category `C` and `K` in the derived category, the
morphisms `P[0] ⟶ K[n]` are the morphisms `P ⟶ H^n(K)`. We record the consequence that one of
these groups vanishes if and only if the other does
(`DerivedCategory.subsingleton_singleFunctor_hom_shift_iff_of_projective`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*} {c : ComplexShape ι}

/-- For a projective object `P`, there are no nonzero morphisms `P ⟶ H_j(K)` if and only if
every morphism `P ⟶ K_j` killed by the differential factors through the incoming
differential. -/
lemma subsingleton_hom_homology_iff_of_projective (K : HomologicalComplex C c) {i j k : ι}
    (hi : c.prev j = i) (hk : c.next j = k) (P : C) [Projective P] :
    Subsingleton (P ⟶ K.homology j) ↔
      ∀ f : P ⟶ K.X j, f ≫ K.d j k = 0 → ∃ g : P ⟶ K.X i, g ≫ K.d i j = f := by
  have hT : (ShortComplex.mk (K.toCycles i j) (K.homologyπ j) (by simp)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel i j hi)
  refine ⟨fun h f hf ↦ ?_, fun h ↦ ⟨fun φ ψ ↦ ?_⟩⟩
  · refine ⟨hT.liftFromProjective (K.liftCycles f k hk hf) (Subsingleton.elim _ _), ?_⟩
    rw [← K.toCycles_i, ← Category.assoc]
    erw [hT.liftFromProjective_comp]
    exact K.liftCycles_i f k hk hf
  · suffices H : ∀ φ : P ⟶ K.homology j, φ = 0 by rw [H φ, H ψ]
    intro φ
    obtain ⟨g, hg⟩ := h (Projective.factorThru φ (K.homologyπ j) ≫ K.iCycles j)
      (by rw [Category.assoc, K.iCycles_d, comp_zero])
    have : Projective.factorThru φ (K.homologyπ j) = K.liftCycles
        (Projective.factorThru φ (K.homologyπ j) ≫ K.iCycles j) k hk
          (by rw [Category.assoc, K.iCycles_d, comp_zero]) := by
      rw [← cancel_mono (K.iCycles j), liftCycles_i]
    rw [← Projective.factorThru_comp φ (K.homologyπ j), this]
    exact K.liftCycles_homologyπ_eq_zero_of_boundary _ k hk g hg.symm

end HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A projective object placed in a single degree is a K-projective complex. -/
instance isKProjective_singleFunctor_obj (P : C) [Projective P] (n : ℤ) :
    ((singleFunctor C n).obj P).IsKProjective := by
  have (m : ℤ) : Projective (((singleFunctor C n).obj P).X m) := by
    by_cases hm : m = n
    · subst hm
      exact Projective.of_iso (HomologicalComplex.singleObjXSelf (.up ℤ) m P).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hm).projective
  exact isKProjective_of_projective _ n

open HomComplex in
/-- For a projective object `P`, the cohomology classes of degree `n` from `P[0]` to `L` vanish
if and only if every morphism `P ⟶ L^n` killed by the differential factors through the
differential `L^{n-1} ⟶ L^n`. -/
lemma subsingleton_cohomologyClass_singleFunctor_iff (P : C) (L : CochainComplex C ℤ) (n : ℤ) :
    Subsingleton (CohomologyClass ((singleFunctor C 0).obj P) L n) ↔
      ∀ f : P ⟶ L.X n, f ≫ L.d n (n + 1) = 0 → ∃ g : P ⟶ L.X (n - 1), g ≫ L.d (n - 1) n = f := by
  refine ⟨fun h f hf ↦ ?_, fun h ↦ ⟨fun a b ↦ ?_⟩⟩
  · refine (Cocycle.fromSingleMk_mem_coboundaries_iff f (zero_add n) (n + 1) rfl hf (n - 1)
      (by lia)).1 ?_
    rw [← CohomologyClass.mk_eq_zero_iff]
    exact Subsingleton.elim _ _
  · suffices H : ∀ a : CohomologyClass ((singleFunctor C 0).obj P) L n, a = 0 by rw [H a, H b]
    intro a
    obtain ⟨x, rfl⟩ := a.mk_surjective
    obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective x n (zero_add n) (n + 1) rfl
    rw [CohomologyClass.mk_eq_zero_iff, Cocycle.fromSingleMk_mem_coboundaries_iff f (zero_add n)
      (n + 1) rfl hf (n - 1) (by lia)]
    exact h f hf

end CochainComplex

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- For a projective object `P` and `K` in the derived category, there are no nonzero
morphisms `P[0] ⟶ K[n]` if and only if there are no nonzero morphisms `P ⟶ H^n(K)`: the
single complex `P[0]` is K-projective, so the former are the cohomology classes of degree `n`
from `P[0]` to a representative of `K`. -/
lemma subsingleton_singleFunctor_hom_shift_iff_of_projective (P : C) [Projective P]
    (K : DerivedCategory C) (n : ℤ) :
    Subsingleton ((singleFunctor C 0).obj P ⟶ K⟦n⟧) ↔
      Subsingleton (P ⟶ (homologyFunctor C n).obj K) := by
  obtain ⟨L, ⟨e⟩⟩ : ∃ L : CochainComplex C ℤ, Nonempty (Q.obj L ≅ K) :=
    ⟨_, ⟨Q.objObjPreimageIso K⟩⟩
  let S := (CochainComplex.singleFunctor C 0).obj P
  let e₁ : ((singleFunctor C 0).obj P ⟶ K⟦n⟧) ≃
      ((HomotopyCategory.quotient C _).obj S ⟶ (HomotopyCategory.quotient C _).obj (L⟦n⟧)) :=
    (Iso.homCongr ((singleFunctorIsoCompQ C 0).app P ≪≫ (quotientCompQhIso C).symm.app S)
      ((shiftFunctor _ n).mapIso e.symm ≪≫ (Q.commShiftIso n).symm.app L ≪≫
        (quotientCompQhIso C).symm.app _)).trans
      (Equiv.ofBijective _ (CochainComplex.IsKProjective.Qh_map_bijective S _)).symm
  rw [(e₁.trans
      (CochainComplex.HomComplex.CohomologyClass.homAddEquiv (K := S) (L := L)
        (n := n)).toEquiv.symm).subsingleton_congr,
    (Iso.homCongr (Iso.refl P) ((homologyFunctor C n).mapIso e.symm ≪≫
      (homologyFunctorFactors C n).app L)).subsingleton_congr]
  exact (CochainComplex.subsingleton_cohomologyClass_singleFunctor_iff P L n).trans
    (L.subsingleton_hom_homology_iff_of_projective (i := n - 1) (j := n) (k := n + 1)
      (by simp) (by simp) P).symm

end DerivedCategory
