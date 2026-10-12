/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Exact functors preserve acyclicity

An exact functor between abelian categories preserves acyclicity of homological
complexes (`HomologicalComplex.Acyclic.map`).

If a homological complex `K` is exact at `j`, then `K.toCycles i j` is an epimorphism
(`HomologicalComplex.ExactAt.epi_toCycles`).

A natural endomorphism of the identity functor induces itself on homology
(`HomologicalComplex.homologyMap_eq_app_homology`).

For a projective object `P`, there are no nonzero morphisms `P ⟶ H_j(K)` if and only if every
cycle `P ⟶ K_j` is a boundary (`HomologicalComplex.subsingleton_hom_homology_iff_of_projective`).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]

/-- An exact functor preserves acyclicity of homological complexes. -/
lemma HomologicalComplex.Acyclic.map {ι : Type*} {c : ComplexShape ι}
    {M : HomologicalComplex C c} (hM : M.Acyclic) (F : C ⥤ D) [F.Additive]
    [F.PreservesHomology] :
    ((F.mapHomologicalComplex c).obj M).Acyclic :=
  fun i => ShortComplex.Exact.map (hM i) F

end CategoryTheory

namespace HomologicalComplex

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  {K : HomologicalComplex C c}

/-- If `K` is exact at `j`, then `K.toCycles i j : K.X i ⟶ K.cycles j` is an epimorphism. -/
lemma ExactAt.epi_toCycles {j : ι} (hj : K.ExactAt j) (i : ι) (hi : c.prev j = i) :
    Epi (K.toCycles i j) := by
  subst hi
  exact (K.sc j).exact_iff_epi_toCycles.1 hj

variable (K) in
/-- The short complex `K.cycles i ⟶ K.X i ⟶ K.cycles j`. -/
@[simps]
noncomputable def cyclesShortComplex (i j : ι) : ShortComplex C :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i j) (by
    rw [← cancel_mono (K.iCycles j), Category.assoc, toCycles_i, iCycles_d, zero_comp])

/-- A natural endomorphism `β` of the identity functor, applied termwise to a complex `K`, induces
`β` on the homology of `K`. -/
lemma homologyMap_eq_app_homology (β : 𝟭 C ⟶ 𝟭 C) {K : HomologicalComplex C c} (φ : K ⟶ K)
    (hφ : ∀ i, φ.f i = β.app (K.X i)) (i : ι) :
    homologyMap φ i = β.app (K.homology i) := by
  have hc : cyclesMap φ i = β.app (K.cycles i) := by
    rw [← cancel_mono (K.iCycles i), cyclesMap_i, hφ]
    exact β.naturality (K.iCycles i)
  rw [← cancel_epi (K.homologyπ i), homologyπ_naturality, hc]
  exact (β.naturality (K.homologyπ i)).symm

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
