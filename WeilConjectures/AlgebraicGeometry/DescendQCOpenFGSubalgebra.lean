/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.DescendedQCNeighborhood

/-!
# Descent of quasi-compact opens to finitely generated subalgebras

## References

* Stacks Project, Tag 0388
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private noncomputable def subalgebraOverProjection
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] (B : Subalgebra k A) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Subalgebra.val B).toRingHom)) (by
    dsimp only [Over.mk_hom]
    rw [← Spec.map_comp]
    rfl)

private noncomputable def subalgebraOverTransition
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {B C : Subalgebra k A} (h : B ≤ C) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k C))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)) (by
    dsimp only [Over.mk_hom]
    rw [← Spec.map_comp]
    rfl)

private noncomputable def subalgebraProjection
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (B : Subalgebra k A) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
  baseChangeMap f (subalgebraOverProjection B)

private noncomputable def subalgebraTransition
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    {B C : Subalgebra k A} (h : B ≤ C) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k C))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
  baseChangeMap f (subalgebraOverTransition h)

private theorem subalgebraProjection_transition
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    {B C : Subalgebra k A} (h : B ≤ C) :
    subalgebraProjection f C ≫ subalgebraTransition f h = subalgebraProjection f B := by
  have hc : subalgebraOverProjection C ≫ subalgebraOverTransition h =
      subalgebraOverProjection B := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (Subalgebra.val C).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom) =
      Spec.map (CommRingCat.ofHom (Subalgebra.val B).toRingHom)
    rw [← Spec.map_comp]
    rfl
  change baseChangeMap f _ ≫ baseChangeMap f _ = baseChangeMap f _
  rw [← baseChangeMap_comp, hc]

private theorem subalgebraTransition_quasiCompact
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    {B C : Subalgebra k A} (h : B ≤ C) : QuasiCompact (subalgebraTransition f h) := by
  apply MorphismProperty.of_isPullback (P := @QuasiCompact)
    (isPullback_baseChangeMap f (subalgebraOverTransition h)).flip
  change QuasiCompact (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom))
  infer_instance

/-- A quasi-compact open in a base change to an algebra descends to a finitely generated
subalgebra (Stacks, Tag 0388). -/
theorem descend_qc_open_fg_subalgebra (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (A : Type u) [CommRing A] [Algebra k A] :
    ∀ (V : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Opens),
      IsCompact V.1 →
      ∃ (A' : Subalgebra k A), A'.FG ∧
        ∃ (V' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A')))).Opens),
          IsCompact V'.1 ∧
          ∃ (π : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))) ⟶
              (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A')))) ),
            π = baseChangeMap f
              (Over.homMk (Spec.map (CommRingCat.ofHom (Subalgebra.val A')))
                (by
                  change Spec.map (CommRingCat.ofHom (Subalgebra.val A')) ≫
                      Spec.map (CommRingCat.ofHom (algebraMap k A')) =
                    Spec.map (CommRingCat.ofHom (algebraMap k A))
                  rw [← Spec.map_comp]
                  congr 1
                  ) :
                  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
                    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A')))) ∧
            V = (π ⁻¹ᵁ V')  := by
  classical
  intro V hV
  let Y := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  let P : Y.Opens → Prop := fun U ↦
    ∃ (B : Subalgebra k A), B.FG ∧
      ∃ (W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).Opens),
        IsCompact W.1 ∧ U = subalgebraProjection f B ⁻¹ᵁ W
  have hbot : P ⊥ := by
    exact ⟨⊥, Subalgebra.fg_bot, ⊥, isCompact_empty, rfl⟩
  -- Enlarge both coefficient algebras to their finitely generated supremum.
  have hsup : ∀ U T, P U → P T → P (U ⊔ T) := by
    rintro U T ⟨B, hB, W, hW, rfl⟩ ⟨C, hC, Z, hZ, rfl⟩
    have h₁ : QuasiCompact (subalgebraTransition f (le_sup_left : B ≤ B ⊔ C)) :=
      subalgebraTransition_quasiCompact f _
    have h₂ : QuasiCompact (subalgebraTransition f (le_sup_right : C ≤ B ⊔ C)) :=
      subalgebraTransition_quasiCompact f _
    refine ⟨B ⊔ C, hB.sup hC,
      (subalgebraTransition f le_sup_left ⁻¹ᵁ W) ⊔
        (subalgebraTransition f le_sup_right ⁻¹ᵁ Z),
      (Scheme.Hom.isCompact_preimage _ hW).union
        (Scheme.Hom.isCompact_preimage _ hZ), ?_⟩
    rw [Scheme.Hom.preimage_sup, ← Scheme.Hom.comp_preimage,
      ← Scheme.Hom.comp_preimage, subalgebraProjection_transition,
      subalgebraProjection_transition]
  -- The local lemma uses no compactness or quasi-separatedness hypothesis.
  have hlocal : ∀ x : V, ∃ U : Y.Opens, P U ∧ x.1 ∈ U ∧ U ≤ V := by
    intro x
    obtain ⟨B, hB, W, hW, hx, hle⟩ :=
      exists_descended_qc_neighborhood k X f A V x.1 x.2
    exact ⟨_, ⟨B, hB, W, hW, rfl⟩, hx, hle⟩
  choose U hU hxU hUV using hlocal
  -- Only here do we use compactness of V to select finitely many neighborhoods.
  obtain ⟨s, hs⟩ := hV.elim_finite_subcover (fun x : V ↦ (U x).1)
    (fun x ↦ (U x).isOpen) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  have hfin : ∀ t : Finset V, P (t.sup U) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using hbot
    | @insert x t hxt ih =>
      rw [Finset.sup_insert]
      exact hsup _ _ (hU x) ih
  have hcover : s.sup U = V := by
    apply le_antisymm
    · exact Finset.sup_le fun x _ ↦ hUV x
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
      exact (Finset.le_sup (f := U) hi : U i ≤ s.sup U) hxi
  obtain ⟨B, hB, W, hW, hEq⟩ := hcover ▸ hfin s
  exact ⟨B, hB, W, hW, subalgebraProjection f B, rfl, hEq⟩

end AlgebraicGeometry
