/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorBundleLocallyLinear
public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheafBundle

/-!
# The fibrewise linear functions of a linear atlas do not depend on the chart

Local linearity pulls back along morphisms over a base map
(`AlgebraicGeometry.Scheme.Hom.IsLocallyLinear.pullback`). Transporting the relation `linear j i`
of a linear atlas across the symmetry `Vⱼ ×_Z Vᵢ ≅ Vᵢ ×_Z Vⱼ`, the coordinates of the chart `i` are
locally linear in those of the chart `j` over the overlap; hence the locally linear functions for
the two charts contain each other's coordinate spans
(`AlgebraicGeometry.Scheme.Hom.VectorBundleAtlas.span_chart_coord_le_locallyLinear_and_symm`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {c : ℕ}

/-- Local linearity pulls back along `F : T ⟶ N` lying over `g : P ⟶ Y`. -/
lemma IsLocallyLinear.pullback {T N P Y : Scheme.{u}} (F : T ⟶ N) (q : T ⟶ P) (g : P ⟶ Y)
    (t : N ⟶ Y) (hF : F ≫ t = q ≫ g) {σ : Fin c → Γ(N, ⊤)} {s : Γ(N, ⊤)}
    (hs : IsLocallyLinear t σ s) :
    IsLocallyLinear q (fun l ↦ F.appTop (σ l)) (F.appTop s) := by
  intro y
  obtain ⟨W, hy, β, h⟩ := hs (g y)
  refine ⟨g ⁻¹ᵁ W, hy, fun l ↦ g.app W (β l), ?_⟩
  have hT : F.appTop = F.appLE ⊤ ⊤ (by simp) := by simp [Scheme.Hom.appLE]
  simp only [hT]
  exact Scheme.Modules.appLE_relation' F q g t hF W le_top le_top σ s β h _ _

namespace VectorBundleAtlas

variable {E Z : Scheme.{u}} {p : E ⟶ Z} {z : Z ⟶ E}

/-- The swap `E ×_Z (Vᵢ ×_Z Vⱼ) ⟶ E ×_Z (Vⱼ ×_Z Vᵢ)`. -/
noncomputable def overlapSwap (A : VectorBundleAtlas c p z) (i j : A.ι) :
    pullback p (pullback.fst (A.v i) (A.v j) ≫ A.v i) ⟶
      pullback p (pullback.fst (A.v j) (A.v i) ≫ A.v j) :=
  pullback.map _ _ _ _ (𝟙 E) (pullbackSymmetry (A.v i) (A.v j)).hom (𝟙 Z) (by simp)
    (by simp [pullback.condition])

lemma overlapSwap_appTop_overlapCoordSnd (A : VectorBundleAtlas c p z) (i j : A.ι) (l : Fin c) :
    (A.overlapSwap i j).appTop (A.overlapCoordSnd j i l) = A.overlapCoordFst i j l := by
  rw [overlapCoordSnd, overlapCoordFst, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  congr 2
  exact congrArg Scheme.Hom.appTop
    (pullback.hom_ext (by simp [overlapSwap]) (by simp [overlapSwap]))

lemma overlapSwap_appTop_overlapCoordFst (A : VectorBundleAtlas c p z) (i j : A.ι) (k : Fin c) :
    (A.overlapSwap i j).appTop (A.overlapCoordFst j i k) = A.overlapCoordSnd i j k := by
  rw [overlapCoordSnd, overlapCoordFst, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  congr 2
  exact congrArg Scheme.Hom.appTop
    (pullback.hom_ext (by simp [overlapSwap]) (by simp [overlapSwap]))

/-- Over the overlap `Vᵢ ×_Z Vⱼ`, the coordinates of the chart `i` are locally linear in those of
the chart `j`. -/
lemma isLocallyLinear_overlapCoordFst (A : VectorBundleAtlas c p z) (i j : A.ι) (l : Fin c) :
    IsLocallyLinear (pullback.snd p (pullback.fst (A.v i) (A.v j) ≫ A.v i))
      (A.overlapCoordSnd i j) (A.overlapCoordFst i j l) := by
  have h := (A.isLocallyLinear_overlapCoordSnd j i l).pullback (A.overlapSwap i j)
    (pullback.snd p (pullback.fst (A.v i) (A.v j) ≫ A.v i)) (pullbackSymmetry (A.v i) (A.v j)).hom
    _ (by simp [overlapSwap])
  simp only [overlapSwap_appTop_overlapCoordSnd, overlapSwap_appTop_overlapCoordFst] at h
  exact h

/-- Blueprint `def-pur-vector-bundle-zero-section`: Vector bundle with zero section

**The fibrewise linear functions do not depend on the chart.** Over `Vᵢ ×_Z Vⱼ`, the span of the
coordinates of the chart `i` consists of functions locally linear in the coordinates of the
chart `j`, and conversely. -/
theorem span_chart_coord_le_locallyLinear_and_symm (A : VectorBundleAtlas c p z) (i j : A.ι) :
    letI := (pullback.snd p (pullback.fst (A.v i) (A.v j) ≫ A.v i)).appTop.hom.toAlgebra
    Submodule.span Γ(pullback (A.v i) (A.v j), ⊤) (Set.range (A.overlapCoordSnd i j)) ≤
        locallyLinearSubmodule (pullback.snd p (pullback.fst (A.v i) (A.v j) ≫ A.v i))
          (A.overlapCoordFst i j) ∧
      Submodule.span Γ(pullback (A.v i) (A.v j), ⊤) (Set.range (A.overlapCoordFst i j)) ≤
        locallyLinearSubmodule (pullback.snd p (pullback.fst (A.v i) (A.v j) ≫ A.v i))
          (A.overlapCoordSnd i j) :=
  ⟨A.span_chart_coord_le_locallyLinear i j,
    span_le_locallyLinearSubmodule _ (A.isLocallyLinear_overlapCoordFst i j)⟩

end VectorBundleAtlas

end AlgebraicGeometry.Scheme.Hom
