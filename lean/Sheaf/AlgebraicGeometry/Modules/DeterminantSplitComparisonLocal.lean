/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearMaps
import Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearBijective

/-!
# Local split determinant comparisons

Source: blueprint `lem-sc-riemann-roch`, proof of (*), determinant paragraph.
(blueprint: new-determinant-split-local).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- This is the sectionwise construction part of the split determinant comparison.
Proof: construct bases on a common trivializing neighborhood, transport the direct-sum
exterior isomorphism, and sheafify the resulting sectionwise maps.
(blueprint: new-determinant-split-local) -/
theorem determinant_split_comparison_local {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₃.IsFiniteLocallyFreeOfRank r₃]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g)
    (l : ∀ (W : X.Opens), W ≤ U → S.X₃.val.obj (op W) → S.X₂.val.obj (op W))
    (hl : ∀ W hW b, S.g.val.app (op W) (l W hW b) = b) :
    ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ (d : ∀ (W : X.Opens), W ≤ V →
        (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
          ≃ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W)),
      ∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
        (b : Fin r₃ → S.X₃.val.obj (op W)),
        d W hW (tmulSection (exteriorSheafSection S.X₁ r₁ W a)
          (exteriorSheafSection S.X₃ r₃ W b)) =
        exteriorSheafSection S.X₂ r₂ W
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op W) (a j))
            (fun j ↦ l W (hW.trans hVU) (b j)) (Fin.cast hr i)) := by
  classical
  obtain ⟨d, ⟨hd, _⟩, _⟩ := determinant_split_linear_maps_exists S r₁ r₂ r₃ hr U e hf hg l hl
  intro x hx
  obtain ⟨V, hVU, hxV, hbij⟩ :=
    determinant_split_linear_maps_locally_bijective S r₁ r₂ r₃ hr U e hf hg l hl d hd x hx
  refine ⟨V, hVU, hxV,
    (fun W hW ↦ LinearEquiv.ofBijective (d W (hW.trans hVU)) (hbij W hW)), ?_⟩
  intro W hW a b
  exact hd W (hW.trans hVU) a b

/-- Converting a natural family of linear maps to equal linear equivalences preserves naturality.
Source: blueprint, Riemann--Roch determinant paragraph
(blueprint: new-determinant-split-restriction).
Proof: substitute the equality with the original linear maps into the restriction equation;
then apply their assumed naturality. -/
theorem determinant_split_comparison_restriction {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (_hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₃.IsFiniteLocallyFreeOfRank r₃]
    (V : X.Opens) (d : ∀ (W : X.Opens), W ≤ V →
      (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
        ≃ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W))
    (d₀ : ∀ (W : X.Opens), W ≤ V →
      (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
        →ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W))
    (hn : ∀ (W Z : X.Opens) (hW : W ≤ V) (hZW : Z ≤ W) y,
      (exteriorSheaf S.X₂ r₂).val.map (homOfLE hZW).op (d₀ W hW y) =
        d₀ Z (hZW.trans hW)
          ((exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.map
            (homOfLE hZW).op y))
    (hd : ∀ W hW y, d W hW y = d₀ W hW y) :
    ∀ (W Z : X.Opens) (hW : W ≤ V) (hZW : Z ≤ W) y,
      (exteriorSheaf S.X₂ r₂).val.map (homOfLE hZW).op (d W hW y) =
        d Z (hZW.trans hW)
          ((exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.map
            (homOfLE hZW).op y) := by
  intro W Z hW hZW y
  simpa only [hd] using hn W Z hW hZW y

end AlgebraicGeometry.Scheme.Modules

