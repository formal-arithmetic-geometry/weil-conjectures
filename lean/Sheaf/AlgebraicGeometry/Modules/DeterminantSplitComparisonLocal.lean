/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.Algebra.Homology.ShortComplex.Basic

/-!
# Local split determinant comparisons

Source: blueprint `lem-sc-riemann-roch`, proof of (*), determinant paragraph.
(blueprint: new-determinant-split-local).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Converting a natural family of linear maps to equal linear equivalences preserves naturality.
Source: blueprint, Riemann--Roch determinant paragraph
(blueprint: new-determinant-split-restriction).
Proof: substitute the equality with the original linear maps into the restriction equation;
then apply their assumed naturality. -/
theorem determinant_split_comparison_restriction {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ)
    (V : X.Opens) (d : ∀ (W : X.Opens), W ≤ V →
      (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
        ≃ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W))
    (dNatural : ∀ (W : X.Opens), W ≤ V →
      (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
        →ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W))
    (hn : ∀ (W Z : X.Opens) (hW : W ≤ V) (hZW : Z ≤ W) y,
      (exteriorSheaf S.X₂ r₂).val.map (homOfLE hZW).op (dNatural W hW y) =
        dNatural Z (hZW.trans hW)
          ((exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.map
            (homOfLE hZW).op y))
    (hd : ∀ W hW y, d W hW y = dNatural W hW y) :
    ∀ (W Z : X.Opens) (hW : W ≤ V) (hZW : Z ≤ W) y,
      (exteriorSheaf S.X₂ r₂).val.map (homOfLE hZW).op (d W hW y) =
        d Z (hZW.trans hW)
          ((exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.map
            (homOfLE hZW).op y) := by
  intro W Z hW hZW y
  calc
    (exteriorSheaf S.X₂ r₂).val.map (homOfLE hZW).op (d W hW y) =
        (exteriorSheaf S.X₂ r₂).val.map (homOfLE hZW).op
          (dNatural W hW y) := by rw [hd W hW y]
    _ = dNatural Z (hZW.trans hW)
          ((exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.map
            (homOfLE hZW).op y) := hn W Z hW hZW y
    _ = d Z (hZW.trans hW)
          ((exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.map
            (homOfLE hZW).op y) := by
      rw [hd Z (hZW.trans hW)]

end AlgebraicGeometry.Scheme.Modules

