/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension

/-!
# Comparing the transform of the zero extension with the transform of the middle extension

Rotating the triangle of `0 → j_!M → j_*M → B → 0`, where `B = j_*M / j_!M` is the punctual
boundary sheaf, gives a short exact sequence of curve perverse sheaves
`B → j_!M[1] → j_*M[1]`. Fourier exactness on the perverse heart turns it into a short exact
sequence of perverse sheaves on the dual line. Each punctual summand of `B` transforms into a
lisse Artin–Schreier kernel shifted by one, and the middle extension transforms into
`(j'_*M')[1]`, so the whole sequence is concentrated in one ordinary degree:

`0 → B' → G → j'_*M' → 0`, with `FT_ψ(j_!M[1]) ≃ G[1]` and `FT_ψ(B) ≃ B'[1]`.

The correction term `B'` is lisse on the entire dual line and, by semicontinuity of weights
at the boundary points together with the weight zero of the Artin–Schreier kernel, has weights
at most `w`.

## Main statements

- `AlgebraicGeometry.exists_shortExact_fourierTransform_extensionByZero`: the exact sequence
  above, with `B'` lisse of weights at most `w`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] {l : ℕ} [Fact l.Prime]
variable (ψ : AddChar k₀ (PadicAlgCl l)) (k : Type u) [Field k] [Algebra k₀ k] [IsAlgClosed k]

/-- Blueprint `sk-p-dl-a1-correction`: The zero-extension comparison. For an irreducible
nonexceptional `M` pure of weight `w` with Fourier partner `D'`, there are ordinary Weil
sheaves `G` and `B'` on the dual line with `FT_ψ(j_!M[1]) ≃ G[1]`, `FT_ψ(B) ≃ B'[1]` for the
boundary sheaf `B = j_*M / j_!M`, and a short exact sequence `0 → B' → G → j'_*M' → 0`. The
correction `B'` is lisse on the entire dual line and has weights at most `w`. -/
theorem exists_shortExact_fourierTransform_extensionByZero (ι : PadicAlgCl l →+* ℂ)
    (D D' : LisseOnDenseOpen k₀ l) [Simple D.sheaf] (hne : D.sheaf.IsNonexceptional ψ k)
    {w : ℝ} (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) (hFT : D.IsFourierPartner ψ D') :
    ∃ S : ShortComplex (WeilSheaf k₀ l (affineLine k₀)), S.ShortExact ∧
      S.X₁.IsLisse ∧ S.X₁.HasWeightsAtMost ι w ∧
      Nonempty (S.X₃ ≅ D'.directImage) ∧
      Nonempty ((fourierTransform ψ).obj D.shiftedExtensionByZero ≅
        (WeilSheaf.toComplex.obj S.X₂)⟦(1 : ℤ)⟧) ∧
      Nonempty ((fourierTransform ψ).obj (WeilSheaf.toComplex.obj D.boundarySheaf) ≅
        (WeilSheaf.toComplex.obj S.X₁)⟦(1 : ℤ)⟧) := by
  sorry

end AlgebraicGeometry
