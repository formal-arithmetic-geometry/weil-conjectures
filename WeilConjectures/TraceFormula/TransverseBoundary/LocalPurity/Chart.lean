/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.TransverseBoundary.Basic
public import WeilConjectures.SixFunctors.Etale.EtaleAffineLimitBaseChange

/-!
# Local charts of étale limits of smooth surfaces

Let `Z` be an étale limit with affine transition maps of smooth surfaces `Z_i` over a field `k`
(`AlgebraicGeometry.Scheme.IsEtaleLimitOfSmoothSurfaces`). Every point `y` of `Z` has an open
neighbourhood `O` which is a limit of affine étale schemes over an affine open `W` of a stage
`Z_i` (`AlgebraicGeometry.Scheme.Hom.IsEtaleAffineLimit`): `O` is the inverse image of `W`, the
limit of the inverse images of `W` in the later stages. Finitely many functions on an affine
open neighbourhood of `y` come, on a smaller such `O`, from functions on `W`, since the ring of
functions of the limit of affine schemes is the colimit of the rings of functions.

This is the *local chart* of blueprint `det-tf-transverse-corner-constant`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_isEtaleAffineLimit_chart`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- **Local charts of étale limits of smooth surfaces** (blueprint
`det-tf-transverse-corner-constant`). Let `Z` be an étale limit of smooth surfaces over `k`,
`U` an affine open of `Z` containing `y` and `f₁, …, fₙ` functions on `U`. There are an open
neighbourhood `O ⊆ U` of `y`, an affine smooth surface `W` over `k`, a morphism `π : O ⟶ W` over
`k` which is a limit of affine étale schemes over `W`, and functions `g₁, …, gₙ` on `W` with
`π^* gₐ = fₐ|_O`. -/
theorem exists_isEtaleAffineLimit_chart {k : Type u} [Field k] {Z : Scheme.{u}}
    (aZ : Z ⟶ Spec (.of k)) (hZ : IsEtaleLimitOfSmoothSurfaces aZ) (U : Z.affineOpens) (y : Z)
    (hy : y ∈ (U : Z.Opens)) {n : ℕ} (f : Fin n → Γ(Z, U)) :
    ∃ (O : Z.Opens) (hOU : O ≤ U.1) (_ : y ∈ O) (W : Scheme.{u}) (_ : IsAffine W)
      (aW : W ⟶ Spec (.of k)) (_ : SmoothOfRelativeDimension 2 aW) (π : O.toScheme ⟶ W)
      (g : Fin n → Γ(W, ⊤)),
      π.IsEtaleAffineLimit ∧ π ≫ aW = O.ι ≫ aZ ∧
        ∀ a, π.appTop (g a) = O.topIso.inv (Z.presheaf.map (homOfLE hOU).op (f a)) := by
  sorry

end AlgebraicGeometry.Scheme
