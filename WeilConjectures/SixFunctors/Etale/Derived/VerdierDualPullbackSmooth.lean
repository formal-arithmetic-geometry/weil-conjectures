/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Formal
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality

/-!
# Duality against pullback along an oriented smooth morphism

For a smooth morphism `f : X ⟶ Y` of pure relative dimension `d` carrying an orientation
`Λ_X(d)[2d] ≅ Rf^! Λ_Y`, the duality against pullback `𝔻_X Lf^* ≅ Rf^! 𝔻_Y`
(`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_leftDerivedUpperStar`) reads
`𝔻_X (Lf^* K) ≅ Lf^*(𝔻_Y K) ⊗ᴸ Λ_X(d)[2d]`: this is the second assertion of blueprint
`cor-sf-duality-pullback`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y S : Scheme.{u}}
  [HasInvertibleExponent Λ X]

/-- Blueprint `cor-sf-duality-pullback`, smooth case: for a smooth `f : X ⟶ Y` of pure relative
dimension `d` with an orientation `o : Λ_X(d)[2d] ≅ Rf^! Λ_Y` and `a_X = f ≫ a_Y`,

`𝔻_X (Lf^* K) ≅ Lf^*(𝔻_Y K) ⊗ᴸ Λ_X(d)[2d]`,

that is `D_X Lf^* ≅ Lf^* D_Y (d)[2d]`. It combines `𝔻_X Lf^* ≅ Rf^! 𝔻_Y`
(`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_leftDerivedUpperStar`), the smooth duality
`Rf^! M ≅ Lf^* M ⊗ᴸ Rf^! Λ_Y`
(`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_leftDerivedUpperStar_obj_dualizingComplex`)
and the orientation. -/
theorem nonempty_iso_verdierDual_leftDerivedUpperStar_of_orientation (aY : Y ⟶ S)
    [HasCompactification aY] (f : X ⟶ Y) [HasCompactification f]
    [HasCompactification (f ≫ aY)] [QuasiCompact (f ≫ aY)] {d : ℕ} (o : Orientation Λ f d)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((verdierDual (ModuleCat.{u + 1} Λ) (f ≫ aY)).obj
        (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ≅
      ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj
        ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj (op K)))).obj
          ((tateObject Λ X d)⟦(2 * d : ℤ)⟧)) := by
  have := o.smoothOfRelativeDimension
  obtain ⟨e₁⟩ := nonempty_iso_verdierDual_leftDerivedUpperStar Λ aY f K
  obtain ⟨e₂⟩ := nonempty_iso_derivedTensor_leftDerivedUpperStar_obj_dualizingComplex Λ f d
    ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj (op K))
  exact ⟨e₁ ≪≫ e₂.symm ≪≫ ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj _).mapIso o.purity.symm⟩

end Etale

end AlgebraicGeometry
