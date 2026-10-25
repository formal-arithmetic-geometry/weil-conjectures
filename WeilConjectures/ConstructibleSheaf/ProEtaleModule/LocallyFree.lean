/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def

/-!

# Locally free module objects on the pro-étale site

Let `A` be a closed symmetric monoidal Grothendieck abelian category, `X` a scheme and `R` a
ring object of `Sheaf (Scheme.ProEt.topology X) A`.

`ProEtale.IsLocallyFree R M`: there is a pro-étale cover `{Uᵢ ⟶ X}` such that each `M|_{Uᵢ}`
is free of finite rank over `R|_{Uᵢ}`. For `R = E_X` with `E` a field these are the lisse
`E`-sheaves of Bhatt–Scholze, *The pro-étale topology for schemes*, Definition 6.8.6.

-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

variable {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]

/-- A sheaf of `R`-modules on `X_proét` is *locally free* (of finite rank) if there is a
pro-étale cover `{Uᵢ ⟶ X}` such that each `M|_{Uᵢ}` is isomorphic to `(R|_{Uᵢ})^{nᵢ}`. -/
def IsLocallyFree (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
    Mod.IsFree ((ProEtale.upperStar A (𝒰.f i)).obj R)
      (((ProEtale.upperStar A (𝒰.f i)).mapMod R).obj M)

end AlgebraicGeometry.ProEtale
