/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.TensorBaseChange

/-!
# Locality of the base change map on the source

Let `X' = X ×_K S'` and `Y = X' ×_{S'} T`. Whether the base change map
`Lp^* E ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Lp^* E ⊗ᴸ Le^* F)` is an isomorphism is local on `X`: it
is an isomorphism as soon as, for every affine open `U ⊆ X`, the base change map of the
restricted diagram `U ×_K S' ⟵ U ×_K T` at the restriction of `E` is
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_of_affineOpens`). The restriction of the
base change map to the open `U ×_K S'` of `X'` is identified with the base change map of the
restricted diagram, using étale base change for `Rh_*` and the monoidality of the restrictions.

This is the reduction "the question is local on `X`" in the proof of blueprint `lem-kun-0f1j`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

variable {X X' S' T Y B : Scheme.{u}}

/-- The base change map `Lp^* E ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Lp^* E ⊗ᴸ Le^* F)` is an
isomorphism if its analogues for the restrictions of the diagram to the affine opens of `X`
are. -/
theorem isIso_tensorBaseChangeMap_of_affineOpens (a : X ⟶ B) (b : S' ⟶ B)
    (p : X' ⟶ X) (f' : X' ⟶ S') (_sq₁ : IsPullback p f' a b) (h : Y ⟶ X') (e : Y ⟶ T)
    (g : T ⟶ S') (sq₂ : IsPullback h e f' g)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A))
    (_H : ∀ U : X.affineOpens, ∀ {X'U YU : Scheme.{u}} (pU : X'U ⟶ (U : X.Opens))
      (f'U : X'U ⟶ S') (hU : YU ⟶ X'U) (eU : YU ⟶ T),
      IsPullback pU f'U ((U : X.Opens).ι ≫ a) b → ∀ (sqU : IsPullback hU eU f'U g),
        IsIso (tensorBaseChangeMap A hU eU f'U g sqU.w
          (L((pU)^*[A]).obj (L(((U : X.Opens).ι)^*[A]).obj E)) F)) :
    IsIso (tensorBaseChangeMap A h e f' g sq₂.w (L((p)^*[A]).obj E) F) :=
  sorry

end Etale

end AlgebraicGeometry
