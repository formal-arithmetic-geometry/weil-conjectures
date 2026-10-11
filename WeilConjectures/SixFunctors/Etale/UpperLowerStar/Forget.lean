/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

/-!
# Pullback of étale sheaves of modules and their underlying abelian sheaves

For a commutative ring `Λ` and a morphism of schemes `f : X ⟶ Y`, pulling back an étale sheaf of
`Λ`-modules commutes with taking the underlying abelian sheaf. Consequently the pullback map on
global sections `Γ(Y, G) ⟶ Γ(X, f^* G)` is an isomorphism for `G` if and only if it is one for
the underlying abelian sheaf of `G`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pullback map on global sections of an étale sheaf of `Λ`-modules is an isomorphism if
and only if it is one for the underlying abelian sheaf. -/
theorem isIso_globalSectionsUpperStarMap_iff_forget₂
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) f G) ↔
      IsIso (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)) :=
  sorry

end AlgebraicGeometry.Etale
