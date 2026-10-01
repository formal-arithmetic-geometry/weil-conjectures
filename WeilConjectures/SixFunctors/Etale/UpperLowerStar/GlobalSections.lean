/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Global sections of a pullback of étale sheaves

For a morphism of schemes `f : X ⟶ Y` and an étale sheaf `G` on `Y`, this file constructs the
pullback map `Γ(Y, G) ⟶ Γ(X, f^* G)` on global sections, and shows that it is an isomorphism
when `f` is.

## Main definitions

- `AlgebraicGeometry.Etale.globalSectionsUpperStarMap`: the map `Γ(Y, G) ⟶ Γ(X, f^* G)`.
- `AlgebraicGeometry.Etale.globalSectionsUpperStarIso`: the isomorphism
  `Γ(Y, G) ≅ Γ(X, f^* G)` for an isomorphism `f`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Sheaf Y.smallEtaleTopology A)

/-- The pullback map on global sections

`Γ(Y, G) ≅ G(Y) ⟶ (f_* f^* G)(Y) = (f^* G)(Y ×_Y X) ≅ (f^* G)(X) ≅ Γ(X, f^* G)`,

given by the unit `G ⟶ f_* f^* G` of the adjunction `f^* ⊣ f_*` evaluated at the terminal
object `Y` of the small étale site of `Y`, and the identification of its base change
`Y ×_Y X` with the terminal object `X` of the small étale site of `X`. -/
noncomputable def globalSectionsUpperStarMap :
    (Sheaf.Γ _ A).obj G ⟶ (Sheaf.Γ _ A).obj ((f)^*[A].obj G) :=
  (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app G ≫
    ((sheafSections _ _).obj (op (⊤_ _))).map ((upperStarLowerStarAdjunction A f).unit.app G) ≫
    ((f)^*[A].obj G).obj.map (PreservesTerminal.iso f.Etale).inv.op ≫
    (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app _

/-- The pullback map on global sections along an isomorphism is an isomorphism: the pullback
along an isomorphism is an equivalence, so the unit of `f^* ⊣ f_*` is an isomorphism. -/
instance [IsIso f] : IsIso (globalSectionsUpperStarMap A f G) := by
  have := isEquivalence_upperStar A f
  unfold globalSectionsUpperStarMap
  infer_instance

/-- The isomorphism `Γ(Y, G) ≅ Γ(X, f^* G)` of global sections along an isomorphism
`f : X ⟶ Y`, see `AlgebraicGeometry.Etale.globalSectionsUpperStarMap`. -/
noncomputable def globalSectionsUpperStarIso [IsIso f] :
    (Sheaf.Γ _ A).obj G ≅ (Sheaf.Γ _ A).obj ((f)^*[A].obj G) :=
  asIso (globalSectionsUpperStarMap A f G)

end AlgebraicGeometry.Etale
