/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Global sections of a pushforward and of a pullback of étale sheaves

For a morphism of schemes `f : X ⟶ Y`, this file identifies the global sections of a
pushforward, `Γ(Y, f_* F) ≅ Γ(X, F)`. For an étale sheaf `G` on `Y`, it constructs the pullback
map `Γ(Y, G) ⟶ Γ(X, f^* G)` on global sections, and shows that it is an isomorphism when `f` is.

## Main definitions

- `AlgebraicGeometry.Etale.lowerStarCompGlobalSectionsIso`: the isomorphism
  `f_* ⋙ Γ_Y ≅ Γ_X`.
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

/-- Global sections are invariant under the pushforward along a morphism `f : X ⟶ Y`:
`Γ(Y, f_* F) ≅ (f_* F)(Y) = F(Y ×_Y X) ≅ F(X) ≅ Γ(X, F)`. -/
noncomputable def lowerStarCompGlobalSectionsIso :
    (f)_*[A] ⋙ Sheaf.Γ Y.smallEtaleTopology A ≅ Sheaf.Γ X.smallEtaleTopology A :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal) ≪≫
    lowerStarCompSheafSectionsTerminalIso A f ≪≫
    (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).symm

/-- The pullback map on global sections

`Γ(Y, G) ≅ G(Y) ⟶ (f_* f^* G)(Y) = (f^* G)(Y ×_Y X) ≅ (f^* G)(X) ≅ Γ(X, f^* G)`,

given by the unit `G ⟶ f_* f^* G` of the adjunction `f^* ⊣ f_*` evaluated at the terminal
object `Y` of the small étale site of `Y`, and the identification of its base change
`Y ×_Y X` with the terminal object `X` of the small étale site of `X`. For a finite `f` this is
the pullback `f^♯ a` of a section along a finite morphism.
(blueprint: `def-weil-pbc-finite-section-pullback`) -/
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

/-- The structure morphism of the terminal object of the small étale site of `X` is an
isomorphism: the terminal object is isomorphic to `𝟙 X`. -/
lemma isIso_terminal_hom (X : Scheme.{u}) : IsIso (⊤_ X.Etale).hom := by
  let e := terminalIsTerminal.uniqueUpToIso
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)
  have : IsIso e.hom.left :=
    ⟨e.inv.left, congrArg (·.left) e.hom_inv_id, congrArg (·.left) e.inv_hom_id⟩
  have h : e.hom.left = (⊤_ X.Etale).hom :=
    (Category.comp_id _).symm.trans (MorphismProperty.Over.w e.hom)
  rw [← h]
  exact this

end AlgebraicGeometry.Etale
