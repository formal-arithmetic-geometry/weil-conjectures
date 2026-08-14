/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale

/-!

# Composition isomorphisms for the pushforward `g_*` and the pullback `g^*`

For composable morphisms of schemes `h₁ : T ⟶ S` and `h₂ : S ⟶ R`, this file provides
the pseudofunctoriality isomorphisms of the pushforward and the pullback on sheaves for
the small sites:

- `CategoryTheory.GrothendieckTopology.lowerStarComp`:
  `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*`. Since the pushforward is composition with the base
  change functor `MorphismProperty.Over.pullback`, this is induced by the pullback
  pasting isomorphism `MorphismProperty.Over.pullbackComp` through
  `Functor.sheafPushforwardContinuousComp'`.
- `CategoryTheory.GrothendieckTopology.upperStarComp`:
  `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*`, obtained from `lowerStarComp` by uniqueness of left
  adjoints (conjugation of the adjunctions `g^* ⊣ g_*`).

Both are specialized to the small étale sites as `AlgebraicGeometry.Etale.lowerStarComp`
and `AlgebraicGeometry.Etale.upperStarComp`.

-/

@[expose] public section

universe v' u' u

open CategoryTheory Category Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory

variable (A : Type u') [Category.{v'} A]

namespace GrothendieckTopology

variable (P Q : MorphismProperty Scheme.{u})
variable [P.IsStableUnderBaseChange]

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

variable [(MorphismProperty.Over.pullback P ⊤ h₁).IsContinuous
    (S.smallGrothendieckTopology Q (Q := P)) (T.smallGrothendieckTopology Q (Q := P))]
  [(MorphismProperty.Over.pullback P ⊤ h₂).IsContinuous
    (R.smallGrothendieckTopology Q (Q := P)) (S.smallGrothendieckTopology Q (Q := P))]
  [(MorphismProperty.Over.pullback P ⊤ (h₁ ≫ h₂)).IsContinuous
    (R.smallGrothendieckTopology Q (Q := P)) (T.smallGrothendieckTopology Q (Q := P))]

/-- The composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` of pushforwards on
sheaves for the small sites: both sides send a sheaf `G` to the sheaf
`(V → R) ↦ G(V ×_R T → T)`, up to the pullback pasting isomorphism
`(V ×_R S) ×_S T ≅ V ×_R T` of `MorphismProperty.Over.pullbackComp`. -/
noncomputable def lowerStarComp :
    lowerStar A P Q h₁ ⋙ lowerStar A P Q h₂ ≅ lowerStar A P Q (h₁ ≫ h₂) :=
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) h₁ h₂).symm) A
    (R.smallGrothendieckTopology Q (Q := P)) (S.smallGrothendieckTopology Q (Q := P))
    (T.smallGrothendieckTopology Q (Q := P))

section UpperStar

variable [∀ F : (P.Over ⊤ S)ᵒᵖ ⥤ A,
    (MorphismProperty.Over.pullback P ⊤ h₁).op.HasLeftKanExtension F]
  [∀ F : (P.Over ⊤ R)ᵒᵖ ⥤ A,
    (MorphismProperty.Over.pullback P ⊤ h₂).op.HasLeftKanExtension F]
  [∀ F : (P.Over ⊤ R)ᵒᵖ ⥤ A,
    (MorphismProperty.Over.pullback P ⊤ (h₁ ≫ h₂)).op.HasLeftKanExtension F]
  [HasWeakSheafify (S.smallGrothendieckTopology Q (Q := P)) A]
  [HasWeakSheafify (T.smallGrothendieckTopology Q (Q := P)) A]

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*` of pullbacks on sheaves
for the small sites, obtained from the composition isomorphism `lowerStarComp` of the
pushforwards by uniqueness of left adjoints: both sides are left adjoint to
`(h₁)_* ⋙ (h₂)_*`. -/
noncomputable def upperStarComp :
    upperStar A P Q (h₁ ≫ h₂) ≅ upperStar A P Q h₂ ⋙ upperStar A P Q h₁ :=
  ((conjugateIsoEquiv (upperStarLowerStarAdjunction A P Q (h₁ ≫ h₂))
      ((upperStarLowerStarAdjunction A P Q h₂).comp
        (upperStarLowerStarAdjunction A P Q h₁))).symm
    (lowerStarComp A P Q h₁ h₂).symm).symm

end UpperStar

end GrothendieckTopology

end CategoryTheory

namespace AlgebraicGeometry

variable (A : Type u') [Category.{v'} A]
variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

/-- The composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` of pushforwards on
étale sheaves. -/
noncomputable def Etale.lowerStarComp :
    Etale.lowerStar A h₁ ⋙ Etale.lowerStar A h₂ ≅ Etale.lowerStar A (h₁ ≫ h₂) :=
  GrothendieckTopology.lowerStarComp A @Etale @Etale h₁ h₂

section UpperStar

variable [∀ F : S.Etaleᵒᵖ ⥤ A,
    (MorphismProperty.Over.pullback @Etale ⊤ h₁).op.HasLeftKanExtension F]
  [∀ F : R.Etaleᵒᵖ ⥤ A,
    (MorphismProperty.Over.pullback @Etale ⊤ h₂).op.HasLeftKanExtension F]
  [∀ F : R.Etaleᵒᵖ ⥤ A,
    (MorphismProperty.Over.pullback @Etale ⊤ (h₁ ≫ h₂)).op.HasLeftKanExtension F]
  [HasWeakSheafify S.smallEtaleTopology A]
  [HasWeakSheafify T.smallEtaleTopology A]

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*` of pullbacks on étale
sheaves, obtained from `Etale.lowerStarComp` by uniqueness of left adjoints. -/
noncomputable def Etale.upperStarComp :
    Etale.upperStar A (h₁ ≫ h₂) ≅ Etale.upperStar A h₂ ⋙ Etale.upperStar A h₁ :=
  haveI : HasWeakSheafify (S.smallGrothendieckTopology (Q := @Etale) @Etale) A :=
    inferInstanceAs (HasWeakSheafify S.smallEtaleTopology A)
  haveI : HasWeakSheafify (T.smallGrothendieckTopology (Q := @Etale) @Etale) A :=
    inferInstanceAs (HasWeakSheafify T.smallEtaleTopology A)
  GrothendieckTopology.upperStarComp A @Etale @Etale h₁ h₂

end UpperStar

end AlgebraicGeometry
