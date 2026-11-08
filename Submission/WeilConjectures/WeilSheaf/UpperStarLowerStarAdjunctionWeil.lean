/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.CategoryTheory.Triangulated.AdjunctionUnitLocal
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Adjunction.Basic
public import Submission.WeilConjectures.WeilSheaf.LowerStarComp
public import Submission.WeilConjectures.WeilSheaf.Triangle
public import Submission.WeilConjectures.WeilSheaf.UpperStarLowerStar
public import Submission.WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction
public import Submission.WeilConjectures.WeilSheaf.UpperStarId

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Composition of pullbacks and pushforwards of Weil sheaves

The pushforward of Weil sheaves is left exact, and pushforwards compose. (The composition of
pullbacks, `AlgebraicGeometry.WeilSheaf.upperStarCompIso`, is in
`WeilConjectures.WeilSheaf.UpperStarId`.)

## Main definitions

- `AlgebraicGeometry.WeilSheaf.lowerStarCompIso`: `φ_* ⋙ ψ_* ≅ (φ ≫ ψ)_*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace CategoryTheory.Adjunction

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X Y Z : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

variable [Fact (ringChar k₀ ≠ l)]

section

variable [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- The pushforward of Weil sheaves is the pushforward of pro-étale Weil sheaves. -/
noncomputable def lowerStarCompιIso :
    WeilSheaf.lowerStar φ ⋙ (WeilSheaf.objectProperty k₀ l Y).ι ≅
      (WeilSheaf.objectProperty k₀ l X).ι ⋙ ProEtaleWeilSheaf.lowerStar k₀ l φ :=
  ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _

/-- The pushforward of Weil sheaves is left exact. -/
instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    PreservesFiniteLimits (WeilSheaf.lowerStar (k₀ := k₀) (l := l) φ) :=
  preservesFiniteLimits_of_comp_ι _ (ProEtaleWeilSheaf.lowerStar k₀ l φ) (lowerStarCompιIso φ)

end

variable [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  (ψ : Y ⟶ Z) [ψ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact ψ] [QuasiSeparated ψ]
  [LocallyOfFiniteType ψ] [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]

/-- The composition isomorphism `φ_* ⋙ ψ_* ≅ (φ ≫ ψ)_*` of pushforwards of Weil sheaves. -/
noncomputable def lowerStarCompIso :
    WeilSheaf.lowerStar φ ⋙ WeilSheaf.lowerStar ψ ≅
      WeilSheaf.lowerStar (k₀ := k₀) (l := l) (φ ≫ ψ) :=
  ((WeilSheaf.objectProperty k₀ l Z).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (lowerStarCompιIso ψ) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (lowerStarCompιIso φ) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ProEtaleWeilSheaf.lowerStarCompIso k₀ l φ ψ) ≪≫
      (lowerStarCompιIso (φ ≫ ψ)).symm)

end WeilSheaf

end AlgebraicGeometry
