/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityDescendedTraceUniversal
public import WeilConjectures.WeilSheaf.SmoothPurityFullyFaithfulBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedComplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.GenericPoint

/-! # Open exceptional base change across different fields

For an open immersion, both compact-support functors are fully faithful and their
right adjoints are ordinary pullbacks. The mate of any invertible compact-support
square is consequently invertible. This applies directly to `smoothUnitBaseChange`
without a compatibility assumption on the chosen orientations or counits.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ ℓ)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (f' : X' ⟶ Y')
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}

/-- Pullback commutes around a square even when the fields of definition differ. -/
noncomputable def purityFieldPullbackSquareIso (sq : CommSq πX f'.left f.left πY) :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
        boundedConstructibleUpperStarOfMap ℓ πX ≅
      boundedConstructibleUpperStarOfMap ℓ πY ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f' :=
  (boundedConstructibleUpperStarOfMapComp ℓ f.left πX).symm ≪≫
    eqToIso (congrArg (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := X')) sq.w) ≪≫
      boundedConstructibleUpperStarOfMapComp ℓ πY f'.left

/-- The exceptional mate for an open immersion is invertible at every object,
including the exceptional object of the next factor in a smooth factorization. -/
theorem isIso_smoothExceptionalMate_of_isOpenImmersion
    [IsOpenImmersion f.left] [IsOpenImmersion f'.left]
    (sq : CommSq πX f'.left f.left πY)
    (bc : boundedConstructibleLowerShriek ℓ f ⋙ boundedConstructibleUpperStarOfMap ℓ πY ≅
      boundedConstructibleUpperStarOfMap ℓ πX ⋙ boundedConstructibleLowerShriek ℓ f')
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((mateEquiv (boundedConstructibleUpperShriekAdjunction ℓ f)
      (boundedConstructibleUpperShriekAdjunction ℓ f') bc.inv).app N) := by
  have hff := (fullyFaithfulBoundedConstructibleOpenImmersionLowerShriek _ ℓ f).ofIso
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ f).symm
  have hff' := (fullyFaithfulBoundedConstructibleOpenImmersionLowerShriek _ ℓ f').ofIso
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ f').symm
  have := hff.full
  have := hff.faithful
  have := hff'.full
  have := hff'.faithful
  let θ := Functor.isoWhiskerRight
      (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ f)
      (boundedConstructibleUpperStarOfMap ℓ πX) ≪≫
    purityFieldPullbackSquareIso ℓ f f' sq ≪≫
    Functor.isoWhiskerLeft (boundedConstructibleUpperStarOfMap ℓ πY)
      (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ f').symm
  exact CategoryTheory.Adjunction.isIso_mate_of_isIso_units_of_rightIso
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleUpperShriekAdjunction ℓ f') θ bc N

/-- Exceptional base change for an open immersion across arbitrary fields, in the
exact interface consumed by the descended smooth trace. -/
theorem isIso_smoothUnitBaseChange_of_isOpenImmersion
    [IsOpenImmersion f.left] [IsOpenImmersion f'.left]
    (sq : CommSq πX f'.left f.left πY)
    (bc : boundedConstructibleLowerShriek ℓ f ⋙ boundedConstructibleUpperStarOfMap ℓ πY ≅
      boundedConstructibleUpperStarOfMap ℓ πX ⋙ boundedConstructibleLowerShriek ℓ f')
    (e : (boundedConstructibleUpperStarOfMap ℓ πY).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso e] :
    IsIso (smoothUnitBaseChange ℓ f f' bc e) := by
  have := isIso_smoothExceptionalMate_of_isOpenImmersion ℓ f f' sq bc (𝟙_ _)
  change IsIso ((mateEquiv (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleUpperShriekAdjunction ℓ f') bc.inv).app (𝟙_ _) ≫
      (boundedConstructibleUpperShriek ℓ f').map e)
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
