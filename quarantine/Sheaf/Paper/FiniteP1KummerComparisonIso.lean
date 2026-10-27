/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteP1CoefficientAdjunctionCoordinates
public import Sheaf.Paper.TowerClassFinite
public import Sheaf.AlgebraicGeometry.GeoP1Cohomology

import Sheaf.AlgebraicGeometry.FiniteP1UnitOnPullback

/-! # The finite projective-line comparison isomorphism

Source: blueprint latest, diagonal-tower trace proof (1), identification of the
positive line before applying the Chern-class comparison.
(blueprint: lem-sfb-finite-p1-kummer-comparison-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/--
The exact single, shift, line, and site comparisons identify the evaluated
coefficient line on X with the pullback of the ordinary projective-line twist.
The comparison is constructed from the normalized line coordinate and the
canonical projective-line pullback comparison; no Chern arrow is used.
Source: diagonal-tower trace (1), line identification in paragraph (1).
(blueprint: lem-sfb-finite-p1-kummer-comparison-iso).
-/
theorem finiteP1_kummer_comparison_iso
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (e : X ≅ ProjectiveLine S) (cX : Chern l E X)
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX) :
    Nonempty ((SpTowerShriek.Ev l E X n).obj ((line l E cX)⟦(2 : ℤ)⟧) ≅
      (finiteOverRealization l E n e).obj
        (geoP1Twist (FiniteRing l E n) (l ^ (n + 1))
          (ULift.ext _ _ (coefficient_annihilates l E n)) (ProjectiveLine S) 1 2)) := by
  -- The normalized shifted-line word, retaining its isomorphism rather than just its hom.
  let t := (((SpTowerP1.nu l E n X).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      (SpTowerP1.nuSingle l E n X _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso c.line ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (lineEvaluation l E cX n).symm ≪≫
        (((SpTowerShriek.ev l E X n).mapDerivedCategorySingleFunctor 0).app _).symm) ≪≫
    (((SpTowerShriek.Ev l E X n).commShiftIso (2 : ℤ)).app _).symm)
  have hP : IsUnit ((l ^ (n + 1) : ℕ) : Γ(ProjectiveLine S, ⊤)) :=
    finiteP1_unitOnPullback (l ^ (n + 1)) (ProjectiveLine S ↘ S)
      (by simpa only [Nat.cast_pow] using hS.pow (n + 1))
  exact ⟨t.symm ≪≫
    (Functor.mapDerivedCategory
      (Scheme.sfIntrinsicModuleEquivalence X (SpTowerShriek.R l E n)).functor).mapIso
        (geoP1TwistPullback (FiniteRing l E n) (l ^ (n + 1))
          (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime l)) _)
          (ULift.ext _ _ (coefficient_annihilates l E n)) e.hom hP 1 2).symm⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
