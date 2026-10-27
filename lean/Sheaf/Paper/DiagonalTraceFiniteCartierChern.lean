/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DiagonalTowerTraceLimit
public import Sheaf.Paper.DiagonalTowerTraceCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Forgetting the support of the completed diagonal at one finite level -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource diagonalCompletedCoefficientMap


/-- The ordinary constant-to-supported map induced by the completed coefficient map.
Source: diagonal tower trace proof (2), forgetting support of the diagonal divisor.
(blueprint: def-sfb-diagonal-trace-completed-supported-unit). -/
def completedSupportedUnit (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    SheafOfModules.unit.{u, u + 1, u + 1}
      (Scheme.purTwistRing (diagonalSurface Y)
        (Scheme.purTwistZlCompletion (diagonalSurface Y) l)) ⟶
      diagonalCompletedSource l Y := by
  let unitToPushforwardRestrictedUnit
      {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
      {J : GrothendieckTopology C} {K : GrothendieckTopology D}
      {F : C ⥤ D} [F.IsContinuous J K]
      {R : Sheaf J RingCat.{u + 1}} {S T : Sheaf K RingCat.{u + 1}}
      (α : R ⟶ (F.sheafPushforwardContinuous RingCat J K).obj S) (φ : S ⟶ T) :
      SheafOfModules.unit.{u, u + 1, u + 1} R ⟶
        (SheafOfModules.pushforward.{u + 1} α).obj
          ((SheafOfModules.restrictScalars φ).obj (SheafOfModules.unit T)) := by
    exact SheafOfModules.unitToPushforwardObjUnit
      (α ≫ (F.sheafPushforwardContinuous RingCat J K).map φ)
  unfold diagonalCompletedSource Scheme.proEtaleRingedDirectImage
  let i := diagonalImmersion Y
  let R := Scheme.purTwistZlCompletion (diagonalSurface Y) l
  exact unitToPushforwardRestrictedUnit
    (C := (diagonalSurface Y).ProEt) (D := (ProjectiveLine Y).ProEt)
    (J := Scheme.ProEt.topology (diagonalSurface Y))
    (K := Scheme.ProEt.topology (ProjectiveLine Y))
    (F := Scheme.proEtaleBaseChange i)
    (R := Scheme.purTwistRing (diagonalSurface Y) R)
    (S := Scheme.proEtaleModuleCoefficients
      ((Scheme.proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R))
    (T := Scheme.purTwistRing (ProjectiveLine Y)
      (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))
    ⟨Functor.whiskerRight
      ((Scheme.proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app R).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
    ((sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (diagonalCompletedCoefficientMap l i))

/-- On the surface, forgetting support of the finite completed diagonal gives the
Chern arrow of the actual divisor line. The assertion precedes direct image
along a projection and the geometric adjunction.

Source: diagonal tower limit clause (3), positive finite Cartier reductions;
`sk-prop-sp-tower-geometric-classes.proof.md` (2)--(3), the finite Kummer class;
`lem-amb-cartier-kummer-map.proof.md`, forgetting support of the Cartier class.
(blueprint: lem-sfb-diagonal-trace-finite-cartier-chern).

Proof: unpack the normalized limit data. Write c for its strict supported Ext
class, s for its source cone and t for its root cone. Postcompose the whole-system
limit equation with projection n. Naturality of that projection and the exact
single and shift comparisons identify the projected arrow with c evaluated at n,
preceded by the source cone component. The source-cone generator equation and
DiagonalSourceNormalization identify this source component with the canonical
completed-to-finite supported coefficient quotient. The root-limit equation and
the normalized root comparison identify the target with the finite root line.
Precomposing completedSupportedUnit forgets support, because its underlying map
is the direct-image coefficient map and it sends one to the supported section one.

The finite-cycle normalization identifies the projected class with the positive
Cartier reduction at exponent n+1. Cartier reduction existence and uniqueness
transport it to the etale supported Kummer class with its canonical integral
adjunct. The supported Kummer Chern realization identifies its composite with
the constant-to-support map as the positive Kummer Chern class of the dual ideal.
That line is diagonalPic Y. Apply hc to that Picard class at n. Its integral
boundary equation gives the same Kummer boundary. The coefficient-one and
root-tensor equations in k identify its quotient and root endpoints with the
ones just computed; hn fixes the scalar-unit and single/shift comparisons.
First pass from the completed coefficient unit to its derived finite quotient:
l is regular on the completed ring, and its quotient at exponent n+1 is the
actual finite constant ring. Thus derived reduction of that regular unit is the
finite coefficient unit, and its adjunction unit is the actual coefficient
projection. The scalar-extension adjunction from the integral unit to that finite
unit then makes the coefficient-linear arrows equal from their integral adjuncts.
This does not require faithfulness of forgetting on arbitrary Ext.
Finally the exact-cone projection identity identifies the coefficient input
with k.unitMap followed by L.projection. Exponent n+1 is positive even at n=0;
the same maps and equations cover the empty base. -/
theorem diagonalTrace_finiteCartierChern
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (hδ : IsDiagonalLimit l Y hY D δ)
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (hn : c.Normalized l (ULift.{u} (Padic l)))
    (hc : SpTowerClasses.FiniteChernNormalization l (ULift.{u} (Padic l)) c)
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (L : DiagonalRlim (DiagonalMod l (diagonalSurface Y))) (n : ℕ) :
    let E := ULift.{u} (Padic l)
    let U := diagonalCompletedUnderlying l (diagonalSurface Y)
    let V := r.F.mapDerivedCategory
    let ev := ((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
      (op n)).mapDerivedCategory
    U.map
        ((DerivedCategory.singleFunctor (DiagonalCompleted l (diagonalSurface Y)) 0).map
          (completedSupportedUnit l Y) ≫ δ) ≫
      shiftedComparison U (V ⋙ L.R) (k.lineMap l E L) 2 ≫ (L.projection n).app _ =
        (k.unitMap l E L ≫ (L.projection n).app _) ≫
          ev.map (V.map (SpTowerClasses.firstChern l E c
            (SpTowerClasses.diagonalPic Y))) := by sorry

end AlgebraicGeometry.ProEtale.DiagonalTrace
