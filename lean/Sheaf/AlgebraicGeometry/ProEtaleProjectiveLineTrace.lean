/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem
public import Sheaf.AlgebraicGeometry.CartierDerivedRealization
public import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison

/-!
# The pro-etale projective-line trace and diagonal integrals

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-geo-p1-adjunction,
det-sp-p1-trace, clauses 1--3 and its final arbitrary-base consequence
(blueprint: det-sp-p1-trace).

The helpers extend the existing canonical-arrow interface to arbitrary bases by
accepting the Kummer-normalized Chern arrow explicitly. They introduce no replacement
site, twist, derived functor, or independently chosen trace. Every existential arrow
is fixed by its canonical formula. The diagonal uses the literal Cartier comparison
equation with the uniquely normalized supported Kummer boundary.

## Main statements

- `SpP1TraceStatement` assembles the canonical formulas and every conclusion.
- `proEtale_projectiveLine_trace` specializes to the specified finite coefficient ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u uC vC wC uD vD wD

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Exact comparison of the supported and Cartier Ext classes.
Source: det-sp-p1-trace, clause 3 (blueprint: det-sp-p1-trace). -/
def SpP1CartierCompatibility {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasExt.{wC} C] {D : Type uD} [Category.{vD} D] [Abelian D] [HasExt.{wD} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X L : C} {Y : D} (σ : F.obj X ⟶ Y) (κ : Ext X L 2) (c : Ext Y (F.obj L) 2) :
    Prop := (Ext.mk₀ σ).comp c (zero_add 2) = κ.mapExactFunctor F

/-- The canonical source, diagonal-class, and projection-trace formulas, and both
integral identities. The canonical formulas uniquely determine every arrow.
Source: det-sp-p1-trace, clause 3 (blueprint: det-sp-p1-trace). -/
@[irreducible]
def SpP1DiagonalIntegrals (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (b : SpP1TwistedFamily A N hA) : Prop :=
  ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
    ∃ (hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible)
      (κ : Ext
        ((Etale.lowerStar (ModuleCat.{u + 1} A)
          (pullback.diagonal (ProjectiveLine S ↘ S))).obj
            (Etale.ordinaryFiniteConstant A (ProjectiveLine S)))
        (Scheme.finiteEtaleTateLine
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2)
      (cΔ : GeoCartierClass A N hA (pullback.diagonal (ProjectiveLine S ↘ S)))
      (α : ∀ a : Bool, geoP1Unit A (ProjectiveLine S) ⟶
        (geoP1Pushforward A (Etale.projectiveLineDiagonalProjection S a)).obj
          ((geoP1Pushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
            (geoP1Unit A (ProjectiveLine S))))
      (δ : (geoP1Pushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (geoP1Unit A (ProjectiveLine S)) ⟶
        geoP1Twist A N hA
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) 1 2)
      (τ : ∀ a : Bool,
        (geoP1Pushforward A (Etale.projectiveLineDiagonalProjection S a)).obj
          (geoP1Twist A N hA
            (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) 1 2) ⟶
          geoP1Unit A (ProjectiveLine S)),
      Etale.SupportedKummerBoundary A N hA (pullback.diagonal (ProjectiveLine S ↘ S)) hI
        ((map_natCast ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
          (ProjectiveLine S ↘ S)).appTop.hom N) ▸
            hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
              (ProjectiveLine S ↘ S)).appTop.hom) κ ∧
      SpP1CartierCompatibility
        (comparisonUpperStar (ModuleCat.{u + 1} A)
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
        (geoCartierSourceComparison A (pullback.diagonal (ProjectiveLine S ↘ S))) κ cΔ ∧
      (∃ hE : PreservesFiniteColimits
          (lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))),
        CartierDerivedCompatibility (hF := hE)
          (lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S)))
          (geoCartierConstant A (ProjectiveLine S))
          (geoCartierLine A N hA
            (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
          (cartierUnitSingleIso A (ProjectiveLine S))
          (cartierShiftSingleIso
            (comparisonUpperStar (ModuleCat.{u + 1} A)
              (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
            (Scheme.finiteEtaleTateLine
              (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA))
          cΔ δ) ∧
      HEq (α false)
        ((rightDerivedLowerStarId (ModuleCat.{u + 1} A) (ProjectiveLine S)).inv.app
            (geoP1Unit A (ProjectiveLine S)) ≫
          (rightDerivedLowerStarFactor (ModuleCat.{u + 1} A)
            (pullback.diagonal_fst (ProjectiveLine S ↘ S))).inv.app
              (geoP1Unit A (ProjectiveLine S))) ∧
      HEq (α true)
        ((rightDerivedLowerStarId (ModuleCat.{u + 1} A) (ProjectiveLine S)).inv.app
            (geoP1Unit A (ProjectiveLine S)) ≫
          (rightDerivedLowerStarFactor (ModuleCat.{u + 1} A)
            (pullback.diagonal_snd (ProjectiveLine S ↘ S))).inv.app
              (geoP1Unit A (ProjectiveLine S))) ∧
      ∀ a : Bool,
        IsIso (α a) ∧
        HEq (τ a)
          ((geoP1Pushforward A (Etale.projectiveLineDiagonalProjection S a)).map
                ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
                  (Etale.projectiveLineDiagonalChart S a).val.hom).homEquiv
                    (geoP1Twist A N hA
                      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) 1 2)
                    ((geoP1Pullback A (Etale.projectiveLineDiagonalChart S a).val.hom).obj
                      (geoP1Twist A N hA
                        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) 1 2)) (𝟙 _)) ≫
              (rightDerivedLowerStarFactor (ModuleCat.{u + 1} A)
                (Etale.projectiveLineDiagonalChart S a).property).hom.app
                  ((geoP1Pullback A (Etale.projectiveLineDiagonalChart S a).val.hom).obj
                    (geoP1Twist A N hA
                      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) 1 2)) ≫
              (geoP1Pushforward A (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).map
                (geoP1TwistPullback A N hN hA (Etale.projectiveLineDiagonalChart S a).val.hom
                  ((map_natCast ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
                    (ProjectiveLine S ↘ S)).appTop.hom N) ▸
                      hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
                        (ProjectiveLine S ↘ S)).appTop.hom) 1 2).hom ≫
              geoP1Trace A N hA (ProjectiveLine S)
                (b (ProjectiveLine S)
                  ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
                    hS.map (ProjectiveLine S ↘ S).appTop.hom))) ∧
        HEq (α a ≫
          (geoP1Pushforward A (Etale.projectiveLineDiagonalProjection S a)).map δ ≫ τ a)
          (𝟙 (geoP1Unit A (ProjectiveLine S)))

/-- The full projective-line statement, including its arbitrary-base consequence.
All existential maps have their exact canonical formulas specified above.
Source: det-sp-p1-trace, clauses 1--3 (blueprint: det-sp-p1-trace). -/
def SpP1TraceStatement (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) : Prop :=
  ∃ (c : SpP1ChernFamily A N hA) (b : SpP1TwistedFamily A N hA)
    (d : SpP1DecompositionFamily A N hA),
    SpP1BaseTraceConditions A N hN hA c b d ∧
    SpP1DiagonalIntegrals A N hN hA b

/-- The projective-line component construction, separated from the diagonal clause.
Source: det-sp-p1-trace, clauses 1--2 (blueprint: lem-sp-p1-base-trace-families). -/
theorem exists_spP1BaseTraceConditions (ℓ : ℕ) (hℓ : ℓ.Prime) (n : ℕ) (hn : 0 < n)
    [Finite (ULift.{u + 1} (ZMod (ℓ ^ n)))] :
    ∃ c : SpP1ChernFamily (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
      (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)),
      ∃ b : SpP1TwistedFamily (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
        (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)),
      ∃ d : SpP1DecompositionFamily (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
          (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)),
          SpP1BaseTraceConditions (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
            (pow_pos hℓ.pos n)
            (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)) c b d := by
  sorry

/-- The diagonal integral clause for normalized projective-line families.
Source: det-sp-p1-trace, clause 3 (blueprint: lem-sp-p1-diagonal-integrals-family). -/
theorem spP1DiagonalIntegrals_of_twisted (ℓ : ℕ) (hℓ : ℓ.Prime) (n : ℕ) (hn : 0 < n)
    [Finite (ULift.{u + 1} (ZMod (ℓ ^ n)))]
    (c : SpP1ChernFamily (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
      (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)))
    (b : SpP1TwistedFamily (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
      (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)))
    (d : SpP1DecompositionFamily (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
      (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)))
    (_hbase : SpP1BaseTraceConditions (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
      (pow_pos hℓ.pos n)
      (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)) c b d) :
    SpP1DiagonalIntegrals (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)
      (pow_pos hℓ.pos n)
      (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)) b := by
  sorry

set_option linter.style.haveILetI false in
theorem proEtale_projectiveLine_trace (ℓ : ℕ) (hℓ : ℓ.Prime) (n : ℕ) (_hn : 0 < n) :
    @SpP1TraceStatement (ULift.{u + 1} (ZMod (ℓ ^ n))) inferInstance
      (Finite.of_equiv (ZMod (ℓ ^ n))
        (h := @Finite.of_fintype _ (@ZMod.fintype (ℓ ^ n)
          ⟨ne_of_gt (pow_pos hℓ.pos n)⟩)) Equiv.ulift.symm)
      (ℓ ^ n) (pow_pos hℓ.pos n)
      (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (ℓ ^ n))) (ℓ ^ n)) := by
  letI : Finite (ULift.{u + 1} (ZMod (ℓ ^ n))) :=
    Finite.of_equiv (ZMod (ℓ ^ n))
      (h := @Finite.of_fintype _ (@ZMod.fintype (ℓ ^ n)
        ⟨ne_of_gt (pow_pos hℓ.pos n)⟩)) Equiv.ulift.symm
  obtain ⟨c, b, d, hbase⟩ := exists_spP1BaseTraceConditions ℓ hℓ n _hn
  exact ⟨c, b, d, hbase,
    spP1DiagonalIntegrals_of_twisted ℓ hℓ n _hn c b d hbase⟩

end AlgebraicGeometry.ProEtale
