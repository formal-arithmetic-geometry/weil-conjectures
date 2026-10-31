/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurIntegralRepresentingPairData

/-! # Coordinate representing families

Source: blueprint integral adjunction, coordinate Hom chain and actual counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] WeilConjectures.integralExceptionalSystemDerived
attribute [-instance] WeilConjectures.integralExceptionalLevelDerived
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules
open WeilConjectures AlgebraicGeometry.Scheme
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
namespace WeilConjectures.PurIntegralRepresentingPair
open PurIntegralSupportComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)
  (G : EtaleTowerBrownAdjunction S) (H : BrownTowerComparison.FiniteEvaluation S G)
  (D : BrownTowerComparison.TransportData S G H)

/-- Finite normalization of the transported Brown counit, with the ordinary
etale exceptional lower bound retained.
Source: blueprint sk-prop-sp-integral-adjunction, final finite counit paragraph;
Zheng Lemmas 4.10 and 5.22 (blueprint: lem-pur-finite-coordinate-counit).

Proof: the bounded Brown theorem bounds the etale system G(Rnu_* C). Exact
etale evaluation and its canonical realization preserve this lower bound.
The recorded finite Brown comparison identifies it with the ordinary etale
exceptional object, after direct-evaluation and realization comparisons; these
are actual isomorphisms, so give the claimed bound. Evaluate counit_formula.
Cancel the evaluated invertible compactComparison and paste its recorded
compactComparison_evaluation equation. Substitute evaluation_def, the finite
Brown counit equation, and the realization-normalized finite counit equation.
Naturality moves the direct-evaluation isomorphism through the finite right
adjoint and its counit. The level site counit equation then identifies the final
site counit. The remaining isomorphisms, in precisely that order, are
finiteCoordinates; the remaining actual counit is finiteCounit. Composition
associativity and inverse cancellation give the displayed equality, with no
appeal to faithfulness of evaluation on derived morphisms. -/
theorem finiteCoordinateCounit
    (hD : BrownTowerComparison.Transport S G H D (finite := D.finite))
    (C : DerivedCategory (BrownTowerComparison.ProSystem Y
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)))
    (hC : D.siteY.Origin C)
    (hn : IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology Y)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)
      D.siteY.proEvaluation C)
    (hc : ∀ n, FiniteCoefficientAdjoints.ctf
      (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) Y
      ((D.siteY.realization n).derived.obj ((D.siteY.proEvaluation.evaluation n).obj C)))
    (hb : ∃ a : ℤ, ∀ n,
      ((BrownTowerComparison.finiteExceptional S G H D.siteX D.siteY n).obj
        ((D.siteY.proEvaluation.evaluation n).obj C)).IsGE a) :
    ∃ hbound : ∀ n : ℕ, letI := D.finite n
        DerivedCategory.TStructure.t.plus
          ((BrownTowerComparison.ordinaryFiniteRight
            (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
              (integralExceptionalUniformizer l E) n) c).obj
            ((FiniteCoefficientAdjoints.rnu _ Y).obj
              ((D.siteY.realization n).derived.obj
                ((D.siteY.proEvaluation.evaluation n).obj C)))),
      ∀ n, (D.siteY.realization n).derived.map
          ((D.siteY.proEvaluation.evaluation n).map (D.counit C hC hn hc hb)) =
        (D.compactEvaluation n).hom.app ((brown l E S G H D).obj C) ≫
          (FiniteCoefficientAdjoints.lower
            (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
              (integralExceptionalUniformizer l E) n) c).map
            ((D.siteX.realization n).derived.map ((D.evaluation n).hom.app C) ≫
              (finiteCoordinates l E S G H D hD n).hom.app
                ((D.siteY.proEvaluation.evaluation n).obj C)) ≫
          finiteCounit l E S G H D n C (hbound n) := by sorry

end WeilConjectures.PurIntegralRepresentingPair
