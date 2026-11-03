/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionReductionSquare

/-! # Native consumer of the normalized reduction square

Source: current blueprint, sec-smooth-purity,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, (2)--(3)
(blueprint: lem-sp-complete-projection-mate-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Descent of the native compactification projection through its actual reduction units.
Source: blueprint proof (3), tower projection followed by derived inverse limit
(blueprint: lem-sp-complete-projection-mate-descent).

Proof:
1. Apply `projection_reduction_square`, and cancel the invertible target coordinate.
This identifies reduction of the native projection with `transportedProjection`.
2. Naturality of the actual reduction/limit unit gives pi;eta_U = eta_V;L(r(pi)).
Substitute step 1 and cancel the invertible unit at U, giving the displayed formula.
3. The proper and open system projection factors, and both coordinates, are isomorphisms.
Their composite is an isomorphism. Conjugate its inverse by the actual units to obtain
an inverse of pi; the two compositions are identities by functoriality of L.
4. The native proper and open projection maps and pullback compositor are natural in
both inputs. Their composite has exactly the last displayed bifunctoriality square.
No faithfulness of evaluations, nor a monoidal structure on total limit, is used. -/
theorem complete_projection_mate_descent (m : DescentModels l E)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpl : p ≠ l)
    (X Y : Over (Scheme.Spec.obj (op (CommRingCat.of k))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (AX : Limit l E X.left (m.abelian X.left) (m.red X.left))
    (AZ : Limit l E c.Z (m.abelian c.Z) (m.red c.Z))
    (AY : Limit l E Y.left (m.abelian Y.left) (m.red Y.left))
    (M : Integral l E X.left) (K : Integral l E Y.left)
    (hbM : IsIso (reconstruction l E m c AX AZ AY M))
    (hbH : IsIso (reconstruction l E m c AX AZ AY (inputTensor l E m f.left M K)))
    (hOpen : IsIso (systemOpenInverse l E m c.i ((red l E m X.left).obj M)
      ((VaryingRing.G (rings l E) (transitions l E) c.g).obj ((red l E m Y.left).obj K))))
    (_hProper : IsIso (((systemProperProjection l E m c.g).app
      ((VaryingRing.J (rings l E) (transitions l E) c.i).obj ((red l E m X.left).obj M))).app
        ((red l E m Y.left).obj K)))
    (hUnitU : IsIso ((adj l E m Y.left AY).unit.app
      ((integralImage l E c).obj (inputTensor l E m f.left M K))))
    (hUnitV : IsIso ((adj l E m Y.left AY).unit.app ((integralImage l E c).obj M ⊗ K))) :
    let U := (integralImage l E c).obj (inputTensor l E m f.left M K)
    let V := (integralImage l E c).obj M ⊗ K
    let theta := transportedProjection l E m c AX AZ AY M K hbM hbH hOpen
    let pi := CondensedRing.exceptionalProjectionMorphismOfCompactification
      (spIntegralCondensed l E) c M K
    pi = (adj l E m Y.left AY).unit.app V ≫ (lim l E m Y.left AY).map theta ≫
      inv ((adj l E m Y.left AY).unit.app U) ∧
    ∃ (t : (red l E m Y.left).obj V ≅ (red l E m Y.left).obj U) (e : V ≅ U),
      t.hom = theta ∧ e.hom = pi ∧
      e.inv = (adj l E m Y.left AY).unit.app U ≫
        (lim l E m Y.left AY).map t.inv ≫ inv ((adj l E m Y.left AY).unit.app V) ∧
      ∀ (M' : Integral l E X.left) (K' : Integral l E Y.left)
        (v : M ⟶ M') (w : K ⟶ K'),
        ((integralImage l E c).map v ⊗ₘ w) ≫
          CondensedRing.exceptionalProjectionMorphismOfCompactification
            (spIntegralCondensed l E) c M' K' =
        pi ≫ (integralImage l E c).map (v ⊗ₘ (ringedPull l E f.left).map w) := by
  sorry

end AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent
