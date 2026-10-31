/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemCofinalData

/-! # Factor and evaluation data for cofinal repetition

Source: Zheng, Construction 4.1 and the paragraph preceding Lemma 4.10.
(blueprint: lem-pur-etale-cofinal-factor-evaluation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- Selected-extension factors and their evaluation diagrams exist once the
repetition/support package is fixed.
Source: Zheng, Construction 4.1, printed pp. 21--23.

Proof: identify the repeated tower at `m` with the selected component at the
least index `t(m)`. The ordinary tensor left extension and the repeated
extension are left adjoints of the same actual cofinal restriction, with the
same unit on selected sections. Adjoint uniqueness gives the ordinary factors;
the normalized universal left-derived comparisons give their derived fields.
Evaluating the block geometric square and the open-extension square gives the
three displayed equations.
(blueprint: lem-pur-etale-cofinal-factor-evaluation) -/
theorem etaleCofinalFactorEvaluation_nonempty
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (T : Theory c l) (B : Coefficients.{u} l) (r : ℕ ↪o ℕ)
    (Lx : CofinalExtension X B r) (Ly : CofinalExtension Y B r)
    (R : CofinalRepeatSupport T B r) :
    ∃ (Fx : CofinalFactor X B r Lx R.x (T.scalarX (cofinalCoefficient B r)))
      (Fy : CofinalFactor Y B r Ly R.y (T.scalarY (cofinalCoefficient B r)))
      (x : ∀ m : ℕ,
        R.x.R.mapDerivedCategory ⋙ (T.evaluationX (cofinalRepeated B r) m).E ≅
          (T.evaluationX (cofinalCoefficients B r)
            (SheafOfModules.systemNextSelected r m)).E)
      (y : ∀ m : ℕ,
        R.y.R.mapDerivedCategory ⋙ (T.evaluationY (cofinalRepeated B r) m).E ≅
          (T.evaluationY (cofinalCoefficients B r)
            (SheafOfModules.systemNextSelected r m)).E),
      (∀ (m : ℕ) (N : Derived X (cofinalCoefficients B r).rings),
        (T.evaluationX B m).E.map (Fx.derived.hom.app N) ≫
          (T.scalarEvaluationX (cofinalCoefficient B r) m).iso.hom.app
            (R.x.R.mapDerivedCategory.obj N) ≫
          (scalarExtension ((cofinalCoefficient B r).app (op m)).hom X).map
            ((x m).hom.app N) =
        (Lx.level m (T.evaluationX B m)
          (T.evaluationX (cofinalCoefficients B r)
            (SheafOfModules.systemNextSelected r m))).hom.app N) ∧
      (∀ (m : ℕ) (N : Derived Y (cofinalCoefficients B r).rings),
        (T.evaluationY B m).E.map (Fy.derived.hom.app N) ≫
          (T.scalarEvaluationY (cofinalCoefficient B r) m).iso.hom.app
            (R.y.R.mapDerivedCategory.obj N) ≫
          (scalarExtension ((cofinalCoefficient B r).app (op m)).hom Y).map
            ((y m).hom.app N) =
        (Ly.level m (T.evaluationY B m)
          (T.evaluationY (cofinalCoefficients B r)
            (SheafOfModules.systemNextSelected r m))).hom.app N) ∧
      (∀ (m : ℕ) (N : Derived X (cofinalCoefficients B r).rings),
        (T.evaluationY (cofinalRepeated B r) m).E.map (R.kappa.hom.app N) ≫
          (y m).hom.app ((T.support (cofinalCoefficients B r)).F.obj N) ≫
          (T.supportEvaluation (cofinalCoefficients B r)
            (SheafOfModules.systemNextSelected r m)).iso.hom.app N =
        (T.supportEvaluation (cofinalRepeated B r) m).iso.hom.app
            (R.x.R.mapDerivedCategory.obj N) ≫
          (rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} ((cofinalRepeated B r).rings.obj (op m))) c).map
            ((x m).hom.app N)) := by sorry

end AlgebraicGeometry.Etale.SystemProjection
