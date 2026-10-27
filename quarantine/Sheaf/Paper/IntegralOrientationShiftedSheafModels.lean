/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U6
-/
module

public import Sheaf.Paper.IntegralAdjunctionBijection
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted

/-! # Shifted sheaf models for integral smooth orientation objects

Source: latest blueprint, tower-geometric-gamma proof (1) and
integral-adjunction-bijection, Purity paragraph.
(blueprint: lem-pur-integral-orientation-shifted-sheaf-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpIntegralOrientation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Z Y : Scheme.{u}}
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
  (d : ℕ) (w : SpChartAdmissibility.Twists l E X)
  (RX : SpReductionTower l E X (q.abelian X))
  (NX : SpNormalizedEquivalence l E X (q.abelian X) RX)
  (RY : SpReductionTower l E Y (q.abelian Y))
  (NY : SpNormalizedEquivalence l E Y (q.abelian Y) RY)
  (hF : ∀ M : SpTowerCalculus.C l E b q X,
    spConstructibleTorTowers l E Y (q.abelian Y)
      ((SpTowerCalculus.F l E b o q (SpTowerGamma.factorization j p)).obj M.obj))
  (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
  (a : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ G)
  (lv : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization j p) hF G a)
  (R : SpIntegralAdjunction.Realization l E b o q j p d w RX NX RY NY hF G a lv)

/-- The simultaneous reduction of the shifted integral Tate line and the tower
exceptional image of the integral unit are shifted degree-zero tower sheaves.

Source: latest blueprint, sec-smooth-purity, tower-geometric-gamma proof (1),
combined with twisted-pullback-reduction-tower at the coefficient unit.
(blueprint: lem-pur-integral-orientation-shifted-sheaf-models).

Proof: the simultaneous twisted-pullback reduction comparison identifies reduction
of the integral Tate line, including its shift, with the strict Tate coefficient
tower shifted by 2d. Pullback of the coefficient unit is the coefficient unit;
the completed tensor unitor identifies its tensor with the integral Tate line.
Use the given hT and hU to transport these identifications to the representatives
T and U. All these comparisons hold for entire strict systems, not merely for
individual derived levels. Twists are locally free module sheaves, so the
unshifted Tate tower is an object L of the abelian tower category. The diagonal
orientation of tower-gamma (1) identifies this same shifted Tate tower with the
exceptional tower image of the coefficient unit. Transport along the reduction
of hU and the unit comparison to obtain the target presentation (with W=L).
The ordered positive tensor presentation in tower-gamma is identified with the
single Tate sheaf and its shift by the signed-line tensor comparison. No map
from T to the exceptional object is used. The comparisons also hold when d=0
(the tensor unitors) or X is empty (the zero sheaf category).
-/
theorem shifted_sheaf_models
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (_iE : E →ₐ[Padic l] Ω)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [(j ≫ p).IsOver (Spec (.of D.k))] [SmoothOfRelativeDimension d (j ≫ p)]
    (T : sfIntegralConstructibleCategory l E X)
    (U : sfIntegralConstructibleCategory l E Y)
    (_hT : T.obj ≅ ((DerivedCategory.singleFunctor _ 0).obj
      (integralTwistLine l E X (d : ℤ)))⟦2 * (d : ℤ)⟧)
    (_hU : U.obj ≅ (DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))) :
    ∃ L W : spCoefficientTowers l E X,
      Nonempty
        (((SpIntegralAdjunction.reduce l E X (q.abelian X) RX R.reductionX).obj T).obj ≅
          ((@DerivedCategory.singleFunctor _ _ _ (q.abelian X).hasDerived 0).obj
            L)⟦2 * (d : ℤ)⟧) ∧
      Nonempty
        ((G.obj ((SpIntegralAdjunction.reduce l E Y (q.abelian Y) RY
          R.reductionY).obj U)).obj ≅
          ((@DerivedCategory.singleFunctor _ _ _ (q.abelian X).hasDerived 0).obj
            W)⟦2 * (d : ℤ)⟧) := by sorry

end AlgebraicGeometry.ProEtale.SpIntegralOrientation
