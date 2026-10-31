/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGamma
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Domains of the ordinary tower tensor adjoint

Source: latest blueprint tower-geometric gamma proof, clause (2).
(blueprint: lem-sp-tower-tensor-adjoint-domains).

This extracts only the domain and inverse-projection witnesses. It asserts no
retagging, counit-comparison, transpose-comparison, or orientation equation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerTensorRetagging

variable (P : PurityFiniteSetting.{u})
  (b : SpTowerShriek.Base P.coefficients.l P.extension)
  (o : SpTowerShriek.Operations P.coefficients.l P.extension b)
  (q : SpTowerCalculus.Coordinates P.coefficients.l P.extension b)

/-- The tensor source belongs to the uniform constructible finite-Tor domain and
its specified projection is invertible, for any given exceptional adjunction.
The tensor models and the membership of the actual coefficient unit are conclusions.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md, (2),
and the domain-witness part of
lem-pur-tower-tensor-transpose-ground-field-retagging, proof Step 3.
(blueprint: lem-sp-tower-tensor-adjoint-domains).

Proof:
1. The sequence-site K-flat models give the normalized signed symmetry and scalar
unit constraints of TensorData on X and Y. The coefficient unit has constructible
levels and common cohomological and Tor interval [0,0], hence belongs to C_Y.
2. The chart description and uniqueness of the representing pair in
 det-sp-tower-gluing identify the given G with the exceptional adjoint constructed
there, preserving its counit. Changing compactifications uses the canonical
compact-support comparison. Thus G applied to the coefficient unit has the same
uniform local shifted rank-one descriptions as that constructed adjoint.
3. For K in C_Y choose its common cohomological and Tor intervals. Smooth pullback
preserves the Tor interval and constructibility. Tensor with the shifted locally
free rank-one description of G(unit) translates those intervals by -2d. The
bounds are independent of the coefficient exponent. This gives membership of the
actual tensorSource, after the inverse section-preserving realization.
4. At each finite level the specified compactification projection is the ordinary
finite projection formula, using both bounded etale-origin inputs. The evaluation
comparisons in det-sp-tower-shriek-levels identify it with the displayed tower
projection. Each level is invertible, so conservativity makes that projection
invertible in the ordinary tower derived category. None of these arguments assumes
normalization of K or a chosen orientation map. -/
theorem tensor_adjoint_domains
    (X Y : Over (Spec (CommRingCat.of P.field.k))) (f : X ⟶ Y) (d : ℕ)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated f.left] [SmoothOfRelativeDimension d f.left]
    (c : Compactification f.left)
    (hF : ∀ M : SpTowerCalculus.C P.coefficients.l P.extension b q X.left,
      spConstructibleTorTowers P.coefficients.l P.extension Y.left (q.abelian Y.left)
        ((SpTowerCalculus.F P.coefficients.l P.extension b o q c).obj M.obj))
    (G : SpTowerCalculus.C P.coefficients.l P.extension b q Y.left ⥤
      SpTowerCalculus.C P.coefficients.l P.extension b q X.left)
    (adj : SpTowerGluing.support P.coefficients.l P.extension b o q c hF ⊣ G) :
    ∃ tx : SpTowerP1.TensorData P.coefficients.l P.extension b X.left,
    ∃ ty : SpTowerP1.TensorData P.coefficients.l P.extension b Y.left,
    ∃ hU : spConstructibleTorTowers P.coefficients.l P.extension Y.left (q.abelian Y.left)
      (SpTowerGamma.originalUnit P.coefficients.l P.extension b q Y.left),
    ∀ K : SpTowerCalculus.C P.coefficients.l P.extension b q Y.left,
      spConstructibleTorTowers P.coefficients.l P.extension X.left (q.abelian X.left)
        ((SpTowerCalculus.realization P.coefficients.l P.extension b X.left
          (q.abelian X.left)).inverse.obj
          ((SpTowerGamma.tensorSource P.coefficients.l P.extension b o q f.left
            ((SpTowerGamma.exceptional P.coefficients.l P.extension b q G).obj
              ⟨SpTowerGamma.originalUnit P.coefficients.l P.extension b q Y.left,
                hU⟩)).obj K)) ∧
      IsIso (SpTowerShriek.projection P.coefficients.l P.extension b o c
        ((SpTowerGamma.exceptional P.coefficients.l P.extension b q G).obj
          ⟨SpTowerGamma.originalUnit P.coefficients.l P.extension b q Y.left, hU⟩)
        ((SpTowerGamma.realization P.coefficients.l P.extension b q Y.left).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerTensorRetagging
