/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.Paper.IntegralHomReductionModels
import Sheaf.Paper.IntegralHomModelsExist
import Sheaf.Paper.IntegralHomComparisonIsIso

/-! # Component comparisons for the integral Hom reduction tower

Source: blueprint order 2478, proof steps 4-8; Stacks Tags 07A6, 08J9 and 08TC
(blueprint: lem-sf-integral-hom-tower-components).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- The finite signed Hom comparisons respect consecutive quotient maps and the quotient
unit on fixed representatives. No product or completeness assertion occurs here, and
neither the representative nor its K-flat resolution is chosen by this theorem.

Source: blueprint order 2478, steps 4-8; Stacks Tags 07A6, 08J9 and 08TC
(blueprint: lem-sf-integral-hom-tower-components).

Proof: Use the normalized tensor presentations and the finite comparison_isIso at
exponent n+1. The coefficient extension/restriction adjunction identifies restricted
finite Hom with Hom over the completed ring into restricted coefficients. Compute
the input reductions on q and the output reductions on q'. Transport along e to
obtain the displayed components. On K-flat source and K-injective target models,
the finite comparison sends f tensor z to the function sending x to
(-1)^(degree(z)*degree(x)) f(x) tensor z. This formula is natural in the two-term
quotient complex. Apply it to the quotient chain map whose components are the
uniformizer and identity to obtain the consecutive-transition square. Apply it
to the degree-zero quotient unit to obtain the augmentation square. The scalar
unit and evaluation normalizations identify these with the actual recorded maps.
Resolution independence transports both squares to the fixed q and q'. This
uses arbitrary unbounded K and does not require any countable product. -/
theorem reductionTower_components
    (K : completedIntegralDerivedCategory l E Y D hl)
    (P G P' G' : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (q : P ⟶ G) (q' : P' ⟶ G')
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q')
    (e : DerivedCategory.Q.obj G' ≅
      (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj
        (op K, DerivedCategory.Q.obj G)) :
    let H := (Functor.curry.obj
      (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))).obj (op K)
    ∃ θ : ∀ n : ℕ, H.obj ((integralReductionTower l E Y D hl P).obj (op n)) ≅
        (integralReductionTower l E Y D hl P').obj (op n),
      (∀ n : ℕ,
        H.map ((integralReductionTower l E Y D hl P).map (homOfLE n.le_succ).op) ≫
          (θ n).hom = (θ (n + 1)).hom ≫
            (integralReductionTower l E Y D hl P').map (homOfLE n.le_succ).op) ∧
      ∀ n : ℕ, e.inv ≫ (integralReductionTowerCone l E Y D hl q' hq').π.app (op n) =
        H.map ((integralReductionTowerCone l E Y D hl q hq).π.app (op n)) ≫
          (θ n).hom := by sorry

end WeilConjectures.IntegralHom
