/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportStrictScalarCompositionPrelude

/-! # Composition of normalized reduction balancings -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (j : F →ₐ[ℚ_[l]] L)

/-- Reduction balancing composes before applying any proper/open image or support model.
Source: Stacks 03EK, 06YY, 0940; support realization, reduction-balancing step.
(blueprint: lem-pur-scalar-reduction-balancing-composition).
Proof: compose the ordinary balancings and the two scalar associators. On the local
pure tensors generating the twice-extended reduction, both composites send
`d ⊗ (b ⊗ (1 ⊗ x))` to `1 ⊗ (d ⊗ (b ⊗ x))`, followed by multiplication of the
scalar factors. The retained index equality is `h * (e * (n + 1)) = (h * e) * (n + 1)`;
positivity cancels the predecessor/successor pairs. The generator criterion gives
ordinary natural-transformation equality, including all tower transitions. Apply
this identity degreewise and localize. The source and target universal counits,
and their normalization for completed tensor composition, identify the composite
with the direct reduction balancing by `reductionBalancing_existsUnique`.
No finite-evaluation faithfulness or inverse limit is used. -/
theorem reductionBalancing_composition (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SF : CoefficientDerivedSystemCalculus.{u, u} l F W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (e h : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (hh : PurCompactSupport.Ramification l F L j h) (hhpos : 1 ≤ h)
    (M : DerivedCategory (scalarReductionSource l E W)) :
    (compositionTower l E F i L j W).hom.app ((reduction l E W SE).obj M) ≫
        (reductionBalancing l E L (j.comp i) W SE SL (h * e)
          (compositionRamification l E F i L j e h he hh)
          (one_le_mul hhpos hepos)).hom.app M =
      (T l F L j W).map ((reductionBalancing l E F i W SE SF e he hepos).hom.app M) ≫
        (compositionSelection l F L j W e).hom.app
          ((reduction l F W SF).obj
            ((pbcDerivedExtend (completedCoefficientMap l E F i W)).obj M)) ≫
        (subsequence l L W e).map
          ((reductionBalancing l F L j W SF SL h hh hhpos).hom.app
            ((pbcDerivedExtend (completedCoefficientMap l E F i W)).obj M)) ≫
        (compositionRetained l L W e h hepos hhpos).hom.app
          ((reduction l L W SL).obj
            ((pbcDerivedExtend (completedCoefficientMap l F L j W)).obj
              ((pbcDerivedExtend (completedCoefficientMap l E F i W)).obj M))) ≫
        (subsequence l L W (h * e)).map
          ((reduction l L W SL).map ((compositionCompleted l E F i L j W).hom.app M)) := by
  sorry

end WeilConjectures.PurStrictScalar
