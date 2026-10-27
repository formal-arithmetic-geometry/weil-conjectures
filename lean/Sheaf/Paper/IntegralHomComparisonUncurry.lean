/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralHomReductionComparison
public import Sheaf.Paper.IntegralHomReductionModels

/-! # Uncurried normalization of integral Hom comparison

The equality of uncurried maps is the representative-level normalization step in the
independence proof for integral Hom comparison maps.
(blueprint: lem-sfb-integral-hom-comparison-normalization)
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe d u
open CategoryTheory Opposite
namespace WeilConjectures

/-- The canonical comparison has the normalized uncurried map prescribed by any
`ReductionPresentation`.  This is the representative normalization part of the
comparison-independence argument; it is proved by comparing the two tensor models on
K-flat representatives, using the signed total tensor and the normalized evaluation.
Source: Stacks Tags 06YY and 08J7; the normalization paragraphs of the integral Hom
reduction construction (blueprint: lem-sfb-integral-hom-comparison-normalization).
-/
theorem integralHomComparison_uncurry_eq
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl))
    (m : IntegralHom.ReductionPresentation l E X D hl a n)
    (K L : completedIntegralDerivedCategory l E X D hl) :
    ((m.target.adjunction
      ((integralDerivedReduction l E X D hl n).obj K)).homEquiv _ _).symm
      (integralHomReductionComparison D l hl E X n K L) =
      m.mu.inv.app
          (K,
            (homReductionHom (completedIntegralCommRingSheaf l E X D hl)).obj (op K, L)) ≫
        (integralDerivedReduction l E X D hl n).map
          ((a.adjunction K).counit.app L) := by
  sorry

end WeilConjectures
