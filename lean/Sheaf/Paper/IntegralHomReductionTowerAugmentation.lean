/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralHomReductionModels

/-! # Augmentation compatibility for integral Hom reduction towers

Source: blueprint order 2478, proof steps 4-8; Stacks Tags 07A6, 08J9 and 08TC
(blueprint: lem-sf-integral-hom-tower-components-augmentation).

The normalized finite comparison preserves the degree-zero quotient unit. This
intermediate statement isolates the augmentation equation after a compatible
family of component isomorphisms has been supplied.
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

/--
A transition-compatible family of normalized finite Hom comparisons preserves the
canonical quotient augmentations. This is the augmentation part of
`reductionTower_components`; its proof is the naturality calculation for the
degree-zero quotient unit, followed by resolution independence.

Source: blueprint order 2478, proof steps 4-8; Stacks Tags 07A6, 08J9 and 08TC
(blueprint: lem-sf-integral-hom-tower-components-augmentation).
-/
theorem reductionTower_components_augmentation
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
    ∀ (θ : ∀ n : ℕ, H.obj ((integralReductionTower l E Y D hl P).obj (op n)) ≅
        (integralReductionTower l E Y D hl P').obj (op n)),
      (∀ n : ℕ,
        H.map ((integralReductionTower l E Y D hl P).map (homOfLE n.le_succ).op) ≫
            (θ n).hom =
          (θ (n + 1)).hom ≫
            (integralReductionTower l E Y D hl P').map (homOfLE n.le_succ).op) →
      ∀ n : ℕ,
        e.inv ≫ (integralReductionTowerCone l E Y D hl q' hq').π.app (op n) =
          H.map ((integralReductionTowerCone l E Y D hl q hq).π.app (op n)) ≫
            (θ n).hom := by
  sorry

end WeilConjectures.IntegralHom
