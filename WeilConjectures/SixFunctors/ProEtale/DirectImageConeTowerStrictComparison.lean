/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.DirectImageConeTowerNormalizationDefs

/-! # Strict direct-image comparison of the scalar cone tower -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived AdicCompletion.finiteRingMonoidalObject
  AdicCompletion.finiteRingCommutative AdicCompletion.finiteModulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Direct image commutes with the strict reduction cone tower, with its canonical
normalization on both summands.
Source: literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/prop-weil-pbc-direct-image-limits.proof.md, proof (2).
(blueprint: lem-weil-pbc-direct-image-cone-tower-strict-comparison).

Proof in words: denote ordinary module pullback and pushforward by L and R.
The point-scalar compatibility L(s_Y)=s_X gives R(s_X)=s_Y: transpose under
L ⊣ R and use naturality of the counit at s_X, followed by naturality of s_X
at that counit. Functoriality then proves compatibility with every positive
power. It gives an identity-component comparison from R of the scalar tower
to the scalar tower of R, and likewise the constant-tower comparison. These
comparisons intertwine the two complex power maps. Apply the additive-functor
mapping-cone comparison, followed by the cone isomorphism of this square.
The identity coordinates make its composites with inl and inr exactly the
two displayed equations, including constantPushIso. Cone-map composition
and naturality of the source/target comparisons establish naturality in I.
The construction takes place in complexes of towers, so the scalar-source
and constant-target comparisons already establish the (pi,1) transition
squares. Only finite biproducts occur in each degree, so no boundedness,
exactness of R, or K-injectivity is required. Zero modules, empty schemes,
identity f, and the positive exponent n+1 obey the same calculation. -/
theorem strictDirectImageConeTower_comparison_exists :
    ∃ e : strictRed l E X ⋙ (push l E f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      Functor.mapHomologicalComplex
        (CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f)
          (ComplexShape.up ℤ) ⋙ strictRed l E Y,
      IsStrictDirectImageConeTower l E f e := by
  sorry


end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
