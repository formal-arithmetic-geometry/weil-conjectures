/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.SystemProperOpenScalarData

/-! # Composition and identity for the scalar inverse-image comparison

Source: Stacks 03CZ, 03D7, 07A7; Zheng, Section 5, Lemma 5.13.
(blueprint: lem-sf-scalar-inverse-image-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen.Scalar

variable (A B : ℕ → CommRingCat.{u + 1})
  (a : ∀ n : ℕ, A (n + 1) ⟶ A n) (b : ∀ n : ℕ, B (n + 1) ⟶ B n)
  (φ : ∀ n : ℕ, A n ⟶ B n)
  (hφ : ∀ n : ℕ, φ (n + 1) ≫ b n = a n ≫ φ n)
  (d : ℕ) (hd : 1 ≤ d) (e : Bases A B b φ d)

/-- The specified scalar inverse-image comparison preserves composition and identity.
Source: Stacks 03CZ, 03D7, 07A7; step 6 of the scalar-square argument.
Proof: before deriving, use the identity-on-sections normalization of
restrictionPush_existsUnique. Pasting its two restriction/direct-image squares
for v and w agrees with the single square for v ≫ w under pushComp, since
both maps are identity on every section. For an identity morphism the analogous
square agrees with pushId: both are induced by the same pullbackId map on the
site. Conjugation by the composed scalar and inverse-image adjunctions converts
these equalities into the two equations for ellOrdinary with pullComp and the
ordinary identity comparison. Apply the functors to complexes degreewise and
localize. The mapDerivedCategory composition and identity isomorphisms preserve
the pasted words, giving exactly the displayed pComp and pId equations.
This uses no properness, boundedness, or constructibility hypothesis.
(blueprint: lem-sf-scalar-inverse-image-coherence). -/
theorem scalarInverseImageCoherence :
    (∀ {X Y Z : Scheme.{u}} (v : X ⟶ Y) (w : Y ⟶ Z) (N : Derived A a Z),
      (ell A B a b φ hφ d hd e (v ≫ w)).hom.app N ≫
          (T A B a b φ hφ d hd e X).map ((pComp A a v w).hom.app N) =
        (pComp B b v w).hom.app ((T A B a b φ hφ d hd e Z).obj N) ≫
          (P B b v).map ((ell A B a b φ hφ d hd e w).hom.app N) ≫
          (ell A B a b φ hφ d hd e v).hom.app ((P A a w).obj N)) ∧
    (∀ (X : Scheme.{u}) (N : Derived A a X),
      (ell A B a b φ hφ d hd e (𝟙 X)).hom.app N ≫
          (T A B a b φ hφ d hd e X).map ((pId A a X).hom.app N) =
        (pId B b X).hom.app ((T A B a b φ hφ d hd e X).obj N)) := by sorry

end AlgebraicGeometry.ProEtale.SemilinearProperOpen.Scalar
