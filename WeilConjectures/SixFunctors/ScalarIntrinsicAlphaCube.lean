/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.SystemProperOpenScalarData

/-! # Scalar naturality of the intrinsic proper/open mate

Source: Zheng, Section 5, Lemma 5.13 and Constructions 5.14--5.15.
(blueprint: lem-sf-scalar-intrinsic-alpha-cube).
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

/-- Scalar extension commutes with the intrinsic inverse-image proper/open word.
Source: Zheng 5.13 and Constructions 5.14--5.15; Stacks 03DI, 0E8I, 0F7B.
This is the inverse-image cube of steps 2--4 of the scalar-square argument.
Proof: work first with ordinary strict systems on the ringed sequence site.
The restriction/direct-image comparison defining ellOrdinary is identity on
sections, so its left-adjoint conjugate is the usual pure-tensor comparison.
The inverse open mate defining beta is normalized by the open unit. Hence the
cartesian open base-change comparison and the open and pullback compositors
commute with these scalar comparisons, by the same unit transposition.
For the clopen square lift, restriction to its image and complementary open
identifies systems with a product. Scalar tensor acts on both factors, whereas
the intrinsic projector acts by (1,0); the two commute, including empty factors.
Substitute into alpha's cartesian-comparison/projector/compositor word.
Apply the exact functors termwise to complexes and localize the equality of
natural transformations. Exact localization preserves composition and inverses,
and its comparisons are precisely ell and beta by their definitions.
(blueprint: lem-sf-scalar-intrinsic-alpha-cube). -/
theorem scalarIntrinsicAlphaCube
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (i : W ⟶ Z) (r : U ⟶ W) (p : V ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (N : Derived A a W) :
    (P B b p).map ((beta A B a b φ hφ d hd e i).inv.app N) ≫
        (ell A B a b φ hφ d hd e p).hom.app ((J A a i).obj N) ≫
        (T A B a b φ hφ d hd e V).map ((alpha A a k r p i h).app N) =
      (alpha B b k r p i h).app ((T A B a b φ hφ d hd e W).obj N) ≫
        (J B b k).map ((ell A B a b φ hφ d hd e r).hom.app N) ≫
        (beta A B a b φ hφ d hd e k).inv.app ((P A a r).obj N) := by sorry

end AlgebraicGeometry.ProEtale.SemilinearProperOpen.Scalar
