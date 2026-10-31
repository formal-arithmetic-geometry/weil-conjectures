/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseTensorPullbackRealizationData

/-! # Integral pullback normalization before rational naturality

Source: Bhatt--Scholze Remark 6.8.15; Stacks 07A4.
(blueprint: lem-real-integral-pullback-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme MonoidalCategory
open scoped TensorProduct MonoidalCategory
namespace WeilConjectures.LisseRealization
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Integral naturality of the normalized completion and scalar square, before
extending to arbitrary raw rational morphisms.
Source: Bhatt--Scholze Lemma 6.5.9, Remark 6.8.15; Stacks 0D6D and 07A4
(blueprint: lem-real-integral-pullback-normalization).

Proof: finite-type schemes over D.k are noetherian and finite dimensional, without
separatedness, and l is invertible. The ordinary-completed integral pullback theorem
makes the specified quotient-and-zero map eta invertible on constructible inputs.
For the two coefficient morphisms identify the scalar square by localization and
inverse image. The normalized ordinary comparison flattens iterated scalar tensors;
its inverse inserts one. Thus it carries the actual integral adjunction unit to
the rational unit with scalar one. Derive this comparison by the composition and
geometric two-isomorphism comparisons for ringed topoi, retaining their counit
square. Compose aX.integral, scalar extension of eta inverse, this derived square,
and the image of aY.integral inverse to obtain n.comparison. Each factor is natural
in integral derived morphisms, which proves the asserted naturality equation.
On a finite locally free single the K-flat counit computes ordinary pullback.
The completion map on a free chart sends a basis vector to its quotient vectors
and zero shifted component. Its inverse and the balanced scalar square therefore
preserve that basis. Take H0 and use the identity-normalized degree-zero comparison
to obtain b.comparison and n.heart. Finite locally free pullback preserves local
finite bases, giving b.preserves; naturality follows from the same derived square,
and its ordinary inverse is b.balance. This handles empty schemes, rank zero,
varying ranks and arbitrary, possibly non-k-linear scheme morphisms. -/
theorem integral_pullback_normalization {X Y : Base D l hl} (f : X.scheme ⟶ Y.scheme)
    (aX : At D l hl E X) (aY : At D l hl E Y) :
    ∃ (b : Along D l hl E f aX aY) (n : PullNormalized D l hl E f aX aY b),
      ∀ (K L : sfIntegralConstructibleCategory l E Y.scheme) (g : K ⟶ L),
        (pull D l hl E f ⋙ aX.J).map
            ((sfRationalConstructibleLocalization l E Y.scheme).map g) ≫
          (n.comparison L).hom =
        (n.comparison K).hom ≫
          (aY.J ⋙ ContinuousRational.derivedPull f (coefficientPull l E f)).map
            ((sfRationalConstructibleLocalization l E Y.scheme).map g) := by sorry

end WeilConjectures.LisseRealization
