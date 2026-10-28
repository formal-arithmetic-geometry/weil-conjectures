module

public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.IntegralSystemReductionFullyFaithful

/-!
# Coherent reduction of the integral braiding scalar-extension square

Source: literature/stacks-project/sites-cohomology.tex, Tag 0FPQ
(blueprint: lem-pur-integral-braiding-scalar-extension-square-reduced).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/--
The scalar-extension square for the integral braiding becomes equal after coherent
reduction. This is the finite-stage signed-swap assertion assembled through the
normalized reduction systems.

Source: literature/stacks-project/sites-cohomology.tex, Tag 0FPQ, signed total symmetry;
Bhatt--Scholze, Lemma 3.5.7.
Proof: choose flat-term K-flat representatives, compute the scalar-extension map on
homogeneous tensors, and assemble the compatible quotient-level equalities. The
normalization equations identify the resulting system maps with the reductions of the
two displayed composites.
(blueprint: lem-pur-integral-braiding-scalar-extension-square-reduced).
-/
theorem reducedIntegralBraidingScalarExtensionSquare
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :
    (integralSystemReduction l L W).map (
        (sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map
          ((pullbackTensorIntegralBraiding l E W M N).hom) ≫
          (integralTensorScalarComparison l E L ι W N M).hom) =
      (integralSystemReduction l L W).map (
        (integralTensorScalarComparison l E L ι W M N).hom ≫
          (pullbackTensorIntegralBraiding l L W
            ((sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M)
            ((sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj N)).hom) := by
  sorry

end WeilConjectures
