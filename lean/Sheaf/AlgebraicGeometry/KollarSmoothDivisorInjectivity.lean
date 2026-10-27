module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-!
# Kollar injectivity for a smooth zero divisor

Source: Mihnea Popa, Kodaira dimension of algebraic varieties, section 1.6,
Theorem 1.6.6, printed pages 26--27; characteristic-zero scope on page 22.
(blueprint: lem-sfb-kollar-smooth-divisor-injectivity)

The canonical module is the top exterior power of relative differentials.
The section is represented by its associated morphism from the tensor unit.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

set_option autoImplicit false

/-- Multiplication by a nonzero section of a tensor power of an invertible module,
whose zero scheme is smooth, is injective on every cohomology group after tensoring
with the canonical module. The zero scheme may be empty. No positivity is assumed.

Source: Popa, Kodaira dimension of algebraic varieties, Theorem 1.6.6 and proof,
printed pages 26--27, with the characteristic-zero convention of section 1.6, page 22.
(blueprint: lem-sfb-kollar-smooth-divisor-injectivity)

Proof:
1. For an empty zero scheme, the local coefficients of the section are units,
   so multiplication is an isomorphism. Otherwise integrality and nonvanishing
   make those coefficients nonzerodivisors, identifying the divisor ideal with
   the negative m-th power of the line bundle.
2. The cyclic root cover is smooth and projective, without a connectedness
   assumption. Its character decomposition identifies the character-one block
   of the first Hodge differential with the logarithmic connection on L inverse.
   The first Hodge differential vanishes on cohomology in characteristic zero.
3. Locally the connection sends b to db + (b/m) du/u. Residue sends this to b/m
   on the divisor. Thus restriction is m times the residue of the connection,
   and its map on every cohomology group is zero.
4. The short exact sequence from the negative (m+1)-st power of L into
   L inverse, then onto its restriction to the divisor, gives surjectivity
   on cohomology from the negative (m+1)-st power to L inverse in every degree.
5. Functorial Serre duality transposes that surjection to the asserted injection
   in degrees at most n: the dual sheaf map is multiplication by the same section.
   For degrees above n the source cohomology group vanishes.

The displayed composite inserts the section using the right unitor, tensors
with it, and reassociates. On local tensors it sends w tensor l to
w tensor (l tensor s), giving exactly local multiplication by the section. -/
theorem kollar_smooth_divisor_injectivity
    (F : Type u) [Field F] [IsAlgClosed F] [CharZero F]
    (Y : Scheme.{u}) (f : Y ⟶ Spec (.of F)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsProjective f] [GeometricallyIntegral f]
    (L : Y.Modules) [L.IsInvertible] (m : ℕ) (hm : 2 ≤ m)
    (s : 𝟙_ Y.Modules ⟶ L.tensorPow m) (hs : s ≠ 0)
    (hD : Smooth (s.zeroLocus.subschemeι ≫ f)) (j : ℕ) :
    Function.Injective
      ((RingedSpace.moduleCohomology Y.toRingedSpace j).map
        ((ρ_ (Scheme.Modules.exteriorSheaf f.relativeDifferentials n ⊗ L)).inv ≫
          ((Scheme.Modules.exteriorSheaf f.relativeDifferentials n ⊗ L) ◁ s) ≫
          (α_ (Scheme.Modules.exteriorSheaf f.relativeDifferentials n)
            L (L.tensorPow m)).hom)) := by
  sorry

end AlgebraicGeometry
