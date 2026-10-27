module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.RingTheory.KoszulTensorConeCoordinates

/-! # Multiplying the last elements of H₁-regular tuples

Source: Stacks Project, More on Algebra, Tag 062G, lemma-mult-koszul-regular,
clause (1), specialized to the coefficient module `R`.
(blueprint: lem-per-h1-koszul-last-product).
-/

@[expose] public section

universe u

namespace ExteriorAlgebra

open CategoryTheory.Limits

/-- Vanishing of first Koszul homology for `(h, f)` and `(h, g)` implies its vanishing
for `(h, f * g)`, including an empty prefix and the zero ring.
Source: Stacks Project, More on Algebra, Tag 062G, lemma-mult-koszul-regular (1),
with coefficient module `R` (blueprint: lem-per-h1-koszul-last-product).

Proof:
1. Identify each complex tensored with `R` with the original complex by
   `x ⊗ a ↦ a • x`, inverse `x ↦ x ⊗ 1`. Bilinearity and linearity of the
   differential show that these maps identify cycles, boundaries and homology
   (def-weil-pbc-module-tensor-product, def-weil-pbc-module-chain-complex-homology).
2. Put `A = K(h) ⊗ R` and `B_t = K(h,t) ⊗ R`. Apply
   lem-weil-pbc-koszul-tensor-cone-coordinates with coefficient module `R` to
   `t = f, g, f*g`. The degree-zero, one and two identifications give
   `D₁(x,y) = d x + t • y` and `D₂(u,v) = (d u + t • v, -d v)`.
3. For a cycle `(x,y)` in `B_(fg)`, the pair `(x,f • y)` is a cycle in `B_g`.
   The second vanishing hypothesis gives `u,v` with `x = d u + g • v` and
   `f • y = -d v`, by kernel-modulo-image homology.
4. Now `(v,y)` is a cycle in `B_f`. The first hypothesis gives `w,q` with
   `v = d w + f • q` and `y = -d q`.
5. Linearity and commutativity yield `x = d (u + g • w) + (f*g) • q`, so
   `(x,y) = D₂(u + g • w,q)` is a boundary. Thus first homology vanishes;
   transport back using step 1. For an empty prefix the positive terms of `A`
   are zero, and the same argument applies; no cancellation or properness is used. -/
theorem koszul_h1_last_mul {R : Type u} [CommRing R]
    (s : ℕ) (h : Fin s → R) (f g : R)
    (hf : IsZero ((koszulComplex R (s + 1) (Fin.snoc h f)).homology 1))
    (hg : IsZero ((koszulComplex R (s + 1) (Fin.snoc h g)).homology 1)) :
    IsZero ((koszulComplex R (s + 1) (Fin.snoc h (f * g))).homology 1) := by
  sorry

end ExteriorAlgebra
