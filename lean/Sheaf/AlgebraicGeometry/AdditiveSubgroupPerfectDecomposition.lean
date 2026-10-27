module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Topology.Connected.Basic

/-!
# Closed additive subgroups over a perfect field

Source: Milne, Algebraic Groups (2017), Definition 14.45, printed p.295, and
Proposition 14.52, printed p.297.
(blueprint: lem-sfb-additive-subgroup-perfect-decomposition)

Products are taken in the category of group schemes, including empty products.
The infinitesimal factors have the existing underlying scheme `alpha k (p ^ r)`.
Their group law is specified by requiring their inclusion into the additive group
to be a group homomorphism. This fixes coordinatewise addition, including on
nonreduced test algebras, without requiring characteristic `p ^ r` on the field.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every finite-type closed subgroup of a finite additive power over a perfect
field of positive characteristic is a product of an additive power, positive
Frobenius kernels, and a commutative finite etale group of prime-power order.

Source: Milne, Algebraic Groups (2017), Definition 14.45, printed p.295, and
Proposition 14.52, printed p.297.
(blueprint: lem-sfb-additive-subgroup-perfect-decomposition)

The isomorphisms `e` identify the infinitesimal factors with the explicit
schemes Spec(k[t]/(t^(p^r))). Compatibility of their inclusions with addition
specifies precisely the Hopf law t ↦ t⊗1+1⊗t, t ↦ 0, and t ↦ -t.

Proof:
1. The closed embedding makes H elementary unipotent. Apply
   `lem-sfb-primitive-frobenius-module-duality` to its primitive functions M:
   this is a finitely generated module over k_sigma[F], and H is U(M).
2. Apply `lem-sfb-perfect-skew-polynomial-cyclic-decomposition` to write M as
   a finite direct sum of A/Ag. Restriction to summands and summation identify
   Hom_A(M,R) with the product of the Hom_A(A/Ag,R), naturally and additively
   in every k-algebra R. Reconstruction identifies the represented products.
3. A map A/Ag → R is determined by the image x of 1, with g acting as zero.
   For g = sum c_j F^j this means sum c_j x^(p^j) = 0, so the cyclic factor
   is Spec k[t]/(sum c_j t^(p^j)). Zero g gives Ga; nonzero constant g gives
   the trivial group. This uses `def-weil-pbc-algebra-hom-quotient`,
   `def-sc-gm-ga`, and `def-weil-affine-spectrum`.
4. Normalize a remaining polynomial to be monic of degree p^m, with least
   nonzero index r. Its quotient has dimension p^m by
   `lem-weil-pbc-monic-quotient-free`, hence is finite. Factor it as
   t^(p^r) u(t), with u(0) nonzero. A finite geometric series inverts u
   modulo t^(p^r); the resulting Bezout identity gives the two-factor CRT
   decomposition. The first factor has only the prime (t); the other misses
   the identity. Thus the identity component is alpha_(p^r), with the
   inherited additive law. For r = 0 it is trivial.
5. By `lem-sfb-perfect-finite-commutative-reduced-splitting`, this finite
   factor is alpha_(p^r) times its reduced finite etale subgroup E_g.
   The affine-product coordinate ring is O(E_g)[t]/(t^(p^r)); its monic
   basis gives p^m = p^r dim_k O(E_g), hence dim_k O(E_g) = p^(m-r).
   Use `lem-weil-pbc-fibre-product-affine-spectra` for the coordinate ring.
6. Collect the zero-g factors into Ga^d, discard trivial factors and r = 0,
   and take E to be the product of the E_g. Base change and composition of
   etale morphisms give etaleness. Tensor products of the finite bases give
   finiteness and rank p^a, where a is the sum of the m-r. Reassociate the
   group product isomorphisms. With no finite factors E is Spec k and a = 0;
   empty additive and infinitesimal products are trivial group schemes.
-/
theorem additive_subgroup_perfect_decomposition
    {k : Type u} [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hperfect : ∀ x : k, ∃ y : k, y ^ p = x)
    (n : ℕ) (H : Grp (Over (Spec (.of k))))
    (i : H ⟶ ∏ᶜ fun _ : Fin n ↦ Grp.mk (StandardGroupSchemes.additive k))
    [IsClosedSubgroupScheme i.hom.hom]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom] :
    ∃ (d s a : ℕ) (r : Fin s → ℕ), (∀ j : Fin s, 1 ≤ r j) ∧
      ∃ (A : Fin s → Grp (Over (Spec (.of k))))
        (E : Grp (Over (Spec (.of k)))),
        (∀ j : Fin s, ∃ e : (A j).X ≅ StandardGroupSchemes.alpha k (p ^ r j),
          IsMonHom (e.hom ≫ StandardGroupSchemes.alphaInclusion k (p ^ r j))) ∧
        IsCommMonObj E.X ∧ IsFinite E.X.hom ∧ Etale E.X.hom ∧
        E.X.hom.finrankΓ = p ^ a ∧
        Nonempty (H ≅
          ((∏ᶜ fun _ : Fin d ↦ Grp.mk (StandardGroupSchemes.additive k)) ⨯
            (∏ᶜ fun j : Fin s ↦ A j)) ⨯ E) := by
  sorry

end AlgebraicGeometry
