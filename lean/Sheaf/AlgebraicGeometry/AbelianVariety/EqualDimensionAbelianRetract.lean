module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.Dimension
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# A retract of equal-dimensional abelian varieties

Source: Milne, Abelian Varieties, Chapter I Proposition 7.1(c)--(d), printed p.32,
and Chapter III Lemma 6.9, pp.106--107 (blueprint: lem-sfb-equal-dimension-abelian-retract).

The scheme-theoretic kernel of the split monomorphism is trivial.  The equal-dimension
finite-kernel criterion then makes the map finite locally free, and the rank-one
criterion makes it an isomorphism; the given retraction is its inverse.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A retraction between equal-dimensional abelian varieties is an isomorphism.

Source: Milne, Abelian Varieties, Chapter I Proposition 7.1(c)--(d), printed p.32,
and Chapter III Lemma 6.9, pp.106--107 (blueprint: lem-sfb-equal-dimension-abelian-retract).

Proof:
1. Let `K` be the scheme-theoretic kernel of `s`, with projections `i : K → A`
   and `p : K → Spec k` (def-sc-group-scheme).  Applying `r` to `s i = e_B p`
   and using `r s = id` and preservation of the identity gives `i = e_A p`.
   The identity defines `u : Spec k → K` with `i u = e_A` and `p u = id`.
   The two projections of `u p` equal those of `id_K`, so the fibre-product
   universal property gives `u p = id_K`.  Thus `K` is Spec k and its order is one.
2. Apply lem-sfb-finite-kernel-equal-dimension-isogeny: the dimensions are equal
   and the entire scheme-theoretic kernel is finite by step 1.  Hence `s` is
   surjective and finite locally free (def-pc-finite-locally-free), in particular
   finite, flat and locally of finite presentation.  It is an isogeny by def-sc-isogeny.
3. By lem-sc-isogeny-degree, the rank of `s` at every point of `B` is the order
   of its kernel, namely one.  Clause (3) of lem-weil-pbc-finite-flat-rank-iso,
   applied with the properties from step 2, makes `s` an isomorphism.
4. Write `t` for the inverse.  Then `r = r (s t) = (r s) t = t`.
   Both maps are the original group-scheme homomorphisms, so they are inverse
   in that category as well as in the category of k-schemes.
-/
theorem IsAbelianVariety.exists_iso_of_retraction_equal_dim
    {k : Type u} [Field k] [IsAlgClosed k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
    [IsAbelianVariety A] [IsAbelianVariety B]
    (hdim : A.left.dim = B.left.dim)
    (s : A ⟶ B) [IsMonHom s]
    (r : B ⟶ A) [IsMonHom r]
    (hsr : s ≫ r = 𝟙 A) :
    ∃ e : A ≅ B, e.hom = s ∧ e.inv = r := by
  sorry

end AlgebraicGeometry
