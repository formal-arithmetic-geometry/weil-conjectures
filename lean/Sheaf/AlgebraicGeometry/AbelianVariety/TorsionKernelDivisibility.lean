/-
Copyright (c) 2026 Q154. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q154
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Monoidal.Grp
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Precoverage
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion

/-!
# Divisibility of homomorphisms killing torsion

Source: Milne, Abelian Varieties, Chapter I, Remarks 8.11(f) and 8.12, p.39,
Lemma 10.16, p.49, and Proposition 14.4(b), p.62
(blueprint: lem-sfb-abelian-torsion-kernel-divisibility).

The library writes the group law multiplicatively: `1` is the zero point, `𝟙 A ^ n`
is multiplication by `n`, and `g ^ n` is the pointwise sum of `n` copies of `g`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A homomorphism of abelian varieties over an algebraically closed field which kills all
`n`-torsion points, with `n ≥ 1` invertible in the field, factors uniquely through `[n]`.
The same factorization is `f = n g`, written `f = g ^ n` in the multiplicative convention.

Source: Milne, Abelian Varieties, Chapter I, Remarks 8.11(f) and 8.12, p.39,
Lemma 10.16, p.49, and Proposition 14.4(b), p.62
(blueprint: lem-sfb-abelian-torsion-kernel-divisibility).

Proof:
1. By lem-sc-av-commutative, both group schemes are commutative. Put `q = [n]` and
   `K = A[n]`. By lem-sc-isogeny-facts, `q` is finite, flat and surjective. Since `n` is
   invertible, lem-sc-mult-n-etale-kernel makes `K` finite étale. This also holds in
   dimension zero.
2. The singleton `q` is an fpqc covering by def-weil-pbc-fpqc-covering: the inverse image
   of any affine open is affine by def-weil-finite-integral-morphism, and maps onto that
   open; flatness was established in step 1.
3. By lem-sc-finite-etale-algebra-criterion, the finite algebra of `K` is a product of
   finite separable extensions of the base field. Each extension is the base field,
   because an irreducible polynomial over an algebraically closed field is linear
   (def-weil-algebraic-closure). Thus `K` is a finite disjoint union of rational points.
   The hypothesis says that the restriction of `f` to each component is zero; hence
   the restriction to the entire kernel scheme is zero.
4. Using def-sc-group-scheme and def-sc-mult-n, identify the kernel pair of `q` with
   `A × K` by `(a,t) ↦ (a,a+t)`, with inverse `(a,b) ↦ (a,b-a)`. The latter lands in
   `K` because `q(b-a)=0`. Both are scheme morphisms assembled from the group operations
   and the fibre-product universal property. Under this identification the two
   pullbacks of `f` agree, since `f(a+t)=f(a)+f(t)=f(a)` by step 3.
5. Apply lem-weil-pbc-fpqc-representable-descent to obtain the unique scheme morphism
   `g` with `q ≫ g = f`. Apply its uniqueness again with target `Spec k` to show that
   `g` commutes with the structure maps, so it is a morphism over `k`.
6. The maps `q × id` and `id × q` are the base changes of `q` along the two projections,
   hence fpqc coverings by lem-galois-fpqc-covering-base-change. The two morphisms
   expressing compatibility of `g` with addition agree after precomposition with
   `q × q`, because `q` and `f` are homomorphisms. Cancel `id × q` and then `q × id`
   using uniqueness in lem-weil-pbc-fpqc-representable-descent. The unit is preserved
   since `g(q(0))=f(0)=0`. Compatibility with inversion follows by the same uniqueness
   after precomposition with `q`. Thus `g` is a group-scheme homomorphism.
7. Descent uniqueness also gives uniqueness among group-scheme homomorphisms. On
   every scheme of test points, `g([n](a))=n g(a)` by the homomorphism law and
   def-sc-mult-n. Therefore the factorization is also `f = g ^ n` as scheme morphisms. -/
theorem existsUnique_factor_npow_of_kills_torsion
    {k : Type u} [Field k] [IsAlgClosed k]
    (A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B]
    [IsAbelianVariety A] [IsAbelianVariety B]
    (n : ℕ) (hn : 1 ≤ n) (hnk : IsUnit (n : k))
    (f : A ⟶ B) [IsMonHom f]
    (hf : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ A, x ≫ (𝟙 A ^ n) = 1 → x ≫ f = 1) :
    ∃ g : A ⟶ B, IsMonHom g ∧ f = (𝟙 A ^ n) ≫ g ∧ f = g ^ n ∧
      ∀ g' : A ⟶ B, IsMonHom g' → f = (𝟙 A ^ n) ≫ g' → g' = g := by
  sorry

end AlgebraicGeometry
