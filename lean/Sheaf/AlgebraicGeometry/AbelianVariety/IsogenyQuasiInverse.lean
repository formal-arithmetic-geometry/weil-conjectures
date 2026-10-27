module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Grp

import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
import Sheaf.AlgebraicGeometry.FiniteGroupSchemeOrderAnnihilator
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Precoverage

/-! # An integer quasi-inverse for an isogeny

Source: Milne, Abelian Varieties, I Remark 8.6, printed p.36; Algebraic Groups,
Proposition 11.32, printed p.221; Stacks Tags 023Q and 022D(3).
(blueprint: lem-sfb-abelian-isogeny-quasi-inverse)

Multiplication by `n` is the pointwise power `𝟙 A ^ n` in the existing group-scheme API.
The base field is arbitrary and the kernel is scheme-theoretic.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- An isogeny of abelian varieties has a reverse group-scheme homomorphism whose two
composites are multiplication by the same positive integer.

Source: Milne, Abelian Varieties, I Remark 8.6, printed p.36, using the kernel quotient
universal property discussed at I Proposition 8.10, printed pp.38-39. For arbitrary fields
and nonreduced kernels use Stacks Tag 023Q instead of the algebraically closed finite-group
case of that proposition. Kernel annihilation is Milne, Algebraic Groups, Proposition 11.32,
printed p.221. (blueprint: lem-sfb-abelian-isogeny-quasi-inverse)

Proof plan:
1. Set K = ker f, with inclusion i, using lem-sc-kernel-subgroup and def-sc-isogeny.
   By lem-sc-av-commutative, K is commutative. The result
   lem-sfb-finite-group-scheme-order-annihilator gives n = dim_k Γ(K, O_K) ≥ 1 and
   [n]_K = 0. Repeated addition (def-sc-mult-n) therefore gives i followed by [n]_A = 0.
2. By lem-sc-isogeny-degree, f is finite and flat, and def-sc-isogeny gives surjectivity.
   By def-weil-finite-integral-morphism it is affine: over each affine open of B its
   inverse image is affine and surjects onto that open. Thus the singleton family f is
   an fpqc covering (def-weil-pbc-fpqc-covering).
3. The group laws (def-sc-group-scheme) and the kernel universal property
   (lem-sc-kernel-subgroup) identify A × K with A ×_B A by (a,t) ↦ (a,a+i(t)), with
   inverse (a,a') ↦ (a,a'-a). Under this identification the two projections followed by
   [n]_A agree, because [n]_K = 0 and [n] is a homomorphism (def-sc-mult-n).
4. By lem-weil-pbc-fpqc-representable-descent, [n]_A descends uniquely to g : B → A
   with f ≫ g = [n]_A. Descent uniqueness with target Spec k shows that g is over k.
5. The maps g after the group law of B and the group law of A after g × g agree
   after f × f: both send (a,a') to [n]_A(a)+[n]_A(a'). Factor f × f into id × f and
   f × id. Both are fpqc by lem-galois-fpqc-covering-base-change. Twice applying
   uniqueness in lem-weil-pbc-fpqc-representable-descent gives compatibility with
   multiplication. Since g(e_B) = g(f(e_A)) = [n]_A(e_A) = e_A, g is a homomorphism
   (def-sc-group-scheme).
6. Repeated addition (def-sc-mult-n) gives f ≫ g ≫ f = [n]_A ≫ f = f ≫ [n]_B.
   Descent uniqueness for the covering f and target B cancels f, giving g ≫ f = [n]_B.
   This uses lem-weil-pbc-fpqc-representable-descent and assumes neither perfection,
   separability, nor invertibility of n in k.
-/
theorem IsIsogeny.exists_quasiInverse
    {k : Type u} [Field k] {A B : Over (Spec (.of k))}
    [GrpObj A] [GrpObj B] [IsAbelianVariety A] [IsAbelianVariety B]
    (f : A ⟶ B) [IsIsogeny f] :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ g : B ⟶ A, IsMonHom g ∧
      f ≫ g = (𝟙 A : A ⟶ A) ^ n ∧ g ≫ f = (𝟙 B : B ⟶ B) ^ n := by
  sorry

end AlgebraicGeometry
