/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q115
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Mon
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Sheaf.GroupTheory.TorsionfreeRationalizationInjective
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Finite free groups of homomorphisms of abelian varieties

Source: Milne, Abelian Varieties, Chapter I, Theorem 10.15, pp.49–50,
and the endomorphism convention of Section 10, pp.42–43
(blueprint: lem-sfb-abelian-hom-finite-free).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonObj

namespace AlgebraicGeometry

/-- Group-scheme homomorphisms form a subgroup of the pointwise group of scheme morphisms.
Source: Milne, Abelian Varieties, I Section 10, pp.42–43
(blueprint: lem-sfb-abelian-hom-finite-free). The multiplication here is pointwise addition
on the target abelian variety, written multiplicatively by Mathlib's group-object API. -/
def abelianVarietyHomSubgroup {k : Type u} [Field k]
    (A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B] [IsAbelianVariety B] :
    Subgroup (A ⟶ B) where
  carrier := {f | IsMonHom f}
  one_mem' := (inferInstance : IsMonHom (1 : A ⟶ B))
  mul_mem' := fun {f} {g} (_hf : IsMonHom f) (_hg : IsMonHom g) ↦
    (inferInstance : IsMonHom (f * g))
  inv_mem' := fun {f} (_hf : IsMonHom f) ↦ (inferInstance : IsMonHom f⁻¹)

/-- The abelian group Hom_k(A,B), with pointwise addition induced by B's group law.
`Additive` changes the notation for the subgroup's pointwise multiplication to addition.
Source: Milne, Abelian Varieties, I Section 10, pp.42–43
(blueprint: lem-sfb-abelian-hom-finite-free). -/
abbrev abelianVarietyHom {k : Type u} [Field k]
    (A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B] [IsAbelianVariety B] :=
  Additive (abelianVarietyHomSubgroup A B)

/-- Hom_k(A,B) has a finite integer basis. End_k(A) is a unital associative ring with
its same pointwise additive group, multiplication f*g = f ∘ g, and identity id_A;
its additive group also has a finite integer basis.

Source: Milne, Abelian Varieties, I Theorem 10.15, pp.49–50, and Section 10, pp.42–43
(blueprint: lem-sfb-abelian-hom-finite-free).

Proof plan:
1. By lem-sc-av-commutative, pointwise sum and inverse preserve group homomorphisms.
   Commutativity gives the abelian Hom group; composition is additive in both variables.
2. Choose ell=2 unless char(k)=2, then ell=3. The injective additive Tate action of
   lem-sfb-abelian-tate-action-saturation embeds Hom into a finite free Z_ell-module.
   Since Z_ell lies in the characteristic-zero field Q_ell (def-weil-l-adic-numbers),
   Hom is torsion-free. Embed E=End(C) in E tensor Q by
   lem-trf-torsionfree-rationalization-injective, without assuming finite rational rank.
3. For any finite rationally independent family in E, let V be its rational span and
   Lambda=E intersect V. By lem-sfb-abelian-degree-polynomial, degree is a rational
   polynomial P on V, with P(0)=0. By lem-sfb-simple-isogeny-decomposition, every nonzero
   endomorphism of a positive-dimensional simple C is an isogeny, of positive integer
   degree. Extend P to real coordinates. The open set |P|<1 meets Lambda only in zero;
   its translates prove that Lambda is discrete, also when the family is empty.
4. Apply lem-sfb-discrete-real-submodule-finite, then lem-trf-fg-torsionfree-group-free,
   obtaining an integer basis of Lambda. Clearing denominators proves rational
   independence, and the original family proves spanning. If dim(V)=r, the basis has
   r elements and Lambda/ell Lambda has ell^r elements.
5. Tate action induces Lambda/ell Lambda -> H/ell H, with H=End_Z_ell(T_ell C).
   Saturation from lem-sfb-abelian-tate-action-saturation makes this injective: if
   a=ell b in E, then b=a/ell lies in V, hence in Lambda. Since H has rank 4 dim(C)^2
   and Z_ell/ell=Z/ell by def-weil-l-adic-numbers, r is bounded by 4 dim(C)^2.
6. Choose a rationally independent family of maximal size. Every element of E lies in
   its rational span, or could enlarge it. Every rational tensor is a finite rational
   sum of elements of E, so this span is all E tensor Q. Now Lambda=E, and steps 3–4
   prove finite freeness of End(C) for every positive-dimensional simple C.
7. Use lem-sfb-simple-isogeny-decomposition to choose isogenies p:prod A_i -> A and
   q:B -> prod B_j with simple factors, and quasi-inverses p',q' with pp'=[n], q'q=[m].
   The matrix of qfp defines an additive map Hom(A,B) -> prod Hom(A_i,B_j). A zero
   matrix implies qfp=0, since a map out of a finite product is the sum of its factor
   restrictions. Then 0=q'(qfp)p'=[m]f[n]=mn f, hence f=0 by torsion-freeness.
   This also covers empty products.
8. Between simple factors, Hom is zero or embeds into End(A_i) by composition with a
   quasi-inverse of an isogeny: vf=0 implies tf=hvf=0. Apply
   lem-weil-subgroup-finite-free-abelian-group-free to each such embedding and to the
   matrix embedding of step 7. Finite products have the union of the coordinate bases.
9. Specialize to B=A. Multiplication is f*g=f ∘ g. Associativity and identity are the
   category laws; both distributive laws are additivity of composition from step 1.
   The zero abelian variety gives the one-element ring, empty basis, and 1=0=id_A. -/
theorem abelianVariety_hom_finite_free {k : Type u} [Field k]
    (A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B]
    [IsAbelianVariety A] [IsAbelianVariety B] :
    (∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℤ (abelianVarietyHom A B))) ∧
      ∃ r : Ring (abelianVarietyHom A A),
        r.toAddCommGroup = Additive.addCommGroup ∧
        (∀ f g : abelianVarietyHom A A, (r.mul f g).val = g.val ≫ f.val) ∧
        r.one.val = 𝟙 A ∧
        ∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℤ (abelianVarietyHom A A)) := by
  sorry

end AlgebraicGeometry
