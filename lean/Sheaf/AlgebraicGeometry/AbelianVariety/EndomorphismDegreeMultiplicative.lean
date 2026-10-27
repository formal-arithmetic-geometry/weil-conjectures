module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny

/-!
# Multiplicativity of the degree extended by zero

Source: Milne, Abelian Varieties, Chapter I §7, printed p.32; §10, printed pp.46–47,
Remark 10.11; Lemma 10.22 and Proposition 10.20, printed pp.51–52
(blueprint: lem-sfb-abelian-degree-multiplicative).

The degree here is kernel order for isogenies and zero for other endomorphisms.
Kernel order is scheme length, including inseparable and nonreduced kernels.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Classical in
/-- The degree function introduced in the multiplicativity statement: kernel order for an
isogeny and zero otherwise. Source: Milne, Abelian Varieties, Chapter I §7, printed p.32,
and §10, printed p.46, immediately before Theorem 10.9
(blueprint: lem-sfb-abelian-degree-multiplicative).

This uses the existing `isogenyDegree`, namely the dimension of the coordinate algebra
of the scheme-theoretic kernel. The conditional supplies the specified zero extension. -/
noncomputable def abelianEndomorphismDegree {k : Type u} [Field k]
    {A : Over (Spec (.of k))} [GrpObj A] (a : A ⟶ A) : ℕ :=
  if IsIsogeny a then isogenyDegree a else 0

/-- The degree extended by zero takes the identity to one and multiplies under composition.
Source: Milne, Abelian Varieties, Chapter I §7, printed p.32; Remark 10.11, printed p.47;
Lemma 10.22 and Proposition 10.20, printed pp.51–52
(blueprint: lem-sfb-abelian-degree-multiplicative).

Proof:
1. The identity is a surjective homomorphism whose kernel is Spec k, of order one.
2. If a ∘ b is an isogeny, a is surjective and hence an isogeny by the equal-dimension
   criterion (lem-sfb-equal-dimension-isogeny-criterion). The closed kernel of b embeds
   in the finite kernel of a ∘ b (lem-sc-kernel-subgroup). Its coordinate algebra is a
   quotient of a finite-dimensional algebra, hence is finite-dimensional. The finite-kernel
   criterion (lem-sfb-finite-kernel-equal-dimension-isogeny) makes b surjective, hence an
   isogeny too.
3. Conversely, two isogenies have surjective composite, an isogeny by the equal-dimension
   criterion. Their kernel orders are their finite-flat ranks (lem-sc-isogeny-degree).
   They are finite locally free by the finite-kernel criterion. Multiplication of constant
   finite locally free degrees (lem-sfb-finite-locally-free-degree-composition) gives
   d(a ∘ b) = d(b)d(a) = d(a)d(b), evaluating the ranks at the identity point.
4. If either factor is not an isogeny, step 2 excludes an isogeny composite, so both sides
   of the degree formula vanish by definition. All orders are dimensions of kernel
   algebras; no separability or reducedness is used. -/
theorem abelianEndomorphismDegree_multiplicative {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (hpos : 0 < IsAbelianVariety.dim A) :
    abelianEndomorphismDegree (𝟙 A) = 1 ∧
      ∀ (a b : A ⟶ A) [IsMonHom a] [IsMonHom b],
        abelianEndomorphismDegree (b ≫ a) =
          abelianEndomorphismDegree a * abelianEndomorphismDegree b := by
  sorry

end AlgebraicGeometry
