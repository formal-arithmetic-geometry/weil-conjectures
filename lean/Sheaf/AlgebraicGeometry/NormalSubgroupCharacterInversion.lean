module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Sheaf.AlgebraicGeometry.AffineGroupFrobeniusSmoothImage
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Inverse powers of occurring normal-subgroup characters

Source: Milne, Algebraic Groups (2017), Lemma 5.16, printed pp.102--103.
(blueprint: lem-sfb-normal-subgroup-character-inversion)

A basis identifies a finite-dimensional vector space with k^(ULift (Fin n)).
The A-span of the coordinate image of a subspace is its scalar extension inside A^n.
Evaluating the character's coordinate map on t^(-m) gives chi_A(h)^(-m), including
for nonreduced algebras. No reducedness, smoothness or characteristic restriction is imposed.
The same occurrence formula is used by chevalley_character_cancellation.
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An occurring character of a closed normal subgroup has an occurring negative multiple.
Source: Milne, Algebraic Groups (2017), Lemma 5.16, printed pp.102--103.
(blueprint: lem-sfb-normal-subgroup-character-inversion)

Proof plan, following all five steps of the node:
1. First suppose G is smooth. Choose a line L in the nonzero chi-subspace U.
Let S be the sum of all N-stable lines of V. Normality makes gD another N-stable
line for every g in G(k), since n(gd)=g((g^-1 n g)d) on every algebra.
Using g^-1 as well gives gS=S. Apply
lem-sfb-smooth-group-rational-point-subspace-test to obtain a rational G-action on S.
Only G, rather than N, needs to be smooth.
2. Apply lem-sfb-character-eigenspaces-independent to write S as the direct sum
of its finitely many character eigenspaces. Complement L in the chi-eigenspace
and add the other eigenspaces to obtain S=L direct-sum C with C N-stable on all
algebras. In the dual rational G-representation S*, Ann(C) is a nonzero line with
N-character chi^-1: (n f)(v)=f(n^-1 v). The inverse-transpose matrix defines the
rational dual action. This proves the smooth case with m=1.
3. In characteristic zero, lem-sfb-affine-group-frobenius-smooth-image makes G
smooth. In characteristic p>0, use that lemma to choose q=p^r with r>=1 and a
factorization G -> I -> G^(q), with I smooth, affine and finite type.
4. Base change N, the representation, L and chi along a -> a^q. Form the closed
normal subgroup H=I times_(G^(q)) N^(q), using def-pc-fibre-product and the
pointwise normality of def-sc-group-scheme-subgroup. Restrict the twisted
representation to I and chi^(q) to H, giving psi. The nonzero line L^(q) has
H-character psi: tensoring the first-column identities (chi,0,...,0) gives the
same identities after base change. Naturality of relative Frobenius factors
N -> I through H and gives psi composed with N -> H equal to chi^q. On
coordinate rings b tensor c maps to c b^q, so this holds on every algebra.
5. Apply the smooth case to (I,H,psi). Its dual line has character psi^-1.
Pull the resulting rational I-representation back to G; the line remains
nonzero and its N-character is chi^-q. Take m=q>0. This also covers nonreduced
G and N, and disconnected G, without replacing algebra points by field points. -/
theorem normalSubgroup_character_inverse_power_occurs
    {k : Type u} [Field k] [IsAlgClosed k]
    (G N : Over (Spec (.of k))) [GrpObj G] [GrpObj N]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (i : N ⟶ G) [IsClosedSubgroupScheme i] [IsNormalSubgroupScheme i]
    (χ : N ⟶ StandardGroupSchemes.multiplicative k) [IsMonHom χ]
    (hχ : ∃ (n : ℕ) (ρ : GeneralLinearGroup.RationalHom G (ULift.{u} (Fin n)))
      (_ : IsMonHom ρ) (U : Submodule k (ULift.{u} (Fin n) → k)),
      U ≠ ⊥ ∧ ∀ (A : Type u) [CommRing A] [Algebra k A]
        (h : points N A) (v : ULift.{u} (Fin n) → A),
        v ∈ Submodule.span A
          ((fun w : ULift.{u} (Fin n) → k ↦ fun j ↦ algebraMap k A (w j)) ''
            (U : Set (ULift.{u} (Fin n) → k))) →
        Matrix.toLin' (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A
          (h ≫ i ≫ ρ)) v =
          ((Spec.preimage (h ≫ χ).left).hom (LaurentPolynomial.T 1)) • v) :
    ∃ (m : ℕ), 0 < m ∧
      ∃ (n : ℕ) (ρ : GeneralLinearGroup.RationalHom G (ULift.{u} (Fin n)))
        (_ : IsMonHom ρ) (T : Submodule k (ULift.{u} (Fin n) → k)),
        T ≠ ⊥ ∧ ∀ (A : Type u) [CommRing A] [Algebra k A]
          (h : points N A) (v : ULift.{u} (Fin n) → A),
          v ∈ Submodule.span A
            ((fun w : ULift.{u} (Fin n) → k ↦ fun j ↦ algebraMap k A (w j)) ''
              (T : Set (ULift.{u} (Fin n) → k))) →
          Matrix.toLin' (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A
            (h ≫ i ≫ ρ)) v =
            ((Spec.preimage (h ≫ χ).left).hom (LaurentPolynomial.T (-(m : ℤ)))) • v := by
  sorry

end AlgebraicGeometry
