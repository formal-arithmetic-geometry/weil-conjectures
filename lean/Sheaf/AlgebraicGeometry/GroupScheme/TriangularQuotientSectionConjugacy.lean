module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Conjugacy of sections of a triangular group quotient

Source: Milne, Algebraic Groups (2017), Summary 16.29(b), printed p.334;
Theorem 16.27(a), printed p.333; Proposition 16.2(c), printed p.325
(blueprint: lem-sfb-triangular-quotient-section-conjugacy).

The triangular and unitriangular conditions are equations on points over every
commutative algebra, including nonreduced algebras. The specified closed subgroup V
is the scheme-theoretic intersection with the unitriangular group. The quotient
uses the existing fppf sheafification presentation with its specified maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- Two homomorphism sections of a smooth quotient of a triangular algebraic group
by its unitriangular intersection are conjugate by a rational point of that intersection.

Source: Milne, Algebraic Groups (2017), Summary 16.29(b), printed p.334;
Theorem 16.27(a), printed p.333 (with the smooth quotient hypothesis of the Summary)
(blueprint: lem-sfb-triangular-quotient-section-conjugacy).

Proof plan, following the six steps of the DAG node:
1. The diagonal homomorphism J -> G_m^n has kernel V. Apply
   lem-sfb-algebraic-group-homomorphism-factorization and identify its image with D
   by the quotient universal property. By lem-sfb-split-torus-subgroups-diagonalizable,
   D is diagonalizable. Restrict t_i/t_j to characters chi_ij of D.
2. Use lem-sfb-unitriangular-coordinate-filtration. Its intersections V_r with J
   are normal in J, start at V, and end at 1. Factor each coordinate map on V_(r-1)
   through its faithfully flat image N_r in G_a using the homomorphism factorization.
   Its kernel is V_r, and conjugation acts by chi_ij. Local lifting and faithful-flat
   descent of the closed defining equations show that N_r is stable under this character.
3. Every point of N_r(F) lifts to V_(r-1)(F): its nonempty affine finite-type fibre
   has a closed point, and lem-weil-pbc-closed-point-residue-field-base identifies its
   residue field with F. This argument does not require a reduced or smooth fibre.
4. For any section h, c(d) = h(d)s_1(d)^(-1) factors through V and satisfies
   c(dd') = c(d)(s_1(d)c(d')s_1(d)^(-1)) on every algebra of points.
5. Inductively choose w_r in V(F) so h_r = Int(w_r^(-1))s_2 has difference in V_r.
   Start with w_0 = 1. The next coordinate f_r is a crossed homomorphism into N_r.
   Apply lem-sfb-smooth-diagonal-additive-crossed-vanishing to obtain
   f_r(d) = a - chi_ij(d)a. Lift a to v in V_(r-1)(F) by step 3 and put
   w_r = w_(r-1)v. The new coordinate is -a + f_r(d) + chi_ij(d)a = 0.
   Normality ensures that every factor lies in V_(r-1), so the kernel property
   factors the new difference through V_r, on all commutative algebras.
6. At the end V_m = 1, hence Int(w_m^(-1))s_2 = s_1 and s_2 = Int(w_m)s_1.
   Scalar extension gives the displayed formula. For n = 1 the filtration is empty
   and V = 1, giving equality of the sections. No smoothness of J or V or
   connectedness is used. -/
theorem triangular_quotient_section_conjugacy
    {F : Type u} [Field F] [IsAlgClosed F]
    (n : ℕ) (hn : 1 ≤ n)
    (J V D : Grp (Over (Spec (.of F))))
    [IsAffine J.X.left] [LocallyOfFiniteType J.X.hom] [QuasiCompact J.X.hom]
    [IsAffine V.X.left] [LocallyOfFiniteType V.X.hom] [QuasiCompact V.X.hom]
    [IsAffine D.X.left] [LocallyOfFiniteType D.X.hom] [QuasiCompact D.X.hom]
    (j : J.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) F)
    [IsClosedSubgroupScheme j]
    (htriangular : ∀ (A : Type u) [CommRing A] [Algebra F A]
      (x : (Spec (.of A)).asOver (Spec (.of F)) ⟶ J.X) (a b : Fin n),
      b < a →
        (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) F A (x ≫ j)).val
          ⟨a⟩ ⟨b⟩ = 0)
    (i : V ⟶ J) [IsClosedSubgroupScheme i.hom.hom]
    (hintersection : ∀ (A : Type u) [CommRing A] [Algebra F A]
      (x : (Spec (.of A)).asOver (Spec (.of F)) ⟶ J.X),
      (∃ y : (Spec (.of A)).asOver (Spec (.of F)) ⟶ V.X, y ≫ i.hom.hom = x) ↔
      ∀ a : Fin n,
        (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) F A (x ≫ j)).val
          ⟨a⟩ ⟨a⟩ = 1)
    (q : J ⟶ D) (hquotient : IsFppfGroupQuotient i q) [Smooth D.X.hom]
    (s₁ s₂ : D ⟶ J) (hs₁ : s₁ ≫ q = 𝟙 D) (hs₂ : s₂ ≫ q = 𝟙 D) :
    ∃ v : 𝟙_ (Over (Spec (.of F))) ⟶ V.X,
      s₂.hom.hom =
        (toUnit D.X ≫ v ≫ i.hom.hom) * s₁.hom.hom *
          (toUnit D.X ≫ v ≫ i.hom.hom)⁻¹ ∧
      ∀ (A : Type u) [CommRing A] [Algebra F A]
        (d : (Spec (.of A)).asOver (Spec (.of F)) ⟶ D.X),
        d ≫ s₂.hom.hom =
          (toUnit ((Spec (.of A)).asOver (Spec (.of F))) ≫ v ≫ i.hom.hom) *
            (d ≫ s₁.hom.hom) *
            (toUnit ((Spec (.of A)).asOver (Spec (.of F))) ≫ v ≫ i.hom.hom)⁻¹ := by
  sorry

end AlgebraicGeometry
