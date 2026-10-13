module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-! # The invertible pivot in the residue rank-one kernel argument -/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace ModuleCat

/-- Finite free coordinates with an invertible leading block; the off-diagonal blocks
are unrestricted. Source: Stacks Project, Tags 00O0 and 00NX, unit-minor argument.
(blueprint: new-residue-kernel-unit-minor-pivot)

Proof: Choose finite bases for the two scalar extensions. Tensor associativity
identifies reduction of their matrix modulo the maximal ideal of A with the given
scalar extension to its residue field. Rank-nullity and the kernel equivalence
show that the source dimension n is positive and the matrix rank is n - 1.
Select n - 1 independent columns and n - 1 rows whose square minor has nonzero
determinant. The lifted determinant is a unit of the local ring: its residue is
nonzero. Reorder the selected columns first and the sole remaining column last;
reorder the selected rows first and the complementary rows last. The coordinate
spaces are U = A^(n-1) and C = A^(m-n+1). Take B to be multiplication by the
selected square matrix, with inverse given by its adjugate divided by its unit
determinant. These permutations give eX and eY, and evaluating the leading block
on (u,0) proves the displayed equation. C is free in its coordinate basis. When
n = 1 the leading block is empty, U is zero and B is its identity; no choice of a
nonempty minor is required. The case m < n-1 is excluded by the residue rank.
No elimination of the other three blocks is asserted. -/
theorem residue_kernel_unit_minor_pivot
    (R : Type v) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    [IsLocalRing A] (X Y : ModuleCat.{v} R) (f : X ⟶ Y)
    (hX : Module.Free A
      ((ModuleCat.extendScalars (algebraMap R A)).obj X))
    (hY : Module.Free A ((ModuleCat.extendScalars (algebraMap R A)).obj Y))
    (hfX : Module.Finite A ((ModuleCat.extendScalars (algebraMap R A)).obj X))
    (hfY : Module.Finite A ((ModuleCat.extendScalars (algebraMap R A)).obj Y))
    (hres : Nonempty (LinearMap.ker ((ModuleCat.extendScalars
      ((IsLocalRing.residue A).comp (algebraMap R A))).map f).hom
      ≃ₗ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField A)) :
    ∃ (U C : ModuleCat.{v} A), Module.Free A C ∧
      ∃ (eX : ((ModuleCat.extendScalars (algebraMap R A)).obj X) ≃ₗ[A] (U × A))
        (eY : ((ModuleCat.extendScalars (algebraMap R A)).obj Y) ≃ₗ[A] (U × C))
        (B : U ≃ₗ[A] U),
        ∀ u, (eY (((ModuleCat.extendScalars (algebraMap R A)).map f).hom
          (eX.symm (u, 0)))).1 = B u := by sorry
end ModuleCat
