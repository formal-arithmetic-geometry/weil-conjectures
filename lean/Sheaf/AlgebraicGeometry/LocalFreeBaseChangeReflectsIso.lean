module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
@[expose] public section
universe u v
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
/-- A local homomorphism of commutative local rings reflects finite-free isomorphisms.
Source: Stacks Project, Tag 00O0, Lemma 10.79.4(3), adapted matrix argument.

Proof: Choose finite bases of ranks m and n. Scalar extension gives the same
matrix over S. Reducing the extended inverse modulo the maximal ideal of S
shows m = n, by dimension over its nonzero residue field. The determinant of
the square extended matrix is a unit, since determinants multiply and its
inverse matrix has determinant inverse to it. A local ring homomorphism
reflects units, so the original determinant is a unit in R. Multiplying the
adjugate by its inverse gives a two-sided inverse of the original matrix.
Transport this inverse through the chosen bases to obtain an inverse of φ.
The argument includes rank zero (empty determinant 1); unequal ranks cannot
satisfy the premise. No flatness is required.
(blueprint: lem-sc-local-free-base-change-reflects-iso) -/
theorem isIso_of_isIso_extendScalars_of_finite_free
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f]
    {M N : ModuleCat R} [Module.Free R M] [Module.Finite R M]
    [Module.Free R N] [Module.Finite R N] (φ : M ⟶ N)
    (hφ : IsIso ((ModuleCat.extendScalars f).map φ)) : IsIso φ := by
  sorry
end AlgebraicGeometry.Scheme.Modules
