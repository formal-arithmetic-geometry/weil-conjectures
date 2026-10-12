module
public import Sheaf.FieldTheory.BrauerScalarDefect
@[expose] public section
universe u
namespace Field
/-- Equal scalar-defect classes imply Brauer equivalence.

Equality in cohomology makes the quotient of the two matrix descent defects a
scalar coboundary.  Rescaling one lift by its scalar one-cochain gives a genuine
general-linear cocycle on a finite Galois extension.  Finite Galois descent (the
matrix form of Hilbert 90) trivializes this cocycle, so the tensor product of `A`
with the opposite of `B` is an endomorphism algebra.  The central-simple-algebra
criterion for a split tensor product then gives isomorphic positive matrix
amplifications of `A` and `B`, namely `IsBrauerEquivalent A B`.  This is the
injectivity argument in Stacks Project, Theorem 03R7; the cocycle convention is
that of Section 0DVG. (blueprint: lem-sc-brauer-scalar-defect-faithful-backward). -/
theorem brauerEquivalent_of_brauerScalarDefect_eq (K : Type u) [Field K]
    (A B : CSA.{u, u} K) (x y : GaloisUnitsH2 K)
    (hx : HasBrauerScalarDefect K A x) (hy : HasBrauerScalarDefect K B y)
    (h : x = y) : IsBrauerEquivalent A B := by sorry
end Field
