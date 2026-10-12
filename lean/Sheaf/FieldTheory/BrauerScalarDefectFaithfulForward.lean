module
public import Sheaf.FieldTheory.BrauerScalarDefect
@[expose] public section
universe u
namespace Field
/-- Equality of scalar-defect classes follows from Brauer equivalence.

Given matrix amplifications of `A` and `B` that are isomorphic, tensor the two
splittings and their projective descent lifts (using the opposite lift for `B`).
The scalar defect of the tensor lift is the quotient of the two scalar defects.
Changing a lift by the resulting scalar one-cochain changes its homogeneous
two-cocycle by the corresponding coboundary.  Thus the two representatives have
the same image under `ContinuousCohomology.π`, and hence `x = y`.  This is the
comparison calculation in Stacks Project, Theorem 03R7, with the homogeneous to
inhomogeneous conversion from Section 0DVG.
(blueprint: lem-sc-brauer-scalar-defect-faithful-forward). -/
theorem brauerScalarDefect_eq_of_brauerEquivalent (K : Type u) [Field K]
    (A B : CSA.{u, u} K) (x y : GaloisUnitsH2 K)
    (hx : HasBrauerScalarDefect K A x) (hy : HasBrauerScalarDefect K B y)
    (h : IsBrauerEquivalent A B) : x = y := by sorry
end Field
