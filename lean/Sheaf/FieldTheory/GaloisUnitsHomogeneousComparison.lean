/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker N3
-/
module

public import Sheaf.FieldTheory.GaloisUnitsTwoCocycles
import Sheaf.FieldTheory.GaloisUnitsCohomology
import Sheaf.FieldTheory.GaloisUnitsHomogeneousCocycleDescent

/-!
# Homogeneous and inhomogeneous continuous unit cohomology

Source: Stacks Project, Section 0DVG; Mathlib's `TopRep.homogeneousCochains`.
(blueprint: lem-sc-galois-units-homogeneous-comparison).
-/

@[expose] public section

universe u

namespace Field

/-- The homogeneous degree-two cohomology model agrees with the explicit inhomogeneous
continuous cocycle quotient. This is a comparison of two continuous cochain models and
involves no etale sheaves or sheaf cohomology.

Proof: the Krull topology on `G = Gal(SeparableClosure K/K)` is compact Hausdorff.
A unit and its inverse lie in a finite separable extension; the fixing subgroup of its
normal closure is open. Thus its orbit map is locally constant. Since the coefficient
space is discrete, the action `G × M → M` is jointly continuous.
The compact-open exponential law identifies the iterated maps in homogeneous cochains
with jointly continuous functions on `G^(n+1)`. Send an equivariant homogeneous cochain
`f` to `c(g₁,...,gₙ) = f(1,g₁,g₁g₂,...,g₁...gₙ)`. Its inverse sends `c` to
`f(g₀,...,gₙ) = g₀ • c(g₀⁻¹g₁,...,gₙ₋₁⁻¹gₙ)`. The two formulas are inverse by
homogeneous equivariance. All substitutions are continuous by continuity of group
operations and of the coefficient action. The alternating omission differential
transforms to the inhomogeneous differential: omitting the first coordinate gives
`g₁ • c(g₂,...,gₙ₊₁)`; an interior omission multiplies two adjacent arguments; the last
omission drops the last argument. Mathlib's recursively defined differential has these
alternating omission terms, as follows by induction on the recursion.
In degrees one and two these formulas give respectively
`g • b(h) - b(gh) + b(g)` and
`g • c(h,i) - c(gh,i) + c(g,hi) - c(g,h)`.
The termwise equivalences therefore identify two-cocycles and one-coboundaries.
TopModuleCat homology has underlying algebraic kernel modulo image, with the quotient
topology. Forget that topology and descend the inverse cochain transformations to the
quotients: equality there is exactly the continuous-coboundary relation in
`galoisUnitsTwoCocycleSetoid`. These descended transformations are mutually inverse.

Source: Stacks Project, Section 0DVG, inhomogeneous differential; the homogeneous
change of variables and its compatibility are the explicit argument above.
(blueprint: lem-sc-galois-units-homogeneous-comparison). -/
theorem nonempty_equiv_galoisUnitsH2_twoCocycleClasses (K : Type u) [Field K] :
    Nonempty (GaloisUnitsH2 K ≃ GaloisUnitsTwoCocycleClasses K)  := by
  apply nonempty_equiv_galoisUnitsH2_twoCocycleClasses_of_cocycle_equiv K
  exact nonempty_equiv_galoisUnitsHomogeneousCocycles_twoCocycle K

end Field
