/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.Paper.PQFCohomology
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence

/-! # Affine basic neighbourhoods of closed points

Source: Stacks Project, Tag 01XF, label lemma-quasi-compact-h1-zero-covering,
first paragraph of the proof (blueprint: lem-pqf-h1-closed-point-affine-basic-open).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Ideal H¹ vanishing gives an affine basic neighbourhood of each closed point.

Source: Stacks Project, Tag 01XF, label lemma-quasi-compact-h1-zero-covering,
first paragraph of the proof (blueprint: lem-pqf-h1-closed-point-affine-basic-open).

Proof: Choose an affine neighbourhood U = Spec A of x and let m be its maximal
ideal. Put Z = X \ U and Z' = Z ∪ {x}. The reduced induced closed subschemes give
quasi-coherent ideals I and I' with I' ≤ I. On U these are A and m; on X \ {x}
they agree. Thus I/I' is supported at x and its sections are A/m (glue using
the cover U, X \ {x}; the quotient is zero on the second open and the overlap).
The long exact sequence and H¹(X,I') = 0 lift 1 in A/m to a section f of I.
Viewed in the structure sheaf, f vanishes on Z and is nonzero at x, so
x ∈ X_f ⊆ U. Restriction identifies X_f with D(f|_U), which is affine.
No quasi-compactness or separation hypothesis is used in this step. -/
theorem exists_affineBasicOpen_of_isClosed_singleton_of_h1_ideal_zero (X : Scheme.{u})
    (hI : ∀ (I : X.IdealSheafData), I.toModules.IsQuasicoherent →
      Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I.toModules))
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ f : Γ(X, ⊤), x ∈ X.basicOpen f ∧ IsAffineOpen (X.basicOpen f) := by sorry

end AlgebraicGeometry
