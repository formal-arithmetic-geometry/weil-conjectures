/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSortingOperators
public import Mathlib.Algebra.Homology.Homotopy

/-!
# AlternatingCechSortingBoundaryTransport

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM.
(blueprint: lem-pc-alternating-cech-sorting-boundary-transport)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

open Classical in
/-- Signed stable sorting transports the repeated-tuple boundary.

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equations
20.23.6.1 and 20.23.6.2, transported by signed stable sorting.
Proof: Write kappa for signed stable sorting. The first sorting identity and
square-zero of the differential imply d kappa = kappa d. Stable sorting is
idempotent: sorting a sorted tuple is identity, including its equal-label order.
The repeated-tuple homotopy is the sorted contraction precomposed with kappa:
its formula sorts t and duplicates its first repeat, with the sorting sign.
Duplicating a nondecreasing tuple leaves it nondecreasing. Hence pulling the
sorted contraction back once more by kappa leaves this formula unchanged.
Commute d through kappa in each of the two boundary terms. Both become signed
pullbacks of the boundary at the sorted tuple. The stable-sort filter has one
permutation, characterized by ordering the pairs (t(k), k). Restriction maps
compose by the universal property of the chosen products, so the transports in
these two expansions coincide. Summing over the filter gives the stated formula.
Degree zero has zero contraction. With empty I there are no coordinates.
(blueprint: lem-pc-alternating-cech-sorting-boundary-transport) -/
theorem cechSortingBoundaryTransport (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ)
    (s : S.cochains F p) (t : Fin (p + 1) → I) :
    ((Homotopy.nullHomotopicMap' (cechSecondSortingFamily X U F S)).f p) s t =
      ∑ σ : Equiv.Perm (Fin (p + 1)),
        if cechStableSort t σ then
          (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap t σ).op
            (((Homotopy.nullHomotopicMap'
              (cechSecondSortingFamily X U F S)).f p) s (t ∘ σ)) else 0 := by sorry

end AlgebraicGeometry.Scheme
