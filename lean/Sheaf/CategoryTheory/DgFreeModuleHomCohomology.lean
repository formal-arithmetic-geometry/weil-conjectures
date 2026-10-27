/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The SHEAF contributors
-/
module

public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory

/-!
# Cohomology as morphisms from the regular DG module

Source: Stacks Project, dga.tex, Tags 09K1, 09KM, 09KY(1), and the proof of 09RA
(blueprint: lem-sfb-dg-free-module-hom-cohomology).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CategoryTheory.DgAlgebra

/-- Evaluation on cycles identifies cohomology with derived morphisms from the
regular module. The equation on all homogeneous elements specifies the actual
multiplication map, read through any comparison with the prescribed shift.
In particular a boundary has zero cohomology class and hence zero derived image.
`DerivedStructure` supplies the standard structure on the fixed localization;
`S` with `e` is any representative of the standard shift with unchanged right action.

Source: Stacks Project, dga.tex, Tag 09K1, lemma-hom-from-shift-free;
Tag 09KY, lemma-hom-derived (1), using Tag 09KM; the proof of Tag 09RA
(blueprint: lem-sfb-dg-free-module-hom-cohomology).

Proof plan, following the three steps of the node:
1. Evaluation at 1 identifies the right-linear Hom complex from B with the
underlying complex of M. The Leibniz rule gives d(1)=0 and d(f_x)=f_(dx).
Thus the regular module is homotopically projective, in the sense of
lem-sfb-dg-homotopically-projective-hom-derived.
2. For the shift M[k], cycles are exactly multiplication maps mu_x. If x-x'=dy,
the degree-minus-one right-linear homotopy b maps to (-1)^k yb has differential
mu_x-mu_x'. Conversely evaluation of a homotopy at 1 gives a boundary.
Consequently the map on cohomology is an additive bijection to Hom in K(B,d).
3. Apply lem-sfb-dg-homotopically-projective-hom-derived to B and M[k].
The localization comparison is bijective and, by
lem-sfb-dg-derived-admissible-triangles, additive. Compose the two bijections.
The displayed homogeneous equation pins this composite to x maps to [mu_x],
and the homotopy in step 2 proves the boundary assertion. No restriction on
integer degrees, cardinality, boundedness or commutativity occurs. -/
theorem exists_freeModuleHomCohomologyEquiv
    (B : Algebra.{u}) [DerivedStructure B] (M : RightModule B) (k : ℤ)
    (S : RightModule B) (e : ShiftComparison B k M S) :
    ∃ E : (((underlying B).obj M).homology k) ≃+
        ((Q B).obj (regular B) ⟶ (Q B).obj S),
      ∀ x : ((underlying B).obj M).cycles k,
        ∃ μ : regular B ⟶ S,
          (∀ (r : ℤ) (b : B.X.X r),
            HEq
              (((((underlying B).obj M).shiftFunctorObjXIso k r (r + k) rfl).hom)
                (e.iso.hom.f r ((((underlying B).map μ).f r) b)))
              (act B M k r (((underlying B).obj M).iCycles k x) b)) ∧
          E (((underlying B).obj M).homologyπ k x) = (Q B).map μ ∧
          ((∃ y : ((underlying B).obj M).X (k - 1),
              ((underlying B).obj M).iCycles k x =
                ((underlying B).obj M).d (k - 1) k y) →
            (Q B).map μ = 0) := by
  sorry

end CategoryTheory.DgAlgebra
