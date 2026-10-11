/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Local finiteness of irreducible components of locally Noetherian schemes

Source: Stacks Project, Topology, Lemma 5.9.2, Tag 0052, applied on affine Noetherian
open neighbourhoods (blueprint: lem-sc-locnoeth-components-locally-finite).
-/

universe u

namespace AlgebraicGeometry

/-- Every point of a locally Noetherian scheme has an open neighbourhood meeting only
finitely many irreducible components.

Source: Stacks Project, Topology, Lemma 5.9.2, Tag 0052, applied on affine Noetherian
open neighbourhoods (blueprint: lem-sc-locnoeth-components-locally-finite).

Proof:
1. Fix a point `x`. Choose an affine open neighbourhood `U` whose ring of sections is
   Noetherian, using `pqf-def-locnoeth`.
2. The underlying space of `U` is Noetherian by
   `lem-sc-affine-noetherian-underlying-space`, so its irreducible components form a finite
   set by `lem-sc-noetherian-finite-irreducible-components` (Stacks Tag 0052).
3. By `lem-sc-components-open-injection`, each component of `X` meeting `U` restricts to a
   component of `U`, and distinct such components have distinct restrictions. Indeed, the
   nonempty open intersection with an irreducible component is dense in that component,
   so its closure in `X` recovers the original component. Hence the components meeting `U`
   inject into the finite set of components of `U`, and form a finite set.
4. This `U` is the required open neighbourhood. Since `x` was arbitrary, the components
   are locally finite. -/
theorem exists_open_finite_irreducibleComponents (X : Scheme.{u}) [IsLocallyNoetherian X]
    (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      {Z : Set X | Z ∈ irreducibleComponents X ∧ (Z ∩ (U : Set X)).Nonempty}.Finite := by
  sorry

end AlgebraicGeometry
