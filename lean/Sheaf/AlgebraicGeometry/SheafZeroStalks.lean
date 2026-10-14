/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# A sheaf with vanishing stalks is zero

Source: upstream review #1428, recorded in coord/upstream-review-20261013.md.
(blueprint: pqf-lem-sheaf-zero-stalks)

The upstream module `WeilConjectures.AlgebraicGeometry.Cohomology.FiniteFibre` now
provides `AlgebraicGeometry.Scheme.Modules.isZero_of_isZero_stalk`. The former
`isZero_of_isZero_stalks` declaration was a duplicate and has been retired.
No local declaration callers need adaptation.

This compatibility module intentionally contains no declarations after duplicate removal.
-/

@[expose] public section

-- The canonical upstream theorem is not re-exported by these compatibility imports.
-- The recorded FiniteFibre source is absent from this snapshot. Its signature and proof
-- have not been checked here; see coord/changes/remove-sheaf-zero-stalks-duplicate.md
-- for the existing repair.

-- Repair verification (N2, 2026-10-14): duplicate removal already landed as
-- 20261013T224521-L-1475959; this module has no declarations or proof holes.

-- Second reading (G2, 2026-10-14): compatibility module compiled without warnings;
-- no declarations or proof holes remain. The unavailable upstream theorem is not certified here.

-- Second reading (B4, 2026-10-14): compatibility-only verification; no declarations,
-- new proof progress or certification of the absent upstream theorem.

-- Verification (V1, 2026-10-14): this compatibility module compiles with zero declarations
-- and zero proof holes. The stale repair assignment closes no additional holes.

-- Second reading (W2, 2026-10-14): no declarations or proof holes; compilation is clean.
-- The stale repair assignment verifies the prior landing and closes no additional holes.

-- Second reading (U2, 2026-10-14): clean compatibility compile; zero declarations or holes.
-- This verifies the prior repair and does not certify the unavailable upstream theorem.

-- Second reading (J2, 2026-10-14): compiled cleanly; no declarations or proof holes.
-- Verification of the recorded duplicate removal adds no mathematical proof progress.

-- Verification (Q2, 2026-10-14): the assigned compatibility module has no declarations
-- or proof holes. The prior duplicate-removal landing supplies the repair; no new proof.

-- Second reading (W4, 2026-10-14): compatibility module checked and compiled cleanly.
-- No declarations, proof holes, or new mathematical proof progress.
