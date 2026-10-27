## What changed

Completed the ordinary dense-open direct-image finiteness proof in
`Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness`, preserving its public statement
and all public imports. Added only proof imports and proved private helpers.

The proof encodes native adic modules as continuous condensed Qbar modules. Finite residue
field direct-image finiteness follows from the finite-coefficient etale open theorem and
etale/pro-etale comparison. The integral residue criterion and the actual reduction mate
then give bounded constructibility of the integral image. Constructible integral models,
qcqs rational-localization continuity and finite-extension descent give bounded
constructibility for Qbar coefficients. The native derived encoding reflects the result.
The DAG proof and proof dependencies record this argument.

The final proof compiled cleanly through `lcompile.py` in 34.3 seconds before the last
import cleanup. Large scalar-change comparisons are locally irreducible, and the
continuous integral step caches its module tensor and flat-resolution structures.
This resolves the earlier 60-second elaboration timeout without increasing the limit.
No auxiliary modules or intermediate holes are delivered.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.bounded_constructible_rightDerivedFunctor_adicLowerStar_of_denseOpenImmersion`.
Holes closed: 1. Holes added: 0. Holes remaining in delivered Lean modules: 0.
All private helpers have complete proofs. Existing imported residue/completion and native
coefficient comparison obligations retain their own separately assigned declarations;
this delivery proves the assigned theorem from those declarations as required in stage 3.

## No longer needed

No original imports were removed: they belong to the unchanged statement interface.
The final packet also excludes the unused new modules and dependency-interface edits
from the interrupted attempt; the existing shared interfaces suffice. The private
exposure of `Sheaf.SixFunctors.ProEtale.DerivedCompletion` was removed, retaining its
ordinary proof import.
The proposed global lisse lattice input
`lem-weil-pbc-lisse-e-constructible-integral-lattice`
(`Sheaf.Paper.LisseEConstructibleIntegralLattice`) is not used or imported: the proved
constructible-complex integral-model theorem handles general constructible inputs.

The direct proof no longer calls `lem-kun-0f10`
(`Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension`) or
`lem-sf-integral-direct-image-constructible` (`Sheaf.Paper.SfIntegralDirectImageConstructible`).
Their roles are supplied by finite-field open finiteness, finite Tor amplitude over the
residue field, and the integral residue criterion. Those modules remain transitive
imports of existing infrastructure; this packet does not withdraw them or claim they are
globally unused. `def-weil-algebraically-closed-coefficients` remains a statement dependency
and transitive coefficient infrastructure, but its abstract common-stage category is not
used as a direct proof input. The concrete finite-subfield descent and actual qcqs
coefficient-change mate are used instead.

## Where the brief, the DAG or earlier work was wrong

The original plan named a lattice theorem for lisse objects although the input is only
constructible. The available constructible-complex integral-model theorem is the needed
replacement; no global lisse lattice is asserted. The generic condensed finiteness theorem
has positive-characteristic and separatedness assumptions absent here, so it cannot be
applied directly. The present proof uses the characteristic-independent finite-coefficient
open theorem and qcqs coefficient comparisons. No hypotheses are added to the assigned
statement, no definitions or other modules are changed, and the unit route is preserved.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
