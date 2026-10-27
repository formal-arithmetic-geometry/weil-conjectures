## What changed

Proved `AlgebraicGeometry.Scheme.adicResidue_vanishing_successor` without changing its
signature. A termwise-flat K-flat representative is chosen directly over the completed
coefficient sheaf on the actual slice. Natural tensor cancellation identifies its
coefficient tensors with the specified derived reductions. K-flat change of rings,
acyclic K-flat tensor vanishing, and the homology exact sequence complete the argument.

Added `Sheaf.Paper.AdicResidueCoefficientSequence` for the ordinary coefficient sequence.
Its proof constructs the quotient kernel as an ideal, descends its action to the residue
quotient, proves the constant-module scalar comparisons, and applies exact sheafification,
slice restriction, and scalar restriction. The unit and quotient actions are retained.
The construction covers the zero ideal and unit ideal without domain or regularity
assumptions. All helper definitions contain explicit constructions; every private helper
is proved. New imports in the assigned module are proof imports; its original public
import is preserved. No existing statement, definition, consumer, or source-library file
is changed. Updated the assigned DAG proof to this route.
The acyclic K-flat tensor theorem is reused from its proved adopted-source module
`WeilConjectures.Algebra.Homology.AcyclicKFlatTensor`; it realizes the same assertion as
`lem-pur-acyclic-kflat-tensor-arbitrary` (the legacy K-flat predicate is definitionally the
source predicate at the common slice/coefficient universe).

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.adicResidue_vanishing_successor`
(`lem-sfb-adic-residue-vanishing-successor`).

Also proved the new ordinary coefficient theorem
`AlgebraicGeometry.Scheme.adicResidue_coefficient_sequence`
(`lem-sfb-adic-residue-coefficient-sequence`).

No `sorry` remains in either delivered module, and no new hole is added. This is a proof,
not a decomposition into new unproved statements. The final server compilation of both
modules passed without warnings: the coefficient sequence took 44.3 seconds and the
successor proof took 25.7 seconds, each below the 60-second limit.

## No longer needed

The original plan's use of `lem-weil-pbc-constant-module-section-properties` is unnecessary:
exact constant module sheafification suffices; no exactness of sections is used.
The original direct proof dependency `lem-pur-derived-change-of-rings` is replaced by the
more specific natural tensor cancellation and all-K-flat change-of-rings declarations.
The flatness of the constant-to-completed coefficient map and its finite comparison are
not used, because the resolution is taken directly over the completed slice. The node
`lem-weil-pbc-constant-completion-equivalence` remains needed for the coefficient definitions
and their specified derived computation comparisons.

No original import was removed (the file had only its public statement import), no module
is withdrawn, and no globally pruned module is claimed. The unit's prescribed route stays.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The DAG's route through a restricted
constant-coefficient resolution was longer than necessary. Resolving directly over the
completed slice avoids that comparison while proving the same unbounded statement.

## New nodes

`lem-sfb-adic-residue-coefficient-sequence` is the ordinary consecutive coefficient sequence
with its residue kernel action. It contains no derived complex or vanishing assertion and
is strictly a coefficient-construction step in the original successor argument. Its module
is proved in this delivery. No change record is needed because existing interfaces are
unchanged.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
