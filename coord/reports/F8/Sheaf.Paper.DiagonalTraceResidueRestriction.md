## What changed

Proved `AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceResidueRestriction`
in `Sheaf.Paper.DiagonalTraceResidueRestriction`, preserving its complete signature and
all existing public imports. The actual functor restricts module presheaves along the
constant residue cone, then takes vertical slices. It retains the original section
carriers and additive maps definitionally. The scalar normalization follows from
naturality of sheafification and the natural-number representative of a finite residue.
Exactness follows from continuous and cocontinuous vertical restriction on additive
sheaves, then reflection through the existing exact constant-scalar forgetful functor. All construction helpers are private and fully proved. The construction works at level zero
and on an empty scheme, without assuming that any coefficient section ring is nonzero.

Updated the assigned node's proof, proof dependencies and proof origin to this argument.
No existing definition, instance, signature, or other module was changed.

Validation: the complete proof compiled in 23.2 seconds with profiling enabled.
The delivery compile validates the final file after removing all profiling options.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceResidueRestriction`
(node `lem-sfb-diagonal-trace-residue-restriction`).

Holes closed: 1. Holes added: 0. Holes remaining in the delivered module: 0.
No split-off statements or new nodes.

## No longer needed

The proof does not use the full `lem-coef-semilinear-derived-sections` theorem
(`Sheaf.Paper.SemilinearDerivedSections`): the already proved ordinary evaluation API
of `def-coef-semilinear-system-models` supplies the sequence-site definitions and continuity;
continuous/cocontinuous vertical restriction on additive sheaves gives exactness directly. Nor does it use the equivalence and
abelian-calculus package `det-sp-coefficient-towers-abelian`
(`Sheaf.Paper.SmoothPurityCoefficientTowersAbelian.sp_coefficient_towers_abelian`):
exactness is reflected directly after additive-sheaf forgetting. These two planned
proof dependencies were removed from this node. Their modules are not withdrawn;
coefficient definitions and other ambient imports can still use them elsewhere.

No Lean imports were removed, and no whole module is claimed to leave the target closure.

## Where the brief, the DAG or earlier work was wrong

The proposed finite residue construction is valid and can be completed directly;
no eighth decomposition is needed. Its generic derived-section and coefficient-tower
existence packages are larger than the ordinary exactness argument requires.
The rework row names an older quarantined false-tail import. The current assigned
source is present, contains the residue-only statement, and has no such import;
this delivery proves that current statement without reinstating the obsolete import.
Its inherited public import closure is unchanged; no false-tail theorem is used by the proof.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
