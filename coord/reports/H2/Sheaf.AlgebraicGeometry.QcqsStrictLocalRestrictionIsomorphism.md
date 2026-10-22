## What changed

Submit the required withdrawal of
Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionIsomorphism via deleted.txt.
The current source is already an empty withdrawal stub, following reviewed landing
20261022T002436-L-1930859 (S2) and subsequent landing
20261022T011827-L-3218894 (E4). This packet does not claim those earlier changes
as new work. The dispatcher still assigns this retirement.

The former consumer Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison is
included byte-for-byte from the current source. Its already-landed replacement
argument uses the official set comparison and canonical small/full-colimit
transport, preserving its complete small-model public interface. It no longer
imports or calls the withdrawn declaration. The official source consumer imports
WeilConjectures.AlgebraicGeometry.QcqsStrictLocalRestrictionIsomorphism and applies
its theorem directly. Neither upstream files nor target statements change.

Validation: a fresh sandbox copy of the former consumer compiled through
lcompile.py in 9.1 seconds with exit code 0. Its theorem's printed axioms are
exactly propext, Classical.choice, and Quot.sound. A fresh scan of both Lean roots
found zero imports of the withdrawn module; a JSON scan of all DAG nodes found
zero lean.module attachments to it. The existing item node points to the official
twin and carries the independent retirement review. The parent comparison node
already records its replacement proof and removes the retired theorem from its
proof dependencies. Scratch verification files are outside the delivery's lean/.

## Proved and sorry left

Assigned module: 0 declarations and 0 holes. Holes closed: none (0 of 0).
Holes added: none. Statements split off: none. No sorry remains in the included
consumer or the adopted isomorphism theorem.
AlgebraicGeometry.Etale.exists_qcqsStrictLocalModuleComparison and
AlgebraicGeometry.Etale.isIso_qcqsStrictLocalRestriction_of_formula are already
proved; their proofs and signatures are unchanged by this packet.

## No longer needed

Withdraw lean/Sheaf/AlgebraicGeometry/QcqsStrictLocalRestrictionIsomorphism.lean.
There are no remaining Lean importers or DAG Lean attachments to this copy.
The small-model consumer's separate restriction-isomorphism dependency was
already removed by the reviewed replacement argument. Its other dependencies
remain needed; no further module or node is pruned. The blueprint unit route
remains unchanged. The withdrawal tool represents deletion by an empty module.

## Where the brief, the DAG or earlier work was wrong

This is a zero-hole retirement, not a proof repair. The retirement row remains
in coord/retire-items.tsv after two recorded landings, so this assignment repeats
completed work. There is no matching rework row or current H2 return requesting a
new mathematical repair. This packet explicitly records that state while
performing the requested withdrawal through the required delivery tool.
No statement is disputed, weakened or replaced by an assumption. No definition
is hollowed, and no source-library declaration is changed.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
