## What changed

Restored the complete assigned quarantined module Sheaf.Paper.TrfDevissageGeneration.
Repaired trfConstantClosureGenerators by expanding the retired
LocallyClosedStratification abbreviation to Scheme.Stratification. The historical
abbreviation is recorded verbatim in the landed F9 retirement record, and the
current FlatModel generator definitions already use Stratification. This one-token
repair preserves the elaborated mathematical definition; no theorem signature,
proof body, public import, coefficient model or target statement changes.

The original archived module fails its server compile at line 124 with
Unknown identifier LocallyClosedStratification. The repaired module compiles
through lcompile.py in 7 seconds with no errors or warnings. The downstream tool
and a separate search of lean/ and quarantine/ find no external Lean consumers.
The three DAG parents retain their generation dependencies. The item node's
lean.note records the restoration; its attachment, proof, proof_deps, statement
and unit route stay unchanged. The quarantine archive remains untouched.

Change record: coord/changes/F3-trf-devissage-stratification-restoration.md.
This is the assigned rework restoration with a definition repair, not a new proof
or a rebase-only delivery. No forced adaptations are needed. Independent review
is left to the delivery process; no second-reader claim is made.

Searches: leanfinder through msearch.py found no existing constant-generation
counterexample. Loogle through msearch.py found nilpotent endomorphism restriction
and quotient lemmas. Searches of the library for constant generation, Kummer
systems and the assigned declarations found no duplicate obstruction theorem.
No new proof route or intermediate lemma is introduced by the repair.

## Proved and sorry left

Holes closed: zero. Holes added: zero. Split off: zero.

The archived proof of AlgebraicGeometry.trf_devissage_generation is preserved and
compiles unchanged, together with its proved private coefficient-annihilation
and bounded-support helpers. It is not counted as a new proof in this delivery.

One existing sorry remains, unchanged:
AlgebraicGeometry.exists_trf_constant_coefficients_not_generating
(blueprint: lem-trf-devissage-generation). Its original source and complete
Kummer-counterexample proof plan remain in its docstring and node. No sorry is
inside a definition, and no new module or unproved declaration is added.

## No longer needed

None. No imports, nodes, modules or proof dependencies are pruned. In particular,
zero current Lean importers does not justify withdrawing this node: its generation
statement remains cited by lem-weil-finite-duality-site-comparison,
prop-trf-exceptional-kunneth and prop-trf-external-hom. The counterexample clause
also remains part of the unit statement.

## Where the brief, the DAG or earlier work was wrong

The quarantine source predates retirement of the LocallyClosedStratification
abbreviation and therefore cannot be restored verbatim against the current
library. Expanding its old definition to Stratification is sufficient; the
single-file compiler confirms it. This does not replace the old notion by the
distinct, weaker FiniteLocallyClosedStratification.

The rework row says the item did not itself fail the earlier batch; that explains
its quarantine history but does not imply the archived file currently compiles.
The existing counterexample hole is explicitly retained under the listed-repair
exception; this packet claims no new theorem proof or sorry reduction.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
