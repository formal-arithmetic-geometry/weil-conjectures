## What changed

Restored `lean/Sheaf/Paper/A1FiniteWeilSectionsDecomposition.lean` from its
quarantine archive and completed the assigned timeout repair. Changed
`a1FiniteCohomologyFunctor`, `a1FiniteStalkFunctor`,
`a1FiniteQbarCohomologyFunctor` and `a1FiniteQbarStalkFunctor` from inferred
abbreviations to explicitly typed ordinary definitions, preserving their bodies.
Enabled normal transparency and removed seven unused private imports.

Profiling identified repeated expansion of the stalk-functor object and module
structures in the Qbar statement. The unchanged archive compiled in 24.5 seconds
against this published build; the repaired whole module compiled cleanly in
12.8 seconds. The historical rework entry records a 60-second timeout.
No compile limit was changed and no declaration was split.

Change record: `coord/changes/C2-a1-finite-sections-functor-elaboration.md`.
It contains the exact old/new definitions and the reverse import closure across
both live and quarantined sources. The three direct consumer modules were read;
none uses a changed functor name yet, so no adaptation is needed.

## Proved and sorry left

This is a timeout rework delivery: zero of two existing theorem holes closed;
zero holes added or split off. Both retained holes belong to
`lem-a1-finite-weil-sections-decomposition`:

- `WeilConjectures.a1FiniteWeilSectionsDecompositionRational`.
- `WeilConjectures.a1FiniteWeilSectionsDecomposition`.

Both remain named public theorems with their source and full proof descriptions.
All data definitions remain genuine constructions, with no new choice or sorry.

## No longer needed

Removed these unused private imports:

- `Sheaf.Paper.ZlFiniteAdicDirectImage`.
- `Sheaf.AlgebraicGeometry.ClosedPointField`.
- `Sheaf.Paper.IntegralPullbackComposition`.
- `Sheaf.Paper.ProperCoincidenceFrobenius`.
- `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso`.
- `Mathlib.FieldTheory.Finite.GaloisField`.
- `Sheaf.SixFunctors.FrobeniusCohomologyTransport`.

The existing declarations elaborate from the retained public imports. These
removals concern the current module's direct import list; they do not withdraw
any declaration, DAG dependency, planned proof step, or module elsewhere in the
library. In particular, the finite-geometric-sections/point-orbits and the
proper-Weil-iterate-germ dependencies are preserved for the mathematical proof.
No DAG node or entire library module is pruned by this repair.

## Where the brief, the DAG or earlier work was wrong

The timeout is load-sensitive: the current unchanged archive compiled within
60 seconds, but still performed unnecessary eager unfolding and loaded unused
proof dependencies. This delivery changes those actual causes, rather than
only restoring or rebasing the file.

The current node's two new assembly dependencies,
`lem-a1-finite-geometric-sections-and-point-orbits` and
`lem-a1-proper-weil-iterate-germ-formula`, have neither Lean attachments nor
Mathlib matches in the shared snapshot and are not assumed. They cannot yet be
imported as suggested by the general stage-3 brief. Their statements and the
item's own Lean attachment and dependency records are preserved; no substitute
statement or relocated hole is introduced. This repair therefore reports its
actual two retained holes and does not claim to prove the decomposition.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
