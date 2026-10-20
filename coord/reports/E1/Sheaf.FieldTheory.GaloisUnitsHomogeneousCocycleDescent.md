## What changed

Retired Sheaf.FieldTheory.GaloisUnitsHomogeneousCocycleDescent in favour of
WeilConjectures.FieldTheory.GaloisUnitsHomogeneousCocycleDescent, as instructed by
the human's 2026-10-20 Hand-off. The only direct consumer,
Sheaf.FieldTheory.GaloisUnitsHomogeneousComparison, now imports the official twin
privately and packages Field.galoisUnitsH2EquivTwoCocycleClasses into Nonempty.
Its theorem signature, docstring and public imports stay identical.

Repointed lem-sc-galois-units-homogeneous-cocycle-equivalence and
lem-sc-galois-units-homogeneous-cocycle-descent to the twin's explicit equivalences.
Updated the comparison node's proof dependency to the descent result actually used.
Listed the retired copy in deleted.txt and removed its sandbox source.
No upstream or target files changed.

Change record:
coord/changes/retire-galois-units-homogeneous-cocycle-descent-20261020.md.

## Proved and sorry left

Field.nonempty_equiv_galoisUnitsH2_twoCocycleClasses remains fully proved, now from
Field.galoisUnitsH2EquivTwoCocycleClasses. The retired copy initially had zero holes.
Holes closed: zero. Holes added: zero. Split off: zero. No sorry remains in the
adapted consumer, and neither upstream equivalence uses sorry.

## No longer needed

- Module and private consumer import
  Sheaf.FieldTheory.GaloisUnitsHomogeneousCocycleDescent: withdrawn, with all users
  adapted to the official twin in this packet.
- Field.nonempty_equiv_galoisUnitsHomogeneousCocycles_twoCocycle and
  Field.nonempty_equiv_galoisUnitsH2_twoCocycleClasses_of_cocycle_equiv: the removed
  wrappers have no remaining callers. Their two nodes remain and now point to the
  corresponding explicit upstream constructions.
- The consumer's separate application of cocycle equivalence is unnecessary:
  upstream descent constructs its canonical cocycle equivalence internally.
  The cocycle equivalence node is retained, not withdrawn.

The coefficient and two-cocycle definition nodes remain needed. No source-library
module or declaration is deleted.

## Where the brief, the DAG or earlier work was wrong

The retained attempt predates the explicit RETIRE assignment and contained a no-op
packet. Its required initial dry run again reported "FAILED: nothing is proved."
The current packet performs the requested retirement instead of claiming a new
proof. The twin lacks the two old theorem names because it exposes stronger
explicit equivalences; no fallback sorry is necessary.

Validation: the sole consumer compiled through lcompile.py without errors or
warnings (1.5 seconds). Its import closure contains neither the retired copy nor
any pair of Sheaf/upstream twins. A full Lean source scan with this packet overlaid
found no remaining reference to the retired module or either removed theorem.
The required deliver3.py --no-push run passed compilation and preflight at
80bc76259d (CODEX: retirement, consumer adaptation, node and change-record review).
The delivery tool reported no forbidden axiom.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
