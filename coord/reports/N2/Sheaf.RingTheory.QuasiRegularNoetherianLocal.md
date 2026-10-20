## What changed

Proved `RingTheory.Sequence.quasiRegularNoetherianLocal` without changing its statement.
A proved private helper transports regularity of a polynomial variable through a bijective
associated-graded map: a zero product forces its other factor into every ideal power,
and separatedness then makes it zero. The main proof applies this helper in every prefix
quotient using `Ideal.quasiRegular_prefix_quotient`, Krull intersection, and Mathlib's
local-ring upgrade from weak regularity to regularity.

Added the proof-only import `Mathlib.RingTheory.Ideal.Quotient.Noetherian` for Noetherian
quotient instances. Updated the existing node's proof and origin to describe the argument.
The file compiles with no errors or warnings through `lcompile.py`.

## Proved and sorry left

Closed 1 of 1 holes: `RingTheory.Sequence.quasiRegularNoetherianLocal`.
Added 0 holes; split off 0 statements. There are no `sorry`s in the delivered Lean file.
The proof uses the existing stated theorem `Ideal.quasiRegular_prefix_quotient`, whose
proof remains a separate item and is unchanged by this delivery.

## No longer needed

Removed the proof-only import `Mathlib.RingTheory.Finiteness.Defs`; the proof uses the
Noetherian local ring specialization of Krull intersection, with the required module
instances available from the retained imports. No planned mathematical dependency,
node, or module is pruned: the prefix-quotient and associated-graded structure declarations
are used, and Krull intersection is supplied directly by Mathlib.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The plan can avoid choosing the least failed filtration
level: induction shows that a factor of a zero product lies in every power. It can also
apply Krull intersection over each Noetherian local quotient ring directly, avoiding
an explicit comparison between ideal powers and powers acting on an A-module.
The empty-sequence case is covered by the same Mathlib local-ring criterion.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
