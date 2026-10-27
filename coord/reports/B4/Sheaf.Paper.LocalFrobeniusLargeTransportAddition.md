## What changed

Replaced the hole in `WeilConjectures.LocalFrobeniusLarge.transportIterate_add` by
induction on the first positive index, generalizing the point object. The zero
case is the defining recursion. The successor case uses transport naturality,
inverse compositor associativity, and equality of the scheme powers, keeping
all endpoint identifications heterogeneous. Updated its node to match.

Added two constituent comparison laws in their own modules and nodes:
`LocalFrobeniusLargeTransportNaturality` and
`LocalFrobeniusLargeCompositionAssociativity`. Each is a genuine part of the old
first proof step, independent of the addition conclusion. No definition,
existing signature, or target statement changed.

## Proved and sorry left

Closed: `WeilConjectures.LocalFrobeniusLarge.transportIterate_add` (one original hole).
Added two holes: `WeilConjectures.LocalFrobeniusLarge.transportIterate_naturality`
(`lem-zl-large-transport-iterate-natural`) and
`WeilConjectures.LocalFrobeniusLarge.composition_inv_assoc`
(`lem-zl-large-composition-inverse-associativity`). No holes remain in the item
module. This is a decomposition: one hole closed and two strictly constituent
comparison obligations added, not a net decrease in holes.

## No longer needed

No original import was removed: the public coefficients import is required by
the unchanged statement. The old direct proof dependencies
`lem-trf-point-transport-composition`,
`lem-weil-point-automorphism-restriction-natural`, and
`lem-pod-integral-pullback-composition` are now below the two explicit comparison
laws. They remain needed there; no claim of pruning those modules is made.
No module or unit-route node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The finite/integral statements do not directly give the needed common-stage
naturality and associativity equations with the exact published comparisons.
The old first proof step contained this additional transfer argument. It is now
represented by two independently stated obligations. Neither is the original
addition theorem under another name. The unit and chapter routes are preserved.

## New nodes

`lem-zl-large-transport-iterate-natural`: the naturality square for any positive
transport iterate, on every common-stage arrow. Its source and complete proof
in words spell out the restriction, completed, rational, and stage transfer.

`lem-zl-large-composition-inverse-associativity`: inverse compositor associativity
on arbitrary composable scheme maps and actual common-stage objects. This is
independent of point transports, Frobenius powers, and the concatenation induction.
Its proof in words uses the stated integral associativity equation and cancels
the internal normalized object comparisons after localization and stage inclusion.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
