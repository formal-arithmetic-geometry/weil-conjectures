## What changed

Added the named intermediate theorem `CategoryTheory.brownHypotheses_structural` in
`BrownHypothesesStructural.lean`. It proves the coefficient-independent ambient
part of the Brown package: local smallness, triangulation, closure under
isomorphisms, fixed-universe coproducts, and idempotent completeness of the
localizing closure. The item's original module retains its original imports,
statement, definition, and proof hole; it privately imports the intermediate
module so the delivered diagnostic is attached to the item without changing the
public interface seen by its consumers.

## Proved and sorry left

Original holes closed: 0 of 1. The sole remaining hole is
`CategoryTheory.brownHypotheses` in the item's module (`sk-lem-brown-hypotheses`),
which is already marked `STATEMENT-DISPUTED`. Holes added: 0. The new structural
theorem is proved with no `sorry`.

## No longer needed

No original import, declaration, node, or dependency was pruned. The earlier
finite-field specialization, compactness equivalence, and experimental split
helpers are not part of this packet; they remain only in the preserved sandbox
backups and archived attempt logs.

## Where the brief, the DAG or earlier work was wrong

The source module already marks the arbitrary-field compactness assertion as
disputed, but the ordinary stage-3 delivery guard treated the pre-existing
marker as if no substantive diagnostic result could be delivered. The existing
worker packet proves the independent ambient portion and leaves the disputed
compactness theorem open. The compactness dependencies require finite-field or
cohomological-dimension hypotheses that are absent from the item's arbitrary
positive-characteristic statement, so completing that hole would require changing
the mathematical contract or supplying an unavailable theorem. This packet does
neither and does not claim a counterexample.

The dispatcher repair record now explicitly registers this already-disputed
diagnostic packet, allowing the normal delivery and independent preflight to
review it without weakening the proof guard. The current registry entry in
`coord/repairs.txt` explicitly requests acceptance of the compiled structural
packet despite the retained original hole. Earlier dry
runs rejected it with `FAILED: nothing is proved`; the resumed 2026-10-20 dry run
now passes and assigns the packet to independent CODEX review.
No launcher scripts or dispatcher settings were changed by this worker.

Current verification on 2026-10-20: the two delivery modules compile cleanly
through `lcompile.py --all` (structural 0.2 s, original module 2.4 s, exit 0).
A fresh separate axiom probe confirms
`brownHypotheses_structural` uses only `propext`, `Classical.choice`, and
`Quot.sound`. That probe is outside the delivered Lean roots.
The current consumer audit finds two calls to `brownHypotheses` in
`Sheaf.Paper.LocalizingExceptionalAdjoint`, both under the same arbitrary-field
hypotheses; restricting the theorem would not discharge these consumers.
The previous continuation recorded two dry runs killed with exit code 137.
The required initial dry run of this continuation completed successfully:
`OK (dry run): commit 6dde2ec990 compiles and passes the preflight; nothing pushed`.
It assigns the packet to CODEX review for its new module, declaration, node and
change record. No proof or signature changed during this continuation; the
retained packet was checked against the current source before delivery.

## New nodes

`h1-brown-hypotheses-structural` corresponds to
`Sheaf.SixFunctorsBasics.BrownHypothesesStructural` /
`CategoryTheory.brownHypotheses_structural`. Its node records the blueprint
location, proof dependencies, and Lean declaration. Its statement dependency is
`sk-def-localizing-closure`, which defines the actual `localizingClosureProEtale`
used here; the earlier `def-sfb-bounded-constructible-localizing-closure` reference
named a different closure of Dbc and has been corrected. No statement or definition
of the original item was changed. The proof import change is recorded in
`coord/changes/h1-brown-hypotheses-diagnostic-import.md`.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
