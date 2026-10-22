## What changed

Proved `WeilConjectures.sfCompleteDirectImage_reduction` with its statement unchanged.
The proof compares the completed and finite coefficient presentations through ordinary
section-normalized squares, lifts their coherence through the universal derived units,
and transports the specified projection-formula adjunct through the scalar adjunctions.
It uses the existing completed-coefficient pushforward comparison to preserve completeness.
Finally it pushes the augmented Roos triangle and compares it with the prescribed triangle
by the triangle five lemma. Every auxiliary result is private and proved in this module.
The original two public imports remain unchanged; added imports serve only the proof.
The proof uses the localization and derived-functor APIs without unfolding their data.
The node's proof and proof dependencies now describe this explicit argument.
The preflight-requested change record is
`coord/changes/e1-sf-complete-direct-image-proof-commands.md`; it records the private
helper commands, transparency controls, instance selections, and unchanged consumer.

## Proved and sorry left

Closed the one original hole in `WeilConjectures.sfCompleteDirectImage_reduction`
(node `lem-sf-complete-direct-image-reduction`). Added zero holes and split off zero
statements. No `sorry` remains in the delivered module. Existing stated dependencies,
including the completed-coefficient comparison and finite projection formula, are used
as the stage-3 brief prescribes.

## No longer needed

The standalone DVR proof is not repeated or directly imported: the existing completed
finite projection-formula theorem already packages its perfect-quotient argument.
Accordingly `lem-weil-l-adic-extension-integers-dvr` is removed from this node's direct
proof dependencies; it remains needed below the theorem used here. No module is withdrawn
or claimed to be globally pruned. No original import is removed. Redundant private
imports of `SfDerivedDirectImage` and `RightDerivedFunctor.Triangulated` are avoided:
the original public import and `CompletedTowerDirectImage` already supply these APIs.

## Where the brief, the DAG or earlier work was wrong

The original plan's normalization step required an explicit coherence argument: arbitrary
isomorphisms of derived functors do not identify the specified scalar-adjunction mate.
The proof supplies that argument on K-injective representatives, using the actual chosen
cochain units and localization factors. Finite sf coefficient modules also require the
existing explicit K-injective-resolution construction at this application. No statement
or definition repair, target change, forced adaptation, or new public declaration was
needed.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
