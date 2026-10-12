## What changed

Proved `CategoryTheory.resolution_homology_transport` with its existing signature
unchanged. A comparison from the chosen injective resolution to the prescribed
resolution intertwines their augmentations. Naturality of the derived unit then
identifies the derived comparisons. Upstream quotient-homology and prescribed-resolution
naturality give the homology comparison; cancelling the inverse map-extension and
extension isomorphisms completes it. The original final quotient-homology transport
argument is retained.

The first submission's unproved `resolution_homology_transport_core` was proved during
second reading, then folded into a local `have hcore` in the existing theorem. Its new
module and node were removed from the delivery. Removed the redundant direct proof
import of `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`:
`CanonicalResolutionDerivedIso` already publicly imports it. Updated the existing
node's proof steps, proof dependencies, and proof origin to match the complete proof.
No statements, definitions, public imports, or target interfaces change.

## Proved and sorry left

Hole closed: `CategoryTheory.resolution_homology_transport`
(node `lem-pc-canonical-resolution-homology-comparison`).

Holes added: none. Sorries left in delivered modules: none. One of one original holes
is closed; this is a proof, not a decomposition. The discarded provisional
`CategoryTheory.resolution_homology_transport_core` is not delivered.

Local compilation passes without errors or warnings. A scratch copy with
`#print axioms CategoryTheory.resolution_homology_transport` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

Removed the redundant direct import
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`, while
retaining its declarations through the public import of `CanonicalResolutionDerivedIso`.
This removes no module from the targets' import closure.

Removed the provisional import, module, and node
`Sheaf.CategoryTheory.CanonicalResolutionHomologyCore` /
`lem-pc-canonical-resolution-homology-comparison-core` from the sandbox delivery.
These were not part of the original library or original proof dependencies.

Every original proof dependency remains used: `def-pc-canonical-resolution-derived-iso`,
`def-sp-injective-resolutions`, `lem-sp-derived-functor-single-identification`, and
`lem-sp-derived-well-defined`. No original dependency node or reached module is pruned.

## Where the brief, the DAG or earlier work was wrong

The first submission's core theorem had the original hypotheses and left-hand side,
with the right-hand side changed only by definition expansion and quotient-homology
naturality. Leaving it unproved did not discharge the actual resolution comparison.
Its report overstated progress, and its node's proof steps did not agree with the
changed proof dependencies. The original plan is sufficient: Mathlib's comparison map
and upstream `isoRightDerivedObjCochainComplex_inv_naturality` supply the missing
argument. No new statement is necessary.

## Second reading by H3

1. Compared the delivered module with the repository's version. The existing theorem's
   signature is byte for byte identical (checked programmatically); no definition or
   public import changed. There are no forced adaptations or statement change records.
   Verdict: pass.

2. Compiled the initial two modules, then the repaired single-module delivery and its
   scratch axiom-check copy through `lcompile.py`. The final module compiles without
   warnings, contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or
   `extern`, and introduces no data definition. `#print axioms` reports only the three
   allowed axioms. Verdict: pass.

3. Rejected the provisional unproved core as an equivalent transport formulation,
   proved it, and folded it into the existing proof. Repeated searches with Lean Finder
   (any injective resolution and augmentation compatibility), Loogle (upstream
   cochain-complex inverse naturality), and `rg` on the library and upstream sources.
   Finder returned the classical resolution API; Loogle does not index the upstream
   identifier. Reading upstream `PlusSingle.lean` found the inverse naturality lemma
   and the chosen-resolution naturality argument used here. No new statement or hole
   remains. Checked degree zero: no positive-degree or left-exactness hypothesis is
   used; the same functoriality and inverse cancellations apply at n = 0, for the chosen
   resolution itself, and for a zero additive functor. Verdict: pass after repair.

4. The complete proof follows the original augmentation/unit/homology plan using
   Mathlib and proved upstream declarations. Imports are minimal (one public import).
   All four original dependency nodes are retained and used. Read
   `dag/units/sk-thm-picard-rr.json`: its realized statement/step lists are empty; this
   supporting comparison realizes none of them and changes no unit route. No reached
   library module is claimed as pruned. Verdict: pass.

5. Updated the existing node's `proof`, `proof_deps`, and `proof_origin` to match the
   actual comparison and cancellations. Their dependency union is exactly the four
   recorded original dependency nodes. The Lean statement recorded in the node stays
   unchanged. Removed the provisional new node; no new-node obligations remain.
   Verdict: pass after repair.

Second reading changed: closed the core proof, folded it into the original theorem,
removed its provisional module/node/import and one redundant direct import, corrected
DAG proof metadata, and replaced the inaccurate progress report. No signature changed.
