## What changed

Reapplied the retained proof to the current shared version of
`Sheaf.AlgebraicGeometry.TruncatedHigherImageQuasiCoherent`, as requested by the
return at delivery head `302a668a94`. Restored the finite-filtration helper and
proved `AlgebraicGeometry.truncated_higherImage_isQuasicoherent` by the existing
truncation hypercohomology spectral sequence, ordinary higher-image
quasi-coherence, kernel/cokernel closure, and finite extension induction.

The retained delivery needed two actual interface repairs against the current
source: the private helper now takes `PBCDecreasingFiltration M`, which is the
filtration returned by `exists_truncationHypercohomology`; the call to
`Scheme.Modules.isQuasicoherent_of_shortExact` now supplies only the short-exactness
proof because the short complex is implicit. The former helper was commented
out in the current shared file, so no active helper signature changes. The public
theorem signature and visibility are unchanged. No definitions or consumer
modules change; no interface change record is needed. Updated the existing node's
fourth proof step to name the current filtration type. Other node fields and the
unit route are unchanged.

## Proved and sorry left

Closed the one actual hole in the current shared module:
`AlgebraicGeometry.truncated_higherImage_isQuasicoherent`
(node `lem-pc-truncated-higher-image-quasi-coherent`).

The restored private `property_of_shifted_filtration` helper is completely proved,
as is the unchanged `property_pages`. No sorry remains in the item and no holes
are added elsewhere: one hole closed, zero holes added, zero statements split
off. The earlier report's count of two holes was stale: the helper was commented
out, rather than an active declaration containing sorry, in the current baseline.

The proof handles a zero-length filtration directly from its zero step. It also
handles total degrees below the truncation bound, negative spectral-sequence
indices, zero modules, and empty schemes without additional hypotheses. Choosing
a bounded-below representative is done only inside this theorem's proof; no data
definition or arbitrary witness from an unproved existence theorem is introduced.

## No longer needed

Removed the unused proof import `WeilConjectures.AlgebraicGeometry.Ample`.
No dependency nodes or additional modules are pruned. Every existing proof
node remains used: standard truncation, derived direct image, truncation
hypercohomology, ordinary higher images, kernels, cokernels, and extensions.
Removing the Ample import is not a claim that the module becomes unreachable
from all targets.

## Where the brief, the DAG or earlier work was wrong

The return was a real concurrent-file conflict: the original delivery was based
on `e32d4da34`, and another landing subsequently changed this module. This repair
starts from the current shared file and reapplies the proof there.

The retained second-reading claim that the proofs compile unchanged is no longer
true after the upstream synchronization. The first compile failed because
`DecreasingFiltration` no longer has `step`, `gradedPiece`, or `antitone_step`;
the spectral-sequence interface uses `PBCDecreasingFiltration`. After that repair,
the next compile exposed the extension theorem's now implicit short-complex
argument. Both issues are repaired locally without changing any public
statement. The retained second-reading section was removed because this changed
delivery still requires its own independent reading.

The DAG's extension dependency Lean record still shows the older explicit
short-complex binder. Its mathematical statement and the proof's use of extension
closure remain correct. The existing main node's proof and dependencies already
describe the argument, apart from naming the current filtration type in step 4.

Local sources checked: Stacks `perfect.tex`, lemma
`lemma-quasi-coherence-direct-image` (08D5), bounded-below paragraph;
`derived.tex`, `lemma-two-ss-complex-functor` (015J), finite induced filtrations;
and `coherent.tex`, `lemma-quasi-coherence-higher-direct-images` (01XJ), part (1).
The unit `sk-thm-picard-duality` has no realized entries containing this auxiliary
node, and its route is unchanged.

## Second reading by F1

1. **Signatures and accidental changes — pass.** Compared the delivered module
   with the shared repository version. The public theorem signature and all
   existing declarations are unchanged byte for byte. The private filtration
   helper is restored as a proof-local declaration, and the node records only the
   corresponding proof wording change.

2. **Proof and axioms — pass.** Compiled the module with `lcompile.py`; it exits
   successfully with no errors and no `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, or `extern`. A scratch audit of
   `AlgebraicGeometry.truncated_higherImage_isQuasicoherent` reports only
   `propext`, `Classical.choice`, and `Quot.sound`.

3. **Statements and split-offs — pass.** The target statement remains exactly the
   stated quasi-coherence assertion. No new public statement or split-off hole was
   added; the private helper is fully proved. Searches found no existing library or
   Mathlib theorem duplicating the helper or target.

4. **Route and pruning — pass.** The proof follows the existing truncation
   hypercohomology route through ordinary higher images, page kernel/cokernel
   closure, and finite extension induction. The `Ample` proof import is unused and
   removed; all listed proof dependencies remain used. The unit route is unchanged.

5. **DAG agreement — pass.** The node proof step now names the actual
   `PBCDecreasingFiltration` returned by the truncation theorem, matching the Lean
   proof. Its proof dependencies, origin, and unit metadata remain consistent.

Changed during second reading: repaired the filtration helper's current type,
updated the extension-closure call for its implicit short-complex argument,
removed the unused `WeilConjectures.AlgebraicGeometry.Ample` import, and updated
the existing node's proof-step wording.
