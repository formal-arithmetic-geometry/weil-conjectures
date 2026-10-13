## What changed

Replaced the sorry of `AlgebraicGeometry.Scheme.picardCupPairing_baseChange`
with a complete Lean reduction. The statement and its public import are unchanged.
The proof privately imports `Sheaf.AlgebraicGeometry.PicardPairingPullbackCoherence`.
It proves inverse and forward tensor-comparison naturality locally, and proves
injectivity of pullback on pairings by naturality and cancellation of the invertible
structure-sheaf adjunction unit. It expands uncurry/curry, applies the existing
`picardPushforwardPairing_counit`, and substitutes the two one-coefficient counit
identities into the tensor/unit coherence identity.

Added `PicardBaseChangeCounit` and `PicardPairingPullbackCoherence`, with real
square and coefficient isomorphisms constructed from existing composition maps.
No definition chooses an arbitrary existence witness. Updated the target node's
proof route and added nodes for the two intermediate statements.

## Proved and sorry left

Closed one existing hole: `AlgebraicGeometry.Scheme.picardCupPairing_baseChange`.
There is no sorry left in the assigned module.

Added two holes, so this delivery is a decomposition, with net holes closed minus
added equal to -1, not an unconditional proof of the full import closure:

- `AlgebraicGeometry.Scheme.Modules.picardDirectImageBaseChangeMap_counit`
  (`lem-sc-picard-base-change-counit`, `PicardBaseChangeCounit`). This computes the
  adjoint of a single coefficient map and involves no pairing or duality.
- `AlgebraicGeometry.Scheme.Modules.picardPairing_pullback_coherence`
  (`lem-sc-picard-pairing-pullback-coherence`, `PicardPairingPullbackCoherence`).
  This transports an arbitrary pairing with arbitrary coefficient maps; its
  conclusion contains no base-change map, adjunction unit, or adjunction counit.

These are the only sorries added or left in delivered files. Both apply to arbitrary
modules and zero pairings; no flatness, local freeness, or invertibility of beta is
needed. Empty schemes are included by the same functorial identities. Source and
complete proof calculations are in their docstrings and nodes.

## No longer needed

No existing import was removed: `PicardCanonicalBaseChange` is still needed for
its definitions, and its public import remains unchanged. The target's direct
proof dependency on `lem-weil-pbc-module-base-change-map-pasting`
(`Sheaf.AlgebraicGeometry.ModuleBaseChangeMapPasting`) is no longer needed for
this proof: it uses counits and tensor/unit coherence directly, not pasting of
base-change maps. This is a local DAG edge pruning; no global module pruning is
claimed, since other import paths may still need that module.

`lem-weil-pbc-module-base-change-map-open-restriction` remains needed indirectly:
it defines `moduleBaseChangeMap`, used by the canonical comparison module and
by the new counit statement. It has not been pruned.

## Where the brief, the DAG or earlier work was wrong

The existing proof dependencies expose naturality and pasting, but do not state
the vertical counit identity for the explicit Picard comparison, or the required
monoidal coherence of its composition/square maps. The target node's second step
combined both calculations in one prose paragraph. The two new statements make
these distinct parts explicit; neither restates the original cup compatibility.

Read Stacks Tags 0BDP, 0095, 0096 and 08HY. Tag 08HY describes the adjoint of a
base-change map via the pulled counit; the new underived calculation identifies
it with the library's horizontally defined mate. Tag 0095 supplies the tensor
formula; composition and adjunction from 0096 supply the comparisons. The
coherence proof is categorical glue for the final cup-product paragraph of
0BDP, not a new geometric hypothesis. The unit record `sk-prop-av-cube` has no
realized node entries here; its statement and unit route are preserved.

The shared build initially lacked `PicardCanonicalBaseChange.olean`; it refreshed
and the block cleared. No dependency copies or tool changes were used.

## New nodes

`lem-sc-picard-base-change-counit` is in
`dag/nodes/sec-abelian-varieties/lem-sc-picard-base-change-counit.json` and its
statement module is `lean/Sheaf/AlgebraicGeometry/PicardBaseChangeCounit.lean`.
It isolates the one-coefficient mate/counit calculation and constructs the two
comparison isomorphisms used by both remaining steps.

`lem-sc-picard-pairing-pullback-coherence` is in
`dag/nodes/sec-abelian-varieties/lem-sc-picard-pairing-pullback-coherence.json`
and its statement module is
`lean/Sheaf/AlgebraicGeometry/PicardPairingPullbackCoherence.lean`. It isolates
three tensor/unit coherence identities and their naturality calculation. The
new node search covers the existing Picard and module base-change modules,
Mathlib mate and composition lemmas, and external LeanFinder/Loogle searches.

No change record is required: no existing statement, definition, signature or
visibility changed. No existing module was adapted.

## Second reading by W3

1. Compared every delivered module with the repository. Only
   `PicardCupPairingBaseChange` exists there: its public import, existing docstring,
   theorem signature (byte for byte), visibility and definitions are unchanged.
   The additions are a private proof import, three private proved helpers and the
   theorem body. The other two modules and their definitions are new. Read the
   landed `j1-picard-base-change-comparisons.md` change record; this delivery uses
   its current canonical definitions and does not undo an adaptation. Verdict: pass.
2. Compiled all three files through `lcompile.py --all`: 3.5, 2.6 and 13.3 seconds,
   no errors or warnings. Inspected every proof and construction: exactly the two
   reported named public theorem holes; no hole in data, forbidden declaration or
   arbitrary existence witness. Scratch `#print axioms` checks show only `propext`,
   `Classical.choice`, `Quot.sound` for both new isomorphisms; these plus `sorryAx`
   for both split theorems and the assigned theorem. The private helpers are
   kernel-checked cancellation and naturality proofs. Verdict: pass as decomposition,
   not as a sorry-free import closure.
3. Read both new signatures, their docstring calculations and nodes against the
   definitions of the maps. The counit identity is the vertical mate of the
   horizontally defined map, followed by counit naturality for the coefficient
   comparison. The coherence identity transports an arbitrary pairing across
   the square: cancel the tensor comparison in `hg`, then use tensor naturality
   and the coefficient comparison. Tested the formulas mathematically for identity
   arrows (all transported comparisons cancel), zero coefficients, zero pairings
   (`g = ev = 0`), and empty schemes (all maps unique). No flatness, finite rank,
   invertible beta or dual comparison is used. The two statements isolate distinct,
   strictly smaller parts of the argument and neither is a renamed cup theorem.
   Repeated searches with different words using LeanFinder (Beck--Chevalley,
   transpose and counit), Loogle (`conjugateEquiv`, unavailable as an identifier),
   and grep (`pullbackComp.*(unit|tensor)|counit.*mate|mate.*counit`). Read the actual
   `mateEquiv_counit` and `mateEquiv_counit_symm` declarations and the existing
   base-change pasting proof; the generic counit identity does not itself identify
   the explicit square comparison. Searched both library roots and upstream
   module files for the new names and composition/coherence variants: no exact
   duplicate. Read Stacks [0095](https://stacks.math.columbia.edu/tag/0095),
   [0096](https://stacks.math.columbia.edu/tag/0096),
   [08HY](https://stacks.math.columbia.edu/tag/08HY), and
   [0BDP](https://stacks.math.columbia.edu/tag/0BDP): the underived and tensor
   calculations are agent-written categorical glue, not claims that these tags
   literally state the Lean formulas. Verdict: pass.
4. Read the proof from the assigned hole down: injectivity on pairings, existing
   cup-counit identity, tensor naturality, two one-coefficient identities, then
   coherence. No shorter proved library route was found. Each public import of a
   new file is needed by its signatures; the assigned file's additional import
   is private and needed only for its proof. Checked every old `proof_deps` edge:
   cup definitions and canonical comparisons remain; open-restriction is still
   needed indirectly for `moduleBaseChangeMap`; pasting is unused by this proof.
   No module pruning is claimed. Read `sk-prop-av-cube.json`: its `realized`
   statement and step arrays are empty; this local reduction changes no unit route.
   Verdict: pass after retaining the canonical-comparison dependency below.
5. Compared the node signatures verbatim with the Lean theorem headers, checked
   new-node fields, the proof-step dependency unions, chapter and unit. The target
   node omitted canonical comparisons although its proof uses their definitions
   and tensor-comparison naturality. Restored that dependency in the first step
   and `proof_deps`. No existing statement fields changed. Verdict: repaired.

Second-reading changes: restored the target node's canonical-comparison proof
edge and added this independent review. No delivered Lean proof needed repair.
A quick attempt to close the counit hole using the existing scratch mate reduction
exceeded the 60-second local compile limit; that experiment is not delivered and
no hole is claimed closed by it. The delivered three-module set remains the
compiling decomposition: one existing hole closed, two holes added, net -1.
