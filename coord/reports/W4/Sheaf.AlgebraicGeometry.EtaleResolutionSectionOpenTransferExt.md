## What changed
The existing target signature and public imports are unchanged. Its proof now rewrites
by `AlgebraicGeometry.Etale.resolutionSection_transfer_ext`, then applies
`AlgebraicGeometry.Etale.etaleOpenObjectCohomologyMap_pullback` to the represented Ext
class. Both new imports in the target are proof-only.

Added the real construction `AlgebraicGeometry.Etale.etaleOpenFreeSheafPullback`:
apply the inverse-image adjunction unit to the identity section, restrict along
`openSectionPullback`, and use the inverse sections equivalence. Its body has no
postponed proof, existence choice, or `sorry`. The two independent remaining calculations
are stated in their own modules, each with its complete mathematical proof in words
and its matching DAG node. The open-object calculation imports the generic exact-functor
composition theorem only for its proof plan.

## Proved and sorry left
Closed the original hole in
`AlgebraicGeometry.Etale.resolutionSection_transfer_open_ext` (one of one item holes).
Added exactly two named holes:

- `AlgebraicGeometry.Etale.resolutionSection_transfer_ext`, node
  `lem-weil-pbc-etale-resolution-section-transfer-ext-class`: equality in Ext before
  open localization; it does not use either open cohomology map.
- `AlgebraicGeometry.Etale.etaleOpenObjectCohomologyMap_pullback`, node
  `lem-weil-pbc-etale-open-object-cohomology-pullback`: compatibility of the
  open-object map for an arbitrary Ext class; it has no injective resolutions,
  augmentation-preserving chain map, cocycles, or section-transfer hypothesis.

This is a decomposition, not a completed mathematical proof or net progress:
one original hole closed and two holes added, hence net -1 in this delivery's
import closure. The constructed free-open pullback morphism is fully defined.
The first reader's equivalent reformulation
`resolutionSection_transfer_open_ext_of_eq` and its node/module were removed;
they were never library declarations and add no delivered hole.

## No longer needed
No original public import is removed and no original module is pruned. The unused
first-reader proof-only import `EtaleResolutionSectionTransferOpenExtCore` is removed,
together with that undelivered module and node.

All seven old direct `proof_deps` are replaced by the two genuinely intermediate
identities. Specifically:

- `def-weil-pbc-cohomology-pullback`
- `def-weil-pbc-etale-open-comparison-data`
- `def-weil-pbc-etale-open-object-cohomology-map`
- `def-weil-pbc-etale-resolution-section-transfer`
- `def-weil-pbc-inverse-image`
- `lem-weil-pbc-ext-exact-functor-composition-comparison`
- `prop-weil-pbc-inverse-image-exact`

They remain needed in the intermediate nodes or their construction; this replacement
of direct proof edges does not prune them from the target closure.

## Where the brief, the DAG or earlier work was wrong
The first-reader split was a restatement: its sole new hypothesis replaced
`sectionsEquiv fY = transferredSection` with the logically equivalent
`fY = sectionsEquiv.symm transferredSection`, and its conclusion was exactly the
original conclusion. Injectivity of an equivalence is not a reduction of the
substantive Ext/localization argument. That split and its incomplete docstring
were rejected. The repaired reduction separates the first two steps of the
original plan (represented Ext transfer) from its final step (localization and
identity-generator coherence). It makes no claim that either substantive
calculation has been formally proved.

The cited Stacks source files are absent on this machine. The four actual tag pages
01F8, 01FB, 03F3, 0A50 were read online. They support the resolution/section/localization
route; these concrete Lean-model identities are agent-written calculations from that
route, not verbatim Stacks statements. Tag 01FB is a remark, not a lemma.

## New nodes
`def-weil-pbc-etale-open-free-sheaf-pullback` records the explicit free-open pullback
construction in `Sheaf.AlgebraicGeometry.EtaleOpenFreeSheafPullback`.

`lem-weil-pbc-etale-resolution-section-transfer-ext-class` records the represented
Ext transfer calculation in `Sheaf.AlgebraicGeometry.EtaleResolutionSectionTransferExtClass`.

`lem-weil-pbc-etale-open-object-cohomology-pullback` records localization/generator
compatibility in `Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyPullback`.

No change records are needed: no existing signature, definition or visibility changed.

## Second reading by W4
1. Compared the complete original and delivered item with `diff`: its existing declaration
   signature is byte-for-byte unchanged, its original docstring and public imports are
   unchanged, and the only edits are two proof-only imports and its proof. All three
   auxiliary modules are new; no other existing module is adapted.
2. Compiled all four delivered modules in import order using `lcompile.py`. No errors
   or non-sorry warnings. Exactly the two reported theorem bodies are `by sorry`;
   no axiom, unsafe, opaque, implemented_by, extern, or data chosen from an unproved
   existence theorem. Checked `#print axioms` in scratch copies (results below).
3. Rejected the equivalent-hypothesis restatement, replaced it with two strictly separate
   calculations, and read each new statement against the definitions. At q=0 the first
   becomes naturality of a morphism from the free sheaf, and the second naturality of
   restriction/pullback on sections. On the empty open the source free sheaf represents
   the zero section group, so both formulas give zero; for zero cocycles/class they also
   give zero by additivity. No positivity or nonempty-open assumption is needed. Checked
   LeanFinder with different queries, Loogle for adjunction/Ext composition formulas,
   and pinned Mathlib plus both local Lean roots by rg; existing generic formulas and
   same-scheme restriction calculations do not assert either cross-scheme identity.
4. The target is reduced from the top downward via an Ext-class intermediate, then the
   open-object map. Both remaining obligations are genuine parts of the old argument.
   The construction introduces no comparison chosen from a holed existence theorem.
   Read `dag/units/sk-thm-p1.json`: none of this item's nodes realizes the unit statement
   or a unit step; its resolution-section/Mayer-Vietoris route is kept. No original
   unit or realized field is changed. Imports needed for existing signatures stay public;
   target proof imports and the generic composition calculation import stay private.
   The pruning list records every old direct proof edge and distinguishes those retained
   transitively from actual module pruning (none).
5. Read all four delivered nodes against Lean: the original node records the two-step
   rewrite/application proof; each new node records its actual construction or remaining
   calculation, source, search results, complete proof plan, provenance, and verbatim
   Lean signature. proof_deps is precisely the union of proof-step uses. New nodes point
   to the original nearest blueprint ancestor. No statement/dependency of the original
   node was changed except its proof_deps, proof and proof_origin.

Second reading changed: removed the restatement split, constructed the canonical
free-open pullback map, split the actual Ext transfer and open-object naturality
calculations, rewrote the item proof and DAG route, and corrected the report's
progress accounting.

Axiom check results: `etaleOpenFreeSheafPullback` uses only propext,
Classical.choice, Quot.sound. Each of the two split theorems and the rewritten
item uses those three plus sorryAx, as expected from the two explicitly reported
open calculations. Scratch-copy compilation passed for each declaration.
LeanSearch was also attempted for the transfer and generator constructions;
it returned Internal Server Error, so no positive result or absence claim is
attributed to that service.
