## What changed

Replaced the target's proof hole by a reduction to two strictly smaller obligations:
construction of the tuplewise total map with the alpha square, and beta compatibility
for a map with that specified action. The original target signature is byte-for-byte
unchanged. Added `EtaleAdditiveCechPullbackTotalMap` and
`EtaleAdditiveCechPullbackTotalBeta`. Only the latter needs a direct proof-only import
in the target module; it publicly imports the map module because its signature uses
`IsAdditiveCechPullbackTotalMap`.

The map module constructs `additiveCechTuplePullback` and
`additiveCechPullbackBidegree` from actual open inclusions and section transfers.
`IsAdditiveCechPullbackTotalMap` specifies every total summand. No data is chosen from
an unproved existence theorem or hidden behind a proof hole.

## Proved and sorry left

Closed the original named hole
`AlgebraicGeometry.Scheme.Modules.exists_additiveCech_pullback_total_transfer`
(node `lem-pbc-etale-additive-cech-pullback-total-transfer`).

Added exactly two named holes:

- `AlgebraicGeometry.Scheme.Modules.exists_additiveCech_pullback_total_map`,
  node `lem-pbc-etale-additive-cech-pullback-total-map`.
- `AlgebraicGeometry.Scheme.Modules.additiveCech_pullback_total_beta`,
  node `lem-pbc-etale-additive-cech-pullback-total-beta`.

This is a decomposition, not a complete proof: one hole closed and two added,
net minus one in holes closed minus holes added. The remaining statements have
source references and full natural-language proofs in their docstrings. The map
existence statement does not assume hα or conclude beta compatibility; the beta
statement does not construct a map and requires its explicit summand action.

## No longer needed

No original imports or modules are pruned. The original direct proof dependencies
`def-pbc-etale-additive-cech-normalization`,
`def-weil-pbc-etale-resolution-section-transfer`, and
`def-sc-etale-additive-structure-restriction` are replaced in the target node by the
two intermediate nodes; they remain needed transitively by the construction and
beta proof. The first worker's redundant direct proof-only import of the map module
was removed: the beta module already publicly imports it.

## Where the brief, the DAG or earlier work was wrong

The first worker's beta statement was false: it quantified over an arbitrary total
map t without any assumption connecting t to α. For the identity pullback with a
singleton full-open family in degree zero and a nonzero structure ring, beta(1) is
nonzero (the resolution augmentation is monic and the (0,0) total inclusion is an
isomorphism); t = 0 would force it to vanish. The report's claim that this was a
valid reduction was therefore incorrect. The repaired beta statement requires the
explicit summand action. The map existence statement supplies that action; its
previous alpha-only conclusion did not suffice.

The cited construction was checked against [Stacks Tag 01FD](https://stacks.math.columbia.edu/tag/01FD),
Lemma 20.15.1, in particular its tuple restriction rule, double-complex map and
augmented commuting diagram. [Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
provides the context of additive quasi-coherent coefficients; no cohomology
comparison or acyclicity is used here.

## New nodes

`lem-pbc-etale-additive-cech-pullback-total-map` records the explicit tuple and
bidegree constructions and the remaining unaugmented total-map/alpha obligation.
`lem-pbc-etale-additive-cech-pullback-total-beta` records beta compatibility only for
maps satisfying the explicit summand specification. Both files are under
`dag/nodes/sec-proper-base-change/`. Their Lean statements are copied verbatim from
the corrected modules. No existing interface changes or change records are needed.

## Second reading by S4

1. Compared the delivered target module against the repository with `diff -u` and
   checked its signature byte-for-byte. Verdict: unchanged statement, definitions,
   visibility and original public import; only a proof and a proof-only import
   change. The two other modules and their declarations are new.
2. Compiled all three files through lcompile.py in import order. Inspected every
   definition: each has explicit data, and the only sorries are the two named
   intermediate theorems above. No forbidden declarations or attributes occur.
   The three explicit constructions/predicates use only propext, Classical.choice
   and Quot.sound; both open lemmas and the reduced target additionally use
   sorryAx, as expected. Checked all six with #print axioms in a scratch module.
3. Rejected the arbitrary-map beta lemma using the degree-zero example above.
   The corrected statements follow the tuple construction and augmentation
   naturality in the cited source. Checked empty index families (zero products),
   empty opens, degree zero, the identity/singleton case, and zero α for the
   unaugmented construction. New searches with leanfinder, loogle and grep used
   different wording; LeanSearch was also attempted and returned an internal
   server error (recorded as unavailable). Results are recorded in searches.jsonl
   and both new nodes.
   Also searched lean/Sheaf and lean/WeilConjectures: existing resolution transfer
   treats a fixed scheme, and scalar transfer treats endomorphisms; neither supplies
   this cross-scheme/open-family construction. No exact existing result was found.
4. The target reduces first to construction/alpha and then to beta for that same
   map; the explicit action is passed between the two steps. These are strictly
   separate parts of the original argument, with no restatement lemma. Imports
   are minimal after removing the redundant map import. No original import is
   pruned. Read dag/units/sk-thm-p1.json and its realized route: this decomposition
   is below that unit's steps and retains the curve/additive comparison route.
5. Corrected proof, proof_deps and proof_origin of the target node to reflect the
   actual two-step reduction. Corrected both new nodes' statements, Lean signatures,
   proof plans and dependency unions to match the repaired code. Their created,
   source, search, blueprint, chapter, unit and lean records are present.

Changed during this reading: repaired the false beta lemma, supplied the missing
explicit map specification via genuine tuple/bidegree constructions, strengthened
the map construction conclusion accordingly, passed that specification in the
target proof, expanded both hole docstrings, removed a redundant proof import, and
corrected DAG metadata, searches and the accounting in this report.
