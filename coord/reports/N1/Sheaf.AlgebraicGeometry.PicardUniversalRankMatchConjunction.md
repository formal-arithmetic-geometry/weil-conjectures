## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.picardUniversalRankMatch_of_singleRankMatch`
with the intersection argument. All signatures and public imports remain identical.
Added proof-only imports of `Sheaf.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank`,
`WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank`.
Six proved private helpers compare tensor pullback with abstract pullback, transport
fixed rank to smaller opens and their fibre products, and detect nonemptiness from the
unit isomorphism. The DAG proof now records nonemptiness of X_W directly, avoiding a
residue-field fibre construction. Its dependencies also record tensor-pullback composition.

## Proved and sorry left

The sole original hole is in
`AlgebraicGeometry.Scheme.picardUniversalRankMatch_of_singleRankMatch`
(node `lem-sc-picard-universal-rank-match-conjunction`). Closed this hole with a complete proof from existing declarations.
The whole module compiles against the published library. No `sorry` remains in the
delivered Lean source, and no holes or nodes were added: one hole closed, zero added.
The delivery dry run passes compilation and preflight; the independent second reading
is recorded below.

## No longer needed

None. All original imports and proof-dependency nodes remain used. The residue-field
base-change construction in the old proof plan is unnecessary: the nonempty intersection
and its unit isomorphism already force X_W to have a point.

## Where the brief, the DAG or earlier work was wrong

The original plan is valid but unnecessarily constructs a residue-field fibre merely to
find a point of X_W. Use the unit at W instead. Empty schemes and rank zero cause no
exceptions. The finite-local-freeness assumption on E is retained unchanged.

Searches ran through msearch.py: LeanFinder for fixed-rank pullback and pointwise rank
uniqueness returned abstract pullback/free isomorphisms; Loogle did not recognize the
source-library fixed-rank class; grep for tensor/abstract pullback and unit-surjectivity
found no direct conjunction theorem. Local searches found the proved fixed-rank pullback
instance, zero modules on empty schemes, nonzero structure modules on nonempty schemes,
and the stalk-finrank theorem. Stacks Tag 0BDP was read online, including the rank
decomposition and intersection of the two direct-image loci. The local literature files
named by older project records are absent on this machine.

The previous attempt was blocked by a missing compiled PicardUniversalSingleRankMatch
dependency. The refreshed published snapshot now includes it; full-module compilation
and `deliver3.py --no-push` both pass. No dependency was restated or adapted.


## Second reading by N1

1. PASS. Compared the sole delivered module and node against the read-only repository
   with diff. The existing theorem signature, visibility, definitions used by its
   signature, and three public imports are byte for byte unchanged. No interface
   change or change record is needed. Only private helpers and the proof were added.
2. PASS. Independently compiled the module with lcompile.py. Compiled a scratch copy
   printing axioms of tensorIso, tensorRank, tensorRankComp, rankOnSmallerOpen,
   referenceRankOnSmallerOpen, nonempty_of_unit_iso, and
   picardUniversalRankMatch_of_singleRankMatch. Every declaration uses only propext,
   Classical.choice, and Quot.sound; no sorryAx. Scanned the delivered source for
   sorry and prohibited declarations: none. The comparison isomorphism is constructed
   by uniqueness of left adjoints from proved adjunctions; no arbitrary object is
   selected from an unproved existence statement.
3. PASS. No split-off statements, new holes, or new nodes. Read all six private
   helpers: fixed-rank pullback transports along isomorphisms; the canonical map
   between fibre products has the required projection; a unit isomorphism over a
   nonempty scheme rules out an empty source. Both reference conditions concern E,
   including the dual-direct-image assumption. Empty test schemes are vacuous;
   W contains t; rank zero is covered by stalk finrank over a nontrivial local ring.
4. PASS after import cleanup. Searched the local library for fixed-rank uniqueness,
   pullback rank preservation, tensor/abstract comparison, and unit nonemptiness.
   The proof uses the existing fixed-rank pullback instance and stalk-finrank theorem;
   no shorter existing conjunction theorem was found. Removed the newly added
   explicit Invertible import, already exported through RankMatch -> Dual. The
   remaining proof-only imports supply the rank instance and stalk theorem. All old
   proof_deps remain used, so no old node or module is pruned. Read
   dag/units/sk-prop-av-cube.json and Stacks Tag 0BDP: this is a local synchronization
   step below the unit, and preserves the intersection-of-two-rank-loci route.
   The unit's existing empty realized entries were not changed or bypassed.
5. PASS. Read the changed node and its dependencies' Lean records. The three steps
   match the restriction, nonemptiness/rank comparison, and common-witness code.
   proof_deps is exactly the union of uses, including the newly recorded tensor
   composition node. proof_origin describes the actual simplification from a
   residue-field fibre to X_W. No new node fields are required.

Changed in this reading: removed one redundant proof-only import and updated this
report. The proof itself needed no repair. Confirmed one original hole closed
(picardUniversalRankMatch_of_singleRankMatch), zero holes added, zero split off.
