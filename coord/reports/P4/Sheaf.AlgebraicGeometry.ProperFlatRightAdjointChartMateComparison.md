## What changed

Repaired and completed the earlier sandbox reduction of
`AlgebraicGeometry.proper_flat_rightAdjoint_chart_mate_comparison` in
`Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison`.
The statement, universes, hypotheses and public imports are unchanged.
The proof constructs the intermediate pullback over W, proves its comparison
map r invertible by the pasted pullback universal property, takes the canonical
right adjoint of its lifted direct image, supplies ordinary base change from
`proper_flat_rightAdjoint_baseChange_hβ`, derives the r/q projection identities,
and composes two arrow isomorphisms.

The two earlier sandbox helper modules are packaged as new statement modules:
`Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen` and
`Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen`. Each has one public theorem,
its source and proof in words, and now a matching new DAG node. Their proof-only
imports retain `ProperFlatRightAdjointRestrictionOpen`, the existing theorem
needed for their open-unit comparisons. The parent has proof-only imports of
these two modules and `ProperFlatRightAdjointBaseChangeHbeta`.

The nodes now describe the actual reduction. No existing interface changes,
forced adaptations, target changes or definition changes are made. Choosing
`FW.rightAdjoint` uses the uniquely determined right adjoint of a given functor,
not arbitrary mathematical data from a mere existence assertion.

## Proved and sorry left

One original hole closed:
`AlgebraicGeometry.proper_flat_rightAdjoint_chart_mate_comparison`
(node `lem-sc-proper-flat-right-adjoint-chart-mate-comparison`).
Its complete Lean proof composes the two strictly one-open comparisons.
There is no sorry left in the item's module.

Two holes added, each the whole proof of its named public theorem:

- `AlgebraicGeometry.rightAdjoint_mate_newBase_open`
  (`lem-sc-right-adjoint-mate-new-base-open`), in `RightAdjointMateNewBaseOpen`.
  It handles only restriction in the new base, leaving the old base unchanged.
- `AlgebraicGeometry.rightAdjoint_mate_oldBase_open`
  (`lem-sc-right-adjoint-mate-old-base-open`), in `RightAdjointMateOldBaseOpen`.
  It handles only restriction in the old base, with a new base already mapping
  to that open, followed by arbitrary derived pullback.

This is a decomposition (1 closed, 2 added; net -1), not a sorry-free proof of
all its dependencies. Neither helper merely renames the full two-open statement.
The new-base helper has no V,b,b'; the old-base helper has no new-base open or
exact restriction and need not assume its r/q maps invertible. Both assert
compatibility, without assuming either mate invertible.

All three modules compile through lcompile.py. The geometric construction,
right-adjoint choice, projection cancellation and composition have real Lean
proofs. Empty opens cause no exception: the comparison lies in the zero derived
category. For the old-base helper, arbitrary Z and noninvertible r/q cause no
exception because derived pullback preserves isomorphisms. Changes of chosen
right adjoints are carried by their canonical uniqueness isomorphisms.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen` from the parent:
the parent now invokes its two one-open helpers. Its node
`lem-sc-proper-flat-right-adjoint-restriction-open` remains needed in the helpers,
and each helper imports it. Thus this removal prunes no transitive module.

The parent no longer directly uses `def-sc-duality-equation-base-change-map`
or `def-pc-derived-base-change-map` as proof steps; they remain necessary to
state the theorem and in both helper arguments. No node or module is globally
unneeded by this reduction. No additional original proof import is removed.
The unit route remains intact; the split is below its realization level.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt contained a noncompiling pullback pasting: the restriction
square has its two legs in the opposite order needed for horizontal pasting.
The repair uses `(isPullback_morphismRestrict ...).flip.paste_horiz` and explicit
`isoPullback_hom_fst/snd` equalities after applying `pullback.hom_ext`.
The earlier attempt also had no report or new-node records for its two helper
sorries; this delivery supplies them.

No false statement or source discrepancy was found. Search found underived
restriction adjunctions and generic mate/uniqueness lemmas, but no existing
scheme-derived one-open arrow comparison. LeanSearch was unavailable with an
Internal Server Error; LeanFinder, Loogle and Mathlib/library rg were used.
The local literature/stacks-project/duality.tex is absent from this clone; the
source was read at the official Stacks pages for 0E9S, 0ATR and 0E4J. No project
source directory or tooling was modified by the worker.

## New nodes

`lem-sc-right-adjoint-mate-new-base-open` at
`dag/nodes/sec-picard-framework/lem-sc-right-adjoint-mate-new-base-open.json`
records the new-base-open part, with its full signature, complete proof plan,
source, three search kinds and inherited chapter/unit/blueprint ancestry.
Its module is `lean/Sheaf/AlgebraicGeometry/RightAdjointMateNewBaseOpen.lean`.

`lem-sc-right-adjoint-mate-old-base-open` at
`dag/nodes/sec-picard-framework/lem-sc-right-adjoint-mate-old-base-open.json`
records the old-base-open part after further derived pullback, with the same
required records. Its module is
`lean/Sheaf/AlgebraicGeometry/RightAdjointMateOldBaseOpen.lean`.
There are no change records because no existing signature or visibility changes.

## Second reading by P4

1. Interface: PASS. Compared the parent with the repository by diff and compared
   the theorem text through `:= by` byte for byte: identical. Only its proof,
   proof-only imports and local heartbeat option differ. Both helpers are absent
   from the repository and introduce no replacement of an existing declaration.
   There are no definitions or interface changes requiring change records.
2. Proof: PASS as a decomposition. All three files compile without warnings
   through lcompile.py (approximately 5, 5 and 14 seconds). A scratch module
   imports the delivered modules and prints axioms for all three declarations:
   only propext, Classical.choice, Quot.sound and sorryAx. The only delivered
   sorries are the two named helper theorems reported above; no forbidden trust
   escape or hollow definition is introduced. FW.rightAdjoint is determined up
   to natural isomorphism by its adjunction, which is the equality used here.
3. Split statements: PASS. Read both entire signatures and docstring arguments
   against Stacks [0E9S](https://stacks.math.columbia.edu/tag/0E9S),
   [0ATR](https://stacks.math.columbia.edu/tag/0ATR), and
   [0E4J](https://stacks.math.columbia.edu/tag/0E4J).
   For the new-base step paste the W restriction square after the global square;
   its mate is invertible by open compatibility. For the old-base step paste
   the V restriction square before the chart square; its mate is likewise
   invertible. The composition law identifies the arrows through endpoint
   isomorphisms, with no assumption that either horizontal mate is invertible.
   Checked identity base maps/full affine opens, empty opens, arbitrary choices
   of right adjoints, and arbitrary noninvertible maps r,q in the old-base step:
   the projection equations force the same map under the pullback isomorphism,
   and further derived pullback preserves the comparison isomorphism. These are
   strictly separate one-open steps, not renamed copies of the two-open parent.
   Independent LeanFinder, Loogle and grep searches using Beck-Chevalley,
   pasting and conjugation terminology found generic mate composition and
   underived restriction results, but no exact library or Mathlib replacement.
   Closing either helper requires the derived comparison/coherence calculation;
   neither has a short direct application proof with the existing API.
4. Route and pruning: PASS. Read the geometric construction of r, its pullback
   pasting proof, the right-adjoint selection, projection cancellation and final
   arrow-isomorphism composition. All three old proof dependencies are accounted
   for in No longer needed: restriction-open moves to the helpers, while the
   two base-change definitions remain statement/argument ingredients. No module
   is transitively pruned. The unit's realized record has empty statement and
   step lists, and this delivery leaves that record and its unit route unchanged.
5. DAG: PASS. Only proof, proof_deps and proof_origin change on the existing
   parent node. Read both new nodes against the signatures, docstrings and
   source: required fields, chapter/unit ancestry, proof steps and dependencies
   match. The right-adjoint existence and ordinary base-change theorem used by
   the parent are now recorded, as are its two comparison helpers.

Second-reading changes: made DerivedOpenRestrictionMaps a proof-only import in
RightAdjointMateOldBaseOpen (its signature uses derivedPullback, supplied by the
canonical mate module, but no exact open-restriction declaration); stored each
new node's Lean signature verbatim instead of flattening its whitespace; added
independent search results and this review. Clarified that the helper modules
are packaged statements with open proofs. No mathematical proof or existing
signature was changed. The delivery closes one original hole and adds two:
net -1, a decomposition, with no transitive pruning.
