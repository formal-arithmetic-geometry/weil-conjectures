## What changed

The target theorem is now proved by combining two strictly smaller public lemmas: the
identity law and the composition law for `structureSheafCohomologyPullback`.  These
lemmas are stated in `StructureSheafCohomologyPullbackIdentity.lean` and
`StructureSheafCohomologyPullbackComposition.lean`, and are imported privately by the
target module.  The two lemmas retain the source argument as named `sorry`s for follow-up
workers; the target proof is a decomposition, not a sorry-free proof. The unused
private import `Sheaf.CategoryTheory.SiteCohomologyPullback` was removed in the second
reading. The component docstrings now give the explicit adjunction and Ext argument.

## Proved and sorry left

Closed the one original hole
`AlgebraicGeometry.Scheme.structureSheafCohomologyPullback_functorial` by `constructor`
and the two component lemmas. Added two holes (listed below). This is a decomposition:
1 original hole closed, 2 new holes added, source-level net -1 before accounting for
import-closure pruning. No claim of a sorry-free proof or positive ledger progress is made.
The following declarations remain sorry:

- `AlgebraicGeometry.Scheme.structureSheafCohomologyPullback_identity`
  (`lem-sc-structure-sheaf-cohomology-pullback-identity`).
- `AlgebraicGeometry.Scheme.structureSheafCohomologyPullback_comp`
  (`lem-sc-structure-sheaf-cohomology-pullback-composition`).

## No longer needed

Removed the private import `Sheaf.CategoryTheory.SiteCohomologyPullback`. The old
proof dependency `lem-weil-pbc-site-cohomology-pullback` is no longer used by the
combining proof. The other old dependency,
`def-sc-structure-sheaf-cohomology-pullback`, remains needed by both component laws
and by the statement. Its module stays publicly imported. No claim is made that the
removed module is globally unreachable: other targets may still import it.

## Where the brief, the DAG or earlier work was wrong

The original node's proof plan required the full resolution and Ext comparison argument,
which is not available as a directly applicable proved declaration. The imported
`siteCohomology_pullback` is a theorem about characterised families over site objects;
it requires a comparison with the particular constant-sheaf Ext construction here.  The target was therefore split
into its two independent conjuncts, each a strictly smaller statement with the same
source proof route.

## New nodes

Created `lem-sc-structure-sheaf-cohomology-pullback-identity` and
`lem-sc-structure-sheaf-cohomology-pullback-composition`; their node files are under
`dag/nodes/sec-abelian-varieties/` and their Lean modules are included in this delivery.

## Earlier second reading (a previous round; superseded)

A second worker should check the two decomposition statements and their DAG records.

## Second reading by M3

1. Compared the delivered original module with the repository using `diff -u`.
   Its declaration signature and docstring are byte for byte unchanged. Only private
   proof imports and its proof body change; no definition or existing statement changes,
   and no change record is needed. The other two modules and nodes are new.
2. All three modules compile through `lcompile.py --all`. There are exactly two
   remaining `sorry`s, the entire proofs of the named component laws listed above;
   none occur in data or definitions. No forbidden declarations or attributes appear.
   Scratch `#print axioms` checks of all three declarations show only `propext`,
   `Classical.choice`, `Quot.sound` and `sorryAx` (the two named open component laws). The delivery tool also runs its axiom probe.
3. The new laws are the two separate conjuncts, each strictly smaller than the original
   conjunction, with exactly its schemes, degrees and morphisms. They are true for
   arbitrary schemes: n = 0 gives the usual section maps; either morphism being an
   identity gives the same composition law; the empty scheme gives zero groups.
   Inspected the actual inverse-image/constant-sheaf/adjoint definition. Expanded the
   docstrings to show the adjunction comparison identities and their cancellation on
   Ext classes, so the missing comparison is explicit. Checked Stacks 01F7 and 01FB
   and searched independently through leanfinder, loogle and grep, plus local rg on
   both library roots. Found exact-functor Ext primitives and coefficient naturality,
   but no separately proved scheme identity or composition law. The existing combined
   theorem is the item itself, not an available proof of these new laws. A bounded
   attempt to close the identity law by unfolding and simplification leaves the
   inverse-image and constant-sheaf comparison goal; it was kept only in scratchpad.
4. The combining proof uses exactly the two smaller laws. Removed its unused private
   site-cohomology import and listed the discarded old dependency above. Read
   `dag/units/sk-prop-av-cube.json`, including `realized`: this is a below-unit
   functoriality sublemma, not a replacement for the cube statement or its general-cube
   step. No unit realization or unit route changes. Reported the result as decomposition.
5. The original node's two proof steps and proof_deps match the two applications in Lean.
   Both new nodes have source, proof, proof_deps, proof_origin, searches, created,
   blueprint, chapter, unit and Lean records. Their statements agree with the Lean;
   the proof plans now give the explicit comparison and Ext calculations of the
   docstrings. Their source routes do not cite the discarded site-family theorem.

Second reading changed: removed one unused private import, completed both new proof
plans/docstrings, added independent search records, and corrected pruning and hole
accounting in the report. Existing signatures and the combining proof were retained.
