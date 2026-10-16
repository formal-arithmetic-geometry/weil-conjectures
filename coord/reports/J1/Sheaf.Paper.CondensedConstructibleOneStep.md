## What changed

Proved `AlgebraicGeometry.ProEtale.condensed_constructible_one_step` using the published
`condensed_constructible_generic_lfp` and open/closed recollement. In the globally locally
finitely presented case, use identity immersions and the identity pullback comparison.
Otherwise use the supplied nonempty open, map the bounded-below recollement triangle to
the ordinary derived category, and transport its three objects with exact-functor/single
comparisons. The original statement, public imports, and blueprint unit route stay unchanged.

Repair X-5280a, H4/H10: replaced all six occurrences of
`condensedConstructiblePieceOver` with the already-landed `condensedLocallyClosedPiece`.
Restored `CondensedConstructiblePiece.lean` exactly to its published f712b09e59 version,
including `public import Sheaf.Paper.CondensedLocallyClosedPiece` and the body
`condensedLocallyClosedPiece (Profinite.continuousMapRingObj E.val) T`. Verified it against
the current repository and omitted that unchanged file from the delivery. Removed the
duplicate `CondensedConstructiblePieceOver.lean`, its definition node, and the obsolete
`condensed-constructible-piece-ring-parameters.md` change record. Updated both references
in the item's node to `def-weil-pbc-condensed-locally-closed-piece`. These duplicate files
never landed on the current base, so no `deleted.txt` is required.

The base now contains B3's `ProEtaleModuleLfpImmersionTransport` and
`CondensedConstructibleGenericLfp`. The final proof reuses the latter, which already uses
the former, rather than duplicating their finite-stratification and presentation transport
arguments. No lower module is changed. No change record remains in this delivery.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.ProEtale.condensed_constructible_one_step`.

No direct `sorry` remains in the delivered Lean module. No new theorem with `sorry` is
added, so this is not a decomposition. Imported project obligations remain separate
obligations, including the landed
`AlgebraicGeometry.ProEtale.localFinitePresentation_of_surjective_closed_pullback`,
which the existing immersion-transport theorem uses. No claim is made that those imported
obligations are proved by this delivery.

## No longer needed

Removed the base's direct proof imports
`Sheaf.AlgebraicGeometry.LocallyClosedStratification` and
`WeilConjectures.ConstructibleSheaf.GenericConstancy`. The two old direct proof dependencies
`def-constructible-stratification` and `prop-constructible-generic-constancy` are no longer
used directly: the published generic-LFP theorem carries that argument and its dependencies.

The second reader also removed direct imports `WeilConjectures.Topology.StratificationDense`
and `Sheaf.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport` from the proposed proof,
replacing them with `Sheaf.Paper.CondensedConstructibleGenericLfp`. Their nodes are now
indirect dependencies through that theorem. Removed the redundant newly proposed
`Mathlib.AlgebraicGeometry.Noetherian` import after a successful removal compile. Every
remaining private import was tested individually; removing it causes an unknown declaration.
No published module is made unreachable by these changes: this is direct import pruning,
not a claim of whole-library module pruning.

Pruned duplicate proposed module `Sheaf.Paper.CondensedConstructiblePieceOver` and node
`def-weil-pbc-condensed-constructible-piece-over`; reuse the published
`Sheaf.Paper.CondensedLocallyClosedPiece` and its node. Omitted unchanged
`Sheaf.Paper.CondensedConstructiblePiece` and removed its obsolete change record.

Pruned proposed `Sheaf.AlgebraicGeometry.ProEtaleModuleLfpImmersion` and node
`lem-weil-pbc-proetale-module-lfp-immersion`; reuse landed
`Sheaf.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport` and node
`lem-weil-pbc-proetale-module-lfp-immersion-transport`. Omitted the proposed edits of
`ProEtaleModuleConstructiblePullback` and `ProEtaleModuleLfpClosedReflection`, the proposed
`ProEtaleNilCoverRefinement` module and node, and `proetale-module-presentation-api.md`.
The item's proof uses the published transport interface and needs none of these edits.
No existing library module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery duplicated the published generic locally closed piece predicate and
removed the export required by `CondensedLocalPieceHomContinuity`. Reusing the published
predicate repairs that break without editing the importer.

The current base contains B3's reflection and immersion-transport interfaces. J1's older
versions would replace an existing reflection declaration and duplicate the immersion
lemma. This repair reuses the canonical transport theorem. E2 currently holds
`ProEtaleModuleLfpClosedReflection`; the dry run confirmed that its original compiles
unchanged against this repair, so changing it is not a forced adaptation. The completed
reflection proof, reconciled with its exact published signature, and the completed
cover-refinement proof are retained under `scratchpad/completed-reflection/` for later
reuse; they are outside the delivery. This repair adds no lower proof obligation.

Restriction to a stratum interior still needs the immersed-image transport theorem:
range containment does not identify schemes with different nilpotent structures.
The existing theorem gives precisely the needed local finite presentation without
adding reducedness or a nilpotence bound.

Validation: the repaired item and the unchanged
`Sheaf.Paper.CondensedLocalPieceHomContinuity` compile. Signature comparison reports no
statement or public-import changes in the item and closes its one direct hole. The final
checks compile against the published lower modules, with obsolete sandbox outputs removed.

## Second reading by J1

1. PASS: compared the entire delivered module with the current repository. The only
   pre-existing declaration, `AlgebraicGeometry.ProEtale.condensed_constructible_one_step`,
   has a byte-for-byte identical signature. Both public imports and its docstring are
   unchanged. There are no delivered definitions, lower-module edits, interface changes,
   or change records; all added helpers are private proved propositions.
2. PASS: compiled the original proposed proof and the repaired proof locally through
   `lcompile.py`. There is no direct `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`,
   `extern`, or hidden data choice in the delivered module. A scratch-copy `#print axioms`
   for the item and the reused generic-LFP theorem reports exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`; the last is from existing imported
   obligations, not a new hole. The delivery's probe also checks the private helpers.
3. PASS: no split-off statement, new node, or new hole is delivered. Read the exact types
   of the existing presentation transport, generic-LFP, constructible pullback, identity
   comparison, and recollement APIs. Checked empty T (the global-LFP alternative), zero M,
   a one-stratum decomposition, and different nilpotent structures: no nonempty point is
   assumed in the identity branch, no reducedness or scheme factorization is used, and
   non-surjectivity of the closed complement follows from the supplied point of U.
4. PASS WITH SIMPLIFICATION: searched `lean/Sheaf`, `lean/WeilConjectures`, and Mathlib's
   triangulated API by alternate descriptions (`exists_nonempty`, generic LFP, stratum
   interior density, and distinguished-triangle transport). Found the already published
   `condensed_constructible_generic_lfp`, which replaces duplicate local empty-cover,
   density, and coefficient-transport proofs. Its dependency closure was already imported;
   reuse adds no lower module except that proved theorem's module. The exact-functor import
   is public because `mapDerivedCategory` occurs in the existing public signature; all
   proof-only imports remain private. Checked the unit record and its `realized` fields:
   open/closed induction is retained and no unit statement or step is bypassed.
5. PASS AFTER UPDATE: checked the item's node, its dependencies' Lean attachments, and
   `dag/units/sk-thm-properbasechange.json`. Updated only `proof`, `proof_deps`, and
   `proof_origin` to record generic-LFP reuse and identity/recollement transport. The
   dependency list is exactly the union of step uses; removed direct old dependencies
   are named above. Statement, statement dependencies, unit, chapter, and Lean attachment
   are unchanged. No new node fields need checking because no new node is delivered.

Changes by the second reader: reuse the existing generic-LFP theorem; remove the two
now-duplicate private lemmas and their direct imports; pass the open and its witnesses to
the closed-complement step; remove the redundant Noetherian import; update the proof route
and report. Closed one original hole, added zero holes; the result is a reduction to
existing obligations, not a claim that imported obligations or final targets are closed.
