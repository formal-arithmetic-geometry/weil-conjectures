## What changed

Replaced the sorry in AlgebraicGeometry.horizontal_duality_mate_commutativity
with a complete Lean composition proof. The proof imports the new module
Sheaf.AlgebraicGeometry.HorizontalRectangleInverseMateFixedTransport privately.
It uses the already proved single-square identification
AlgebraicGeometry.dualityEquationBaseChangeMap_eq_inverseSquareMate twice,
Mathlib CategoryTheory.mateEquiv_vcomp, the full QCoh inclusion, and cancellation
of the fixed endpoint isomorphisms. Existing signatures and public imports stay
unchanged. No definitions or other existing modules were changed.

The geometric rectangle transport is isolated in a new module. Its theorem has
no middle right adjoint or middle adjunction and asserts no second-mate
factorization. The main proof genuinely supplies that missing composition step.
The item node now records these dependencies. This is a decomposition, not a net
reduction in holes.

## Proved and sorry left

Closed: AlgebraicGeometry.horizontal_duality_mate_commutativity
(lem-sc-horizontal-duality-mate-commutativity), 1 of 1 original holes, by a
compiling proof from the named intermediate theorem.

Added and still sorry: AlgebraicGeometry.horizontal_rectangle_inverse_mate_fixed_transport
(lem-sc-horizontal-rectangle-inverse-mate-fixed-transport), exactly one public
named theorem in its own module. Its proof is exactly `by sorry`; its docstring
and node give the source and complete proof in words. No sorry remains in the
item module. Net holes closed minus added: 0, a decomposition.

Both modules compile with lcompile.py --all. The equality is oriented so that
only the source and target endpoint isomorphisms are cancelled; no duality mate
is inverted. The remaining theorem uses natural transformation identities and
therefore covers identity base morphisms, zero objects, and empty schemes.

## No longer needed

None globally: no original import was removed. The direct parent proof no longer
expands dualityEquationBaseChangeMap or derived base change and no longer uses
pullback-composition coherence directly. Those original dependencies
(def-sc-duality-equation-base-change-map, def-pc-derived-base-change-map,
lem-pc-ringed-spaces-derived-pullback-composition) remain needed by the new fixed
rectangle transport theorem; their modules are not claimed pruned. The existing
existential-target RectangleInverseBaseChangeMateTransport and
RightAdjointMateSuccessiveBaseChange modules are not imported or used.

## Where the brief, the DAG or earlier work was wrong

The initial local compile could not find
HorizontalDualityMateComparisons.olean. The shared compiled library refreshed
and the dependency became available; this was a temporary build-state issue.
The first preflight reported a missing second-reading section together with
an unnecessary global scope-opening command. That command has been removed.
The delivery wrapper permits the missing second reading as the sole failure
of a worker dry run; that section is reserved for the second reader.
No mathematical statement error was found. The existing rectangle transport
lemma supplies an existential target comparison and cannot directly prove an
equality with horizontalMateTargetIso. The new lemma pins that comparison and
removes the middle adjoint; Mathlib proves the subsequent composition step.

The Stacks source was read at https://stacks.math.columbia.edu/tag/0ATR and
https://stacks.math.columbia.edu/tag/0ATM because the local literature source
files are not present on this machine. The cited argument uses Tor independence
only to invert ordinary base change; our hypotheses supply those inverses.

## New nodes

lem-sc-horizontal-rectangle-inverse-mate-fixed-transport, in
 dag/nodes/sec-picard-framework/lem-sc-horizontal-rectangle-inverse-mate-fixed-transport.json,
is the fixed-endpoint rectangle transport before any middle right adjoint is
introduced. Its module is
lean/Sheaf/AlgebraicGeometry/HorizontalRectangleInverseMateFixedTransport.lean.
It retains the parent's chapter and unit, cites existing nodes, and records the
three kinds of search plus unavailable LeanSearch. No change record is needed:
no existing interface changed and no forced adaptation was made.

## Second reading by K3

1. PASS. Compared the complete item module with the repository using diff.
   The only Lean changes are a private proof import and replacement of the
   original theorem's `by sorry` body. Its signature, docstring, visibility,
   definitions and public imports are byte for byte unchanged. No other
   existing Lean module is delivered; there are no interface change records.
2. PASS. Independently compiled both delivered modules in import order with
   lcompile.py. The item contains no sorry. The sole added hole is the public
   named rectangle transport theorem, exactly `by sorry`, with its source,
   natural-language proof and matching node. Scanned both files for forbidden
   declarations and kernel bypasses: none. No new definition or witness choice
   occurs. Scratch-copy axiom checks are recorded below.
3. PASS. Read the fixed endpoint constructions, inverse-square mate theorem,
   ordinary base-change definition, and existing existential rectangle lemma.
   The added theorem removes the middle adjoint and only identifies one outer
   mate under geometric transport; it does not assert composition of the two
   second mates. The main proof establishes that separate composition step
   using mateEquiv_vcomp and the proved single-square identifications. Hence
   this is a strict decomposition, not a renamed copy of the item. Checked the
   orientation: G followed by r.inv equals s.inv followed by M, which yields
   the item after cancellation. Identity g or h uses the same coherent unit
   and composition comparisons; zero inputs or empty schemes give zero
   morphisms and introduce no exception. Arbitrary supplied adjunctions are
   accounted for by right-adjoint uniqueness with counit compatibility.
   Re-read [0ATR](https://stacks.math.columbia.edu/tag/0ATR) and
   [0ATM](https://stacks.math.columbia.edu/tag/0ATM): only ordinary base-change
   invertibility is used, supplied here explicitly. Independent leanfinder,
   loogle and grep searches (recorded on the new node), plus local rg on both
   library roots, found no existing fixed-endpoint transport theorem. The
   existential target lemma cannot pin horizontalMateTargetIso. Closing the
   remaining transport would require the substantial geometric coherence
   proof, rather than a short application of a search result.
4. PASS. The proof uses the shortest available generic mate composition law
   before isolating geometric coherence. All imports are needed: the existing
   comparisons and Arrow occur in signatures, the new QCoh inverse-square
   module occurs in its signature, and the new private import supplies the
   main proof's remaining theorem. No import or module is pruned. Exactly the
   three old direct proof dependencies def-sc-duality-equation-base-change-map,
   def-pc-derived-base-change-map and
   lem-pc-ringed-spaces-derived-pullback-composition moved below the new lemma;
   they are still transitively needed. The old comparison dependency stays.
   Checked dag/units/sk-thm-picard-duality.json: no realized statement or step
   is bypassed or changed; this is below the unit level.
5. PASS. Compared both node records with the Lean declarations. The parent
   steps now describe single-square identification, mateEquiv_vcomp, inclusion,
   and cancellation. Its proof_deps equal their cited union. The new node has
   the complete signature, source, proof steps, dependency union, provenance,
   searches, creation and blueprint records, and the parent's chapter/unit.
   The existing node changes are confined to the allowed stage-3 fields.

Second reading changed only this report and the new node's independent search
record; no Lean repair was necessary. One original hole is closed and one
strictly intermediate hole is added: net zero, explicitly a decomposition.

Axiom probe result: horizontal_duality_mate_commutativity,
horizontal_rectangle_inverse_mate_fixed_transport, and the existing
single-square identification each report exactly propext, Classical.choice,
Quot.sound and sorryAx. The latter is expected from the named remaining hole
and open imported statements; no additional axiom appears. The scratch copy
was removed before delivery.
