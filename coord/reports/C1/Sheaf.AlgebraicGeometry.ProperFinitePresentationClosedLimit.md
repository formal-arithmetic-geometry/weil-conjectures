## What changed

Replaced the target's `sorry` by a construction from a proper finitely presented closed
envelope. For the kernel ideal of its closed immersion, the upstream `fgSubDiagram` is
indexed by a nonempty directed poset; its stages are closed subschemes of the proper envelope
and hence proper. Finite presentation follows by composition. The upstream `isLimitFgSubCone`
and the image isomorphism give the required limit cone with vertex X and compatibility over S.
The envelope itself supplies the final existential clause. The existing signature is unchanged.

Added `Sheaf.AlgebraicGeometry.ProperFinitePresentationClosedLimitEnvelope`, containing the
one remaining open geometric step. Its complete natural-language proof follows Stacks 09ZR.
Removed the first worker's redundant system module and its node. Removed unused private imports
of ChowFiniteType, EventuallyClosedImmersion, NagataFinitePresentationEnvelope and ProjectiveSpace.
The original public imports are unchanged; both imports needed only by the new proof are private.

Import change record: `coord/changes/proper-finite-presentation-closed-limit-imports.md`.

## Proved and sorry left

The original module's sole open declaration,
`AlgebraicGeometry.exists_proper_finitePresentation_closedImmersion_limit`, now has a proof.
One new named theorem remains `sorry`:
`AlgebraicGeometry.exists_proper_finitePresentation_closedImmersion_envelope`, node
`lem-weil-pbc-proper-closed-in-proper-fp-envelope-part`.
The target still depends on this open theorem; it is not an axiom-free completed target.
Local compilation of both modules succeeds. Explicit `#print axioms` on a scratch copy shows
only `propext`, `Classical.choice`, `Quot.sound` and `sorryAx` for both declarations.

## No longer needed

Removed private imports: `Sheaf.AlgebraicGeometry.ChowFiniteType`,
`Sheaf.AlgebraicGeometry.EventuallyClosedImmersion`,
`Sheaf.AlgebraicGeometry.NagataFinitePresentationEnvelope`, and
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace` from the target module.
These ingredients remain in the envelope theorem's documented construction; they are not
claimed as globally pruned. The redundant proposed module
`Sheaf.AlgebraicGeometry.ProperFinitePresentationClosedLimitSystem` and its proposed node
`lem-weil-pbc-proper-closed-in-proper-fp-system-part` were removed from this delivery.

The old direct dependencies no longer used directly by the target proof are:
`def-weil-proper-morphism`, `prop-nagata-finite-type-closed-in-fp`,
`def-nagata-finite-type-closed-in-fp`, `def-weil-pbc-scheme-conventions`,
`lem-weil-pbc-chow-finite-type`, `def-nagata-projective-space-base-change`,
`lemma-nagata-projective-space-base-change-proper`, `lem-weil-pbc-closed-immersion-finite`,
`lem-weil-pbc-limit-affine-transition`, `def-pc-fibre-product`,
`lem-weil-pbc-proper-over-separated`, `lem-weil-pbc-proper-immersion-closed`,
`lem-weil-pbc-eventually-closed-immersion`, `lem-weil-pbc-closed-immersion-comp`,
`lem-weil-pbc-surjective-base-change`, and `lem-weil-pbc-image-universally-closed`.
They remain dependencies of the envelope construction. No old node is globally pruned.

## Where the brief, the DAG or earlier work was wrong

The first delivery simply paired two open conjuncts. Its new nodes depended on the original
node, creating proof cycles; their statements and docstrings were insufficiently self-contained.
The report's assertion that the former imports were removed was also incorrect, and one new
proof import was accidentally public. The present delivery replaces that split with an actual
closed-subscheme construction in the target module, removes the cyclic system node, and gives
the envelope node the original geometric proof dependencies instead of the target node.

## New nodes

`lem-weil-pbc-proper-closed-in-proper-fp-envelope-part` states the proper finitely presented
closed envelope step, in its own module. Its node contains a self-contained statement, the
complete Stacks 09ZR construction in steps, and four newly executed searches (LeanSearch, LeanFinder,
Loogle, and Mathlib grep). LeanSearch returned Internal Server Error; this failure is recorded
without a no-match verdict. The searches found permanence lemmas but no proper-envelope theorem.
Source-library grep found only the separated-envelope result 01ZJ, which does not assert
properness; the finite-type subideal limit theorem 09ZP is reused directly in the target.

## Second reading by C1

1. Compared the target with the repository using diff and an exact signature comparison.
   The existing theorem signature is byte-for-byte unchanged, and no definition changed.
   All existing public imports remain unchanged. Verdict: pass.
2. Compiled both delivered modules through `lcompile.py --all`, with no errors or warnings.
   The sole remaining `sorry` is the named envelope theorem documented above. No axiom,
   unsafe, opaque, extern, implemented_by, hollow definition or other forbidden code occurs.
   Explicit axiom inspection shows only the three standard axioms and the expected sorryAx.
   Verdict: pass as a reduction with one open geometric step, not a completed target.
3. Checked the new envelope statement and searched LeanFinder, Loogle, Mathlib and the source
   library. It is a genuine geometric step: the target proof constructs its entire diagram
   and limiting cone from this envelope using 09ZP, rather than merely renaming the target.
   Empty X causes no obstruction: the ideal diagram still contains zero. When f is already
   finitely presented, Y = X and i = identity supply the envelope. No extra hypotheses occur.
   The envelope docstring gives all eight construction steps and its node matches it.
   Verdict: pass; the envelope existence proof remains open.
4. Checked the unit `sk-thm-p1` realized fields: this node is not itself a unit statement or
   designated step, and those fields are unchanged. The envelope retains the Stacks 09ZR
   route, including Chow and eventual closed immersion. The target uses the shorter 09ZP
   construction inside that proper envelope; there is no change to the unit's route.
   Removed unused private imports and listed every former direct dependency above.
   Verdict: pass.
5. Checked the target node's proof and proof_deps against the actual construction, and the
   new node against its Lean signature, source, full natural-language proof, and actual searches.
   There is no remaining dependency from the envelope node back to the target node.
   Verdict: pass.

Second reading changed the proof into the finite-type-subideal construction, removed the
redundant system split, repaired the cyclic DAG dependencies, expanded the envelope proof
and statement, repeated searches (including unavailable LeanSearch), fixed proof imports, and corrected this report.
