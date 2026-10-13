## What changed

Added the strict section-element intermediate theorem in
`Sheaf.AlgebraicGeometry.OrdinaryOpenCounitSquareSectionElement` and imported it into
`Sheaf.AlgebraicGeometry.OrdinaryOpenCounitSquareSection`. The component theorem is now
proved by extensionality and the intermediate elementwise theorem. The intermediate
sectionwise calculation remains a named `sorry` for a subsequent worker.

## Proved and sorry left

Proved `AlgebraicGeometry.schemeMVOrdinaryOpenCounit_square_app` by extensionality.
The new declaration `AlgebraicGeometry.schemeMVOrdinaryOpenCounit_square_section_element`
remains `sorry`; it is recorded by node
`lem-pc-mayer-vietoris-ordinary-open-counit-square-section-element`.

## No longer needed

None; the existing model import remains needed for the statement and the new helper.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped before making the planned elementwise calculation a named
strict intermediate statement. The decomposition makes the component assembly complete
in Lean while preserving the stated route.

## New nodes

`lem-pc-mayer-vietoris-ordinary-open-counit-square-section-element` records the
section-element calculation and its source. Its module is
`Sheaf.AlgebraicGeometry.OrdinaryOpenCounitSquareSectionElement`.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader; the open node is
`lem-pc-mayer-vietoris-ordinary-open-counit-square-section-element`.

## Second reading by H4

1. **Interface unchanged.** Compared the delivered section module with the repository version. The
existing declaration `schemeMVOrdinaryOpenCounit_square_app` has the same signature byte for byte;
only its proof and a proof-only import changed. The new helper is a separate, strictly more
specialized elementwise statement.

2. **Compilation and proof audit.** Compiled both sandbox modules with `lcompile.py --all`; both
compile cleanly. The component theorem contains no `sorry`; the helper has the one explicitly
named `sorry` listed above. No forbidden declarations or hollow definitions were added. The
remaining helper hole is documented with its source and proof plan, and its node is present.

3. **Statement and dependency review.** The helper's statement is a true elementwise consequence
of the sectionwise target and is strictly simpler than the target. It does not duplicate the
item's section equality. The existing public model import is needed by the displayed statement;
the helper's model import is proof support. No Mathlib or upstream declaration matching this
specialized equality was found in the recorded searches.

4. **Pruning and route.** The proof uses extensionality followed by the elementwise helper, exactly
the decomposition recorded in the DAG. The unit `sk-thm-picard-semicon` is retained, and no old
proof dependency or import is unused.

5. **DAG agreement.** The section node's proof, proof dependency, and origin now name the helper;
the helper node records its exact Lean declaration, source, split status, and dependency on the
parent square node. The unit route remains represented by the section node.

Changed only the proof import and proof body of the section module, and added the documented
helper module/node already listed above. No further repair was necessary.
