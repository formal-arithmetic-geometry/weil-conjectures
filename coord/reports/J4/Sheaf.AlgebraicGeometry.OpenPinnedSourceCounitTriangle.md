## What changed

Repaired the returned proof of `AlgebraicGeometry.open_pinned_source_counit_triangle`.
Removed the duplicate private `AlgebraicGeometry.tensorCompositionSymm` and its
now-unused helper `AlgebraicGeometry.conjugateIsoSymm`. Added the proof-only import
`import all Sheaf.AlgebraicGeometry.AffineSpectrumCompositionCounitSquare` and
used its existing `AlgebraicGeometry.SingleComplexBaseChange.tensor_composition_symm`
in `compositionCounit`. The existing theorem is private; importing its private scope
within this same Lake package avoids changing its visibility or adapting its module.

The public statement, public imports and constructed termwise comparison are unchanged.
Six proved private helpers calculate and combine the composition counit, termwise
comparison, exact-open counit and naturality equations. The node's proof and
proof dependencies now record the reused affine-spectrum module. The local
proof-scope change record is `coord/changes/open-pinned-source-counit-proof-scope.md`.

## Proved and sorry left

Closed the one original hole `AlgebraicGeometry.open_pinned_source_counit_triangle`
(node `lem-pc-open-pinned-source-counit-triangle`). No sorry remains in the item;
zero holes added or split off. All six private helpers are proved. Existing upstream
deferred results remain dependencies of the selected derived constructions.

## No longer needed

Removed private helpers `AlgebraicGeometry.tensorCompositionSymm` and
`AlgebraicGeometry.conjugateIsoSymm`. No import or planned dependency node is removed:
both original public imports and all three original proof dependencies are still used.
The added proof import supplies the already-proved tensor composition symmetry lemma;
no new node or module was created. No globally unreachable module is asserted.

## Where the brief, the DAG or earlier work was wrong

The first delivery repeated the statement of the existing private
`AlgebraicGeometry.SingleComplexBaseChange.tensor_composition_symm`.
The landing checker correctly rejected that duplication. This repair imports and
uses the existing theorem directly, rather than repeating its proof or changing binders.
The previous second reading predates this repair and must be repeated by the second reader.

The argument remains valid for empty opens, identity maps and zero complexes:
only isomorphisms are canceled, with no extra geometric hypothesis. The unit route
is preserved. The repaired module compiled locally through `lcompile.py` in 56.2 seconds
without warnings. The duplicate-statement/import-pruning checker also passed.
The delivery dry run enables server compilation and rebases onto current `sheaf-dag`;
its final result is recorded after validation.

## Second reading by J4

1. Compared the delivered module with the repository version. The public theorem and definition
   signatures are byte-for-byte unchanged; the only interface-visible difference is the added
   proof-only import. Verdict: pass.
2. Compiled the module with `lcompile.py` successfully. The item contains no `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, or `extern`; the target's remaining `sorryAx` comes
   only from deferred imported declarations. The axioms probe reports only the permitted base
   axioms plus that imported `sorryAx`. Verdict: pass.
3. Checked the split-off declarations and searched the repository for duplicate helpers. No new
   public split-off theorem was added; the proof reuses the existing private
   `SingleComplexBaseChange.tensor_composition_symm`, and the removed duplicate helpers are gone.
   Verdict: pass.
4. Read the proof from the target downward. The route uses the existing composition and open
   counit interfaces, cancellation and naturality, and retains the unit route; local transparency
   controls are proof-scoped. The proof-only import is needed for the reused private lemma, and no
   unused import or old proof dependency was removed. Verdict: pass.
5. Compared the node with the Lean proof. Its four proof steps, `proof_deps`, and
   `proof_origin` record the composition calculation, reused affine-spectrum lemma, open counit,
   and final cancellation exactly as written. Verdict: pass.

I changed only this review report section; no Lean proof, statement, definition, node, or change
record required repair.
