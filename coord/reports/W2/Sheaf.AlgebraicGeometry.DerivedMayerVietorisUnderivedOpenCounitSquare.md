## What changed

Repaired the delivery returned by reviewer X-8941b (head 8941b83a1).
Removed UnderivedOpenCounitSquareOnQuotient.lean, its new node, and its import.
Added OrdinaryOpenCounitSquare.lean with the ordinary sheaf-module equality
schemeMVOrdinaryOpenCounit_square. Its statement contains no complex or homotopy category.
Its docstring gives the sectionwise preimage/restriction calculation and the
transport through overFunctorEquiv, including the empty and full open cases.

In DerivedMayerVietorisUnderivedOpenCounitSquare.lean, proved the private helper
lift_open_counit_square: rewrite the homotopy counits as quotient images, combine
quotient maps, use extensionality of complex morphisms, compute the component
maps of both comparison isomorphisms and counits, cancel their identity factors,
and apply the ordinary equality in every degree. Specializing this proved helper
to the fixed open models proves the existing theorem with its signature unchanged.
The two explicitly typed adjunctions make its additive instances available.
The existing node is included with updated proof, proof_deps and proof_origin;
all its other fields are preserved.

The sandbox's unchanged DerivedMayerVietorisOpenCounitModel.lean is retained only
because its compiled module is absent from the local baseline; it is byte-identical
to the repository and does not change that module's interface or proof.

## Proved and sorry left

This is a decomposition, not a completed proof of the sectionwise calculation.
Closed 1 original hole: AlgebraicGeometry.schemeMVUnderivedOpenCounit_square,
node lem-pc-mayer-vietoris-underived-open-counit-square.
Added 1 lower hole: AlgebraicGeometry.schemeMVOrdinaryOpenCounit_square,
node lem-pc-mayer-vietoris-ordinary-open-counit-square. This is the sole remaining
sorry in the delivered sources. It concerns an ordinary sheaf of modules on the
inverse-image open. The transition to complexes and the homotopy category is
fully proved in AlgebraicGeometry.lift_open_counit_square (private, no sorry).
Net holes closed minus added: 0. No existing statement or definition was changed.

The old hole AlgebraicGeometry.underived_open_counit_square_on_quotient and node
lem-pc-mayer-vietoris-underived-open-counit-square-on-quotient are removed from the
returned delivery, rather than counted as a mathematical proof.

## No longer needed

Removed the proof import Sheaf.AlgebraicGeometry.UnderivedOpenCounitSquareOnQuotient,
that duplicate module, and its node
lem-pc-mayer-vietoris-underived-open-counit-square-on-quotient.
No original library proof dependencies are pruned. The fixed model and open
adjunction definitions remain necessary. The new ordinary helper is imported
only for the proof; the existing public model import is unchanged.

## Where the brief, the DAG or earlier work was wrong

D1/D2: The returned helper merely substituted K := quotient.obj C into the
original equality. Quotient-object surjectivity alone did not reduce the
mathematical work. The repair removes that duplicate and proves the degreewise
and quotient passage explicitly, leaving only the ordinary-module calculation.

H8: The old docstring explained only how the parent followed. The replacement
helper's docstring describes its own sectionwise calculation: composition maps,
preimage equalities, the two restriction counits, presheaf functoriality and
thinness, and transport along overFunctorEquiv.

C1/review point 6: The existing node is now delivered with its three proof fields
updated to match the repaired Lean argument, including the retained helper node.

F/review point 7: The old claims that the quotient statement was strictly simpler
and that the item was proved outright were inaccurate. The report now explicitly
calls this a decomposition, identifies every remaining hole and node, and reports
one original hole closed and one lower hole added. The earlier second-reading
section has been removed because it described the rejected version.

## New nodes

lem-pc-mayer-vietoris-ordinary-open-counit-square records the ordinary-module
compatibility equation. Its proof is the sectionwise part of the existing parent's
plan, with no complex or homotopy-category equality assumed. The source is the
underived identity in the proof of Stacks Tag 08FE and the open restriction maps
used in Tag 08BV. The source pages were read; the explicit normalization details
are recorded as an agent-written expansion of the existing plan. Searches found
restriction and counit component formulas, but no fixed comparison square;
LeanSearch was unavailable. The change record is
coord/changes/schemeMVUnderivedOpenCounit_square.md.

## Second reading by W2

1. Compared the delivered modules with the repository versions. The existing theorem
   signature is byte-for-byte unchanged; the added ordinary helper is a separate
   declaration and the retained model module is byte-identical.
2. Compiled all three sandbox modules with `lcompile.py`; the build succeeds. The only
   remaining `sorry` is the named ordinary-module theorem, and no forbidden declarations
   or `sorry` occur in definitions. The proved parent uses only the expected quotient,
   categorical, and classical axioms.
3. Checked the split statement and node. The ordinary square is a true strictly lower
   statement: it removes complexes and the homotopy quotient while retaining exactly the
   sectionwise counit compatibility needed degreewise. Its docstring gives the complete
   restriction calculation and its node records the source, proof route, and searches.
4. Checked pruning and the unit route. The ordinary helper is imported privately for the
   proof, the public model import remains necessary, and the unit's realized route is
   preserved. The removed quotient-helper module and node are no longer needed.
5. Checked node/Lean agreement. The parent node's `proof`, `proof_deps`, and
   `proof_origin` match the helper, degreewise quotient descent, and specialization in
   the Lean source; the new node's declaration and statement match its module exactly.

Changed during this second reading: appended this review record only; no proof or
statement changes were needed.
