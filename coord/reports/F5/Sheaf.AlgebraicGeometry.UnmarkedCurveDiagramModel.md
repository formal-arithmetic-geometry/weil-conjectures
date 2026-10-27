## What changed

`Sheaf.AlgebraicGeometry.UnmarkedCurveDiagramModel` now proves
`AlgebraicGeometry.exists_unmarked_curve_diagram_model` with its original signature.
All original public imports are retained. New imports are private proof imports.
No source-library module, public definition, target, or consumer interface changes.

The proof constructs a reduced finite surjective radicial neighbourhood, identifying
its prescribed generic stalk with K. A proved affine-neighbourhood construction
retains compatibility of all transition maps with the ambient scheme. It transports
a descended diagram to an actual open, shrinks downstairs using finite closed
images, and restricts the complete diagram by pullback. The coproduct comparison
and every supplied arrow are preserved. A separate proved fibre argument uses the
residue-field isomorphism of a field-valued point surjective on stalks to identify
the curve fibre, establishing geometric connectedness and the dimension bound.
These constructions also handle the empty indexed family.

The remaining simultaneous finite-presentation descent step is isolated in
`Sheaf.AlgebraicGeometry.FinitePresentationChainDescent`. This is a general limit
lemma for finite chains and a specified model. It has no generic-point, field,
radicial-cover, neighbourhood, or curve-fibre assertion. Its source and complete
proof plan are included in the docstring and new node. The combining proof in the
item performs those additional steps in Lean; the new lemma is not the item with
repackaged hypotheses. Both DAG proof records follow this route.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_unmarked_curve_diagram_model`
(node `lem-weil-pbc-unmarked-curve-diagram-model`). Its file has zero holes.

Added one hole:
`AlgebraicGeometry.exists_finitePresentation_chain_stage`
(node `lem-weil-pbc-finite-presentation-chain-descent`). Its entire proof is
`by sorry` in its own new module. This is a decomposition: one original hole
closed and one strictly smaller argument step left, net zero holes closed by
this packet. Existing imported holes are unchanged. All private helpers are proved.

## No longer needed

No original Lean import was removed, and no module is withdrawn. In particular,
this packet makes no claim that a source-library declaration may be removed.

The item no longer directly needs these original planned dependencies:

- `lem-weil-pbc-purely-inseparable-generic-cover`: construct the cover using
  `lem-weil-pbc-finite-radicial-neighbourhood-model` on the reduction instead.
- `lem-weil-pbc-finite-presentation-over-finite-type-algebra`: finite separable
  field extensions and Noetherian smooth proper curves provide the necessary
  finite-presentation instances directly.
- `lem-weil-pbc-finite-closed-map-finite-fibres` and
  `lem-weil-pbc-finite-composition`: use the packaged finite-image neighbourhood
  shrinking theorem and the existing composition/base-change instances.
- `def-weil-proper-morphism` and `def-sbc-smooth-morphisms`: the properties are
  already present in the unchanged public imports; no separate proof use remains.

The object, arrow and equality descent nodes, and the finite, surjective, etale,
open-immersion, smooth and proper descent nodes, move to the new chain-descent
node's proof dependencies. They remain needed; this is not global pruning.
The affine-neighbourhood stalk-limit node also remains in the route: the private
construction supplies transition compatibility omitted from its current interface.
No unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan leaves two necessary interfaces implicit. Descent to a
neighbourhood needs transition maps compatible with inclusions into the ambient
scheme, not just an abstract limit and unrelated stage isomorphisms. The proved
private affine-neighbourhood helper records this compatibility explicitly.
Furthermore the generic fibre comparison needs the actual residue-field
isomorphism, not only a singleton underlying space. The proved field-point lemmas
supply it from surjectivity on stalks. No original statement is weakened or marked
disputed.

## New nodes

`lem-weil-pbc-finite-presentation-chain-descent` realizes
`AlgebraicGeometry.exists_finitePresentation_chain_stage` in the new module
`Sheaf.AlgebraicGeometry.FinitePresentationChainDescent`. It is precisely the
finite-diagram and morphism-property descent portion of original proof steps 2
and 3. Its dependencies are the existing finite-family, arrow, equality and
property descent nodes. It includes three recorded kinds of Mathlib search,
a self-contained statement, source, proof, and verbatim Lean attachment.
No change record is necessary: no existing statement or definition changes.
The parent `Sheaf.AlgebraicGeometry.MarkedCurveDiagramModel` still receives its
unchanged cartesian coproduct comparison and generic fibre assertions; it uses
that comparison to apply `exists_finite_closedImmersion_locus`.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
