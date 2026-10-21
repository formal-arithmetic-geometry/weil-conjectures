## What changed

Completed `AlgebraicGeometry.Scheme.pbcDistinguishedDiagramLifting` without changing
its signature, any public definition, or the public import of
`Sheaf.Paper.PbcCommonStageCones`.

Private helpers prove representation and transport for all seven expression
constructors; eventual invertibility of a represented isomorphism; simultaneous
lifting of three-component triangle isomorphisms; eventual distinguishedness of
a stage triangle; finite simultaneous refinement for selected rows; and the
canonical recovery equations and triangle isomorphisms. The three components
and commuting squares are indexed by `Option Bool`, with every branch constructed
explicitly.

The proof first chooses a stage containing the vertices, arrow representatives
and the specified base field. It refines for the finite equations, then for the
finite distinguished witnesses. The expression-transport identity preserves the
equations through the second refinement. All finite-family upper bounds use an
Option index, so empty families retain the required starting stage. No pair-category
Verdier axiom is used. The proof imports `Sheaf.Paper.PbcVerdierAxioms` for its
already proved finite-stage exactness. The complete finite-refinement argument is
a private theorem for general stage systems; the public theorem specializes it
to the actual coefficient system.

Validation: the complete module compiles through `lcompile.py` in 21.4 seconds,
with no errors or warnings. Text comparisons confirm all existing expression,
row and geometric definitions and the public theorem signature are unchanged.
There are zero `sorry` tokens and no added axioms or split-off modules.

The node proof and dependencies now describe this argument. Change record:
`coord/changes/A8-distinguished-diagram-lifting-proof.md`.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.pbcDistinguishedDiagramLifting`
(node `lem-weil-pbc-distinguished-diagram-lifting`), the item's sole original hole.
Added holes: none. Remaining holes in delivered modules: none. No split-off
statements or new axioms.

## No longer needed

Removed redundant proof imports `Sheaf.Paper.PbcScalarExtension`,
`Sheaf.CategoryTheory.ScalarLocalizationTriangulated`,
`Mathlib.CategoryTheory.Triangulated.Triangulated`,
`Sheaf.Paper.CommonStageCalculus`, and `Sheaf.Paper.FiniteStagePairCategory`.
The necessary interfaces are already available through the unchanged public
cone import and the finite-stage exactness proof import. Their modules are not
withdrawn: the first, fourth and fifth still supply transitively used interfaces,
and scalar-localization triangulation remains a statement dependency specifying
the finite-stage structure. No node or module is withdrawn or newly declared
unnecessary throughout the library. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The given proof plan is valid. Its explicit enlargement by every witness arrow
and inverse is implemented as the equivalent reusable finite-refinement argument:
represent the three components of each witness triangle isomorphism, refine for
invertibility and the three squares, then transfer distinguishedness. Existing
`qbarScalarExtensionExact` supplies exactness for the actual normalized rational
stages; no new interface or statement repair is necessary.

The library search found no theorem for this complete lifting statement. Searches
with LeanFinder, Loogle and grep are recorded in `searches.jsonl`; local source
inspection reused `PairCategory.exists_mkHom_eq`, `mkHom_eq_mkHom_iff`,
`mkHom_tr`, the normalized preadditive formulas, `Morphism.tr_mapAt`,
`pbcStageShift_coherence`, and Mathlib's triangle/functor isomorphisms.

`import_direction.py may` accepts the exactness import. `downstream.py --direct`
reports zero direct consumers; all public signatures and data remain unchanged,
so no forced consumer adaptations are needed.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
