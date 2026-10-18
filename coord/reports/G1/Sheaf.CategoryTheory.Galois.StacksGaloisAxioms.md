## What changed

Completed `CategoryTheory.stacksGaloisCategory_axioms` in
`Sheaf.CategoryTheory.Galois.StacksGaloisAxioms`, preserving its signature and all visibility.
The first six clauses are proved from the Stacks axioms and Mathlib's general category and
finite-cardinality APIs. The seventh uses the existing
`CategoryTheory.morphism_coproduct_connected_components` declaration.

Faithfulness uses the preserved equalizer and reflection of isomorphisms. Mono/epi detection
uses preservation of pullbacks/pushouts and reflection through the newly proved faithfulness.
Initial and terminal detection uses preservation and reflection of the empty diagrams.
Evaluation uniqueness uses the fibre of the equalizer and connectedness. It also gives the
shorter proof of epimorphisms between connected objects: evaluate a cancellation equation at
an image point of the source fibre. Injectivity of automorphism evaluation then gives the
cardinal bound and the equivalence between equal cardinalities and surjectivity.

The module compiles through `lcompile.py` without errors or warnings. The DAG proof and its
proof-dependency list now record the shorter cancellation argument.

## Proved and sorry left

Closed 1 of 1 original holes: `CategoryTheory.stacksGaloisCategory_axioms`
(node `lem-galois-axioms`). The assigned module has zero remaining holes. Added zero holes,
and split off zero statements.

The imported existing theorem `CategoryTheory.morphism_coproduct_connected_components`
(node `lem-galois-coproduct-morphism-components`) retains its pre-existing hole in its own
module; this delivery uses its declaration as instructed and does not change that module.
Thus the assigned theorem is proved from the stated dependency, rather than being axiom-free
independently of that dependency.

## No longer needed

`lem-galois-epi-iff-cokernel-pair` is removed from this node's proof dependencies: the
one-point uniqueness clause proves epimorphism by cancellation directly. No library module
can be withdrawn on this basis, since that dependency is a Mathlib leaf.

No original imports were removed. All original imports are used. The trial explicit imports
`Mathlib.CategoryTheory.Limits.Constructions.EpiMono`,
`Mathlib.CategoryTheory.Limits.Types.Coproducts`, and
`Mathlib.CategoryTheory.Limits.Types.Products` were removed after compilation confirmed the
existing imports already expose their APIs. The final import list equals the original one.
Every other declared dependency remains used, either as an axiom/definition or in the
corresponding Mathlib argument. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned cokernel-pair argument was valid but unnecessary: cancellation follows directly
from evaluation uniqueness and the nonempty fibre of a connected object. The proof now uses
this shorter route. No statement or definition repair was needed, and there are no new nodes.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
