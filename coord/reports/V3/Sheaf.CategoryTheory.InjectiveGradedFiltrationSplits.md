## What changed

Proved `CategoryTheory.FilteredObject.injective_graded_filtration_splits` in
`Sheaf.CategoryTheory.InjectiveGradedFiltrationSplits`, preserving its statement,
universes, visibility, specified interval, and equality of embedded filtration subobjects.

The proof takes the graded pieces themselves as the summands. Injectivity extends each
quotient map to the whole object. These coordinate maps restrict to every tail; the short
five lemma shows by finite descending induction that the restrictions are isomorphisms.
The assembled map is the required single isomorphism. All auxiliary constructions and
lemmas are private and proved. Updated the existing node's proof, proof dependencies, and
proof origin to this shorter route. The unit's route is unchanged.

Change record: `coord/changes/injective-graded-filtration-splits-proof-environment.md`
records the scoped parameters for private tail helpers required by static preflight.
These commands end before the original theorem and change no public interface.

Read Stacks `derived.tex`, Tag 05TP, `lemma-filtered-injective`, and the existing Mathlib
short-five-lemma node and declaration. LeanFinder returned module-filtration and Dold–Kan
results, with no theorem for this filtration. Loogle found
`ShortComplex.ShortExact.splittingOfInjective`, which only splits one short exact sequence.
The grep search likewise found no compatible finite-filtration splitting theorem.

Validation: the complete module compiles through the required `lcompile.py`, without
warnings (rechecked after resuming); a fresh `#print axioms` check of the final proof reports only
`propext`, `Classical.choice`, and `Quot.sound`. Edge cases are covered explicitly:
the empty tail at `b + 1`, all indices below `a`, all indices above `b + 1`, singleton
intervals, negative bounds, zero objects, and zero graded pieces.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.FilteredObject.injective_graded_filtration_splits`
(node `lem-trf-injective-graded-filtration-splits`).

Added 0 holes. No `sorry` remains in the delivered module. No statements were split off.
This is a complete proof from existing proved declarations, not a decomposition.

## No longer needed

Removed the redundant direct proof import
`WeilConjectures.CategoryTheory.Abelian.Filtration`; its declarations are already publicly
available through `Sheaf.CategoryTheory.Filtration`. Its filtration definitions and
`imageSubobject_comp_eq_of_epi` are still used, so this is only a redundant import removal,
not withdrawal of that module from the library.

The new proof does not use the planned nodes `lem-weil-pbc-product-injectives` or
`lem-weil-pbc-ses-injective-kernel-splits`: no injectivity of filtration steps is required,
and no compatible choices of one-step splittings are made. Their former proof-dependency
edges are removed. The public injectivity import remains necessary for the theorem's
statement. No Lean module is withdrawn; no other dependencies are pruned. The existing
Mathlib leaf `lem-weil-pbc-short-five-lemma` replaces those two proof tools.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The old six-step splitting plan is
valid but longer than the coordinate-extension proof. The old theorem docstring still
records that valid alternative argument; the node now describes the implemented proof.
No target statement, definition, consumer signature, or unit statement is changed.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
