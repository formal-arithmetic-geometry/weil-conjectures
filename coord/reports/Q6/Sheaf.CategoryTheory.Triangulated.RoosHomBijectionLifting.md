## What changed

Proved `CategoryTheory.Functor.map_bijective_of_roos` in
`Sheaf.CategoryTheory.Triangulated.RoosHomBijectionLifting` without changing
its signature or public imports. The proof cancels the source shift comparison,
uses product projections to prove bijectivity of `F.map` into the product, and
performs the kernel-and-image chase directly on the specified distinguished
triangle and its actual image under `F`. Shift naturality verifies the connecting
arrow equation in both injectivity and surjectivity. Updated the existing node's
proof, proof dependencies, and proof origin to record this implementation.

Sources read: Stacks `categories.tex`, definition-product (002I), and
`derived.tex`, lemma-composition-zero (0146) and lemma-representable-homological
(0149). Mathlib's corresponding product and triangle exactness declarations
supply the proof. Searches through msearch (LeanFinder, Loogle, grep) and local
ripgrep found exactness infrastructure but no replacement theorem.

## Proved and sorry left

Closed one hole: `CategoryTheory.Functor.map_bijective_of_roos`
(node `lem-sf-roos-hom-bijection-lifting`). Added zero holes; split off zero
statements. No `sorry` remains in the delivered module.
Final single-file compilation through `lcompile.py` succeeded without warnings
in 5.8 seconds. A temporary `#print axioms` confirmed exactly `propext`,
`Classical.choice`, and `Quot.sound`; the diagnostic command was then removed.
The original namespace commands are preserved. The theorem signature and all
public imports were checked byte-for-byte against
the assigned source. Only the allowed proof fields of the node changed.

## No longer needed

Removed private import `Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four`:
the direct chase proves the five-lemma conclusion without an abelian diagram.
Removed private import `Mathlib.CategoryTheory.Triangulated.Pretriangulated`:
the existing public imports already provide its declarations.
The proof no longer depends on `lem-weil-pbc-five-lemma`; removed it from this
node's proof dependencies. That Mathlib leaf remains available to other nodes.
No project module is withdrawn. All public imports stay identical.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The planned transported target
triangle and abstract five lemma are unnecessary implementation steps: canceling
the product comparison first allows the same argument in the actual image
triangle, whose connecting arrow is exactly `F.map d` followed by the specified
shift comparison. This retains the unit route and the original theorem.
The current blueprint version of `prop-sf-closed-unit-all-stages.proof.md`
now gives a full-faithfulness argument instead of the historical integral-stage
paragraph cited by this node. This delivery proves the assigned standalone
statement from the Stacks product and triangle exactness lemmas; it does not
alter the parent or its route. No new statement requires an edge-case test;
the proof is uniform for zero objects, zero or identity transitions, and the
identity functor, and uses no Mittag--Leffler or vanishing assumption.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
