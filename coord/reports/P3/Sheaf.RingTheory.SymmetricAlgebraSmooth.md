## What changed

Proved `SymmetricAlgebra.smooth_of_finite_projective` with its exact original signature.
The proof obtains finite presentation from the existing
`SymmetricAlgebra.generators_and_finitePresentation`, using Mathlib's
`Module.finitePresentation_of_projective`. It proves formal smoothness directly:
projectivity lifts the restriction of any map to the degree-one module through a quotient;
`SymmetricAlgebra.lift` extends that linear lift, and `SymmetricAlgebra.algHom_ext`
verifies the required composite. `Algebra.Smooth.mk` combines the two fields.

Replaced the two proof imports by the single proof import
`Sheaf.RingTheory.SymmetricAlgebraFinitePresentation`. Both public imports are unchanged.
Updated the target node's proof, proof_deps and proof_origin to this route. No signatures,
definitions, or public interfaces changed. The unit `sk-thm-p1` realized statements and
steps are preserved: neither the old local-cover dependencies nor the new finite-presentation
node is one of those realized steps.

## Proved and sorry left

Closed 1 of 1 holes: `SymmetricAlgebra.smooth_of_finite_projective`
(node `lem-weil-pbc-symmetric-algebra-finite-projective-smooth`). There are no direct
`sorry`s left in the delivered module and no new holes or modules.

The existing imported theorem `SymmetricAlgebra.generators_and_finitePresentation`
(node `lem-weil-pbc-symmetric-algebra-finite-presentation`) still contains its original
`sorry`; this delivery uses its finite-presentation clause and does not claim a
sorry-free proof of the entire dependency closure. Formal smoothness is proved entirely
from Mathlib and the symmetric-algebra universal property.

## No longer needed

Removed proof imports:
- `Sheaf.RingTheory.FiniteProjectiveStandardFreeCover`
- `Sheaf.RingTheory.SymmetricAlgebraBaseChange`

The target proof no longer needs these local-cover nodes:
- `lem-weil-pbc-finite-projective-standard-free-cover`
- `lem-weil-pbc-localization-tensor`
- `lem-weil-pbc-symmetric-algebra-base-change`
- `lem-weil-pbc-polynomial-ring-smooth`
- `lem-weil-pbc-smooth-ring-map-principal-localization`
- `lem-weil-pbc-smooth-ring-map-base-change-composition`
- `lem-weil-pbc-smooth-ring-map-local-on-cover`

`lem-weil-pbc-symmetric-algebra-free-module-polynomial` is removed as a direct dependency
of this target, but remains needed by the finite-presentation dependency's own proof plan.
The universal-property and smooth-ring-map nodes remain directly used. The removed
modules may still be reached elsewhere; this report makes no whole-library pruning claim.

## Where the brief, the DAG or earlier work was wrong

No false statement or tool problem found. The old docstring describes a valid planned
standard-cover argument, but the compiled proof now takes the shorter lifting route
recorded in the updated DAG. The existing finite-presentation theorem supplies exactly
one field of smoothness, so using it is a genuine reduction rather than a restatement.
The lifting argument also covers the zero module and the zero ring without a rank or
nontriviality assumption, and preserves independent universes.


## Second reading by P3

1. **Unchanged interface — pass.** Compared the only delivered Lean module with the
   repository using `diff -u`: the existing theorem signature is byte for byte unchanged,
   both public imports are unchanged, and no definitions or declarations were added.
   Only its proof and private proof imports differ; no change record is required.
2. **Proof and trust — pass, with an existing dependency hole.** Compiled the module
   through `lcompile.py` without errors or warnings. A scratch copy with
   `#print axioms SymmetricAlgebra.smooth_of_finite_projective` reports `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is expected from the
   existing `SymmetricAlgebra.generators_and_finitePresentation`; this is a closed
   direct hole, not a fully axiom-free proof of the closure. There are no direct
   `sorry`s or forbidden declarations in the delivered module. The quotient lift
   equation proves equality on every degree-one generator, and `algHom_ext` proves
   equality of the algebra maps. The argument works even for arbitrary quotient
   ideals, so in particular for the square-zero ideals in formal smoothness.
3. **Split statements — pass (none).** No new statements, nodes, or holes were split
   off. The finite-presentation clause used is strictly one part of smoothness,
   not a renamed restatement. Its module presentation argument is valid also for
   rank zero and the zero ring; formal smoothness imposes no nontriviality or
   equal-universe hypothesis. The existing dependency is outside this delivery.
4. **Shortest route and pruning — pass.** Independently searched Mathlib with
   LeanFinder for finitely presented symmetric algebras, and searched Mathlib,
   the upstream checkout, and `lean/` using finite-presentation and smoothness
   patterns. No established shorter applicable theorem was found. The lifting
   proof directly uses Mathlib's projective lifting property and symmetric-algebra
   universal property. Each remaining import supplies a signature or proof need.
   Compared old and new `proof_deps`: all eight removed dependencies are reported
   in `No longer needed`, including the free-module polynomial node that remains
   below the finite-presentation node. Checked `dag/units/sk-thm-p1.json`:
   none of these local auxiliary nodes realizes its statement or its four steps;
   the unit route is preserved.
5. **DAG agreement — pass.** Only `proof`, `proof_deps`, and `proof_origin` change
   in the existing node. Their steps accurately describe finite presentation,
   the projective linear lift, extension by `lift`, uniqueness by `algHom_ext`,
   and `Algebra.Smooth.mk`. Checked the Lean records/Mathlib matches of all four
   retained dependencies. No new-node fields are needed.

Second-reading changes: added this independent review and explicit axiom-check evidence
in the report. The proof and node were correct and were left unchanged. The original
Lean docstring retains its historical standard-cover plan; the inline proof comment,
updated DAG, and report explicitly identify the shorter implemented route.
