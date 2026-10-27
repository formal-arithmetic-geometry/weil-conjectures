## What changed

Proved `AlgebraicGeometry.ConormalGradedAlgebra.exists_conormalCoproduct_affine_addEquiv`
with its existing statement. Only the assigned Lean module and its proof-route node are changed.
All added imports are private proof imports; the existing public imports are preserved.

The proof constructs the affine quotient equivalence using the surjective quotient projection,
its kernel, and the actual injective power inclusion. It then evaluates
`closedImmersion_power_quotient` with the adjunction used by `representative`, so its projection
identity gives the required normalization. A separate proved private helper restricts a
quasi-coherent coproduct to an affine chart and applies the inverse tilde equivalence in the
full subcategory of quasi-coherent modules. Comparing with the concrete module coproduct and
composing the degreewise equivalences proves the result. Every private helper has a complete
proof. Degree zero, zero/unit ideals and empty affine inverse images require no extra hypotheses.

Validation: the complete proof and axiom probe passed through `lcompile.py` in 22.7 seconds.
`#print axioms` listed exactly `propext`, `Classical.choice`, and `Quot.sound`, with no
unproved dependency. The sole long-docstring-line warning was corrected before delivery; the
temporary axiom-print command was removed. The delivery tool compiles and preflights the final file.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.ConormalGradedAlgebra.exists_conormalCoproduct_affine_addEquiv`
(node `lem-pur-conormal-coproduct-affine-add-equiv`).

Holes closed: 1. Holes added: 0. Holes left in delivered files: 0.
There are no split-off theorems and no definition repairs or statement changes.

## No longer needed

The proof no longer directly uses the planned dependencies
`lem-weil-pbc-formal-associated-graded-affine-multiplication`
(`WeilConjectures.AlgebraicGeometry.FormalAssociatedGradedAffineMultiplication`) or
`lem-weil-pbc-module-pullback-affine-sections`
(`WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`).
The former's elementary power-range calculation is obtained directly from the existing
ideal-times theorem, and the latter is replaced by the normalized closed-immersion quotient
isomorphism. Neither module is imported by this delivery. No previously public import is
removed and no module is withdrawn. These are removals from this node's direct proof plan;
other consumers and transitive imports can still need the corresponding modules.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's tensor-sections route was unnecessary: the existing
closed-immersion quotient theorem already preserves the exact chosen adjunction unit.
The affine coproduct step is supplied here by a complete proof using the full subcategory
and tilde equivalence, rather than another split-off obligation.
The unit record `sk-def-purity-conv` has no realized steps to bypass and is unchanged.

The new generic tools are existing proved declarations: the closed-immersion quotient
comparison, the canonical tensor-pullback quasi-coherence comparison, and open-restriction
colimit preservation. They are recorded in the updated proof dependencies; no new unproved
tools or node approvals are introduced.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
