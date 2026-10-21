## What changed

Proved `HenselianLocalRing.integral_component_henselian_permanence` in
`Sheaf.RingTheory.IntegralComponentHenselianPermanence`, preserving its complete public
signature and all public imports. Added two proved private helpers: one transports
henselianity from the unique factor of the existing finite-product decomposition, and
one derives locality of an integral map of local rings from maximal-ideal contraction.

Finite subalgebras suffice for both locality and simple-root lifting: for the latter,
adjoin the finitely many polynomial coefficients and the approximate root. This is the
direct argument in Stacks Algebra Tag 04GI. Reducing a monic integral equation proves
algebraicity for the exact canonical residue-field algebra in the theorem's signature.
Mathlib's `Algebra.IsAlgebraic.isSepClosed` then proves the strict henselian assertion.
Added the proof import `Mathlib.Algebra.Polynomial.Lifts` to descend the polynomial.
Updated the existing node's proof, proof dependencies and proof origin to this route,
and removed its obsolete filtered-colimit tool approval.
No statements, definitions, unit realizations or other modules changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`HenselianLocalRing.integral_component_henselian_permanence`
(node `lem-trf-integral-component-henselian-permanence`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
Both private helpers have complete proofs. The server single-file compile passed in
3.9 seconds with no diagnostics; `#print axioms` for the main theorem reported exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed these proof-only imports:

- `WeilConjectures.RingTheory.FilteredColimitHenselianPair`:
  direct simple-root lifting in a finite subalgebra replaces the categorical colimit.
- `Mathlib.CategoryTheory.Limits.HasLimits`: no colimit is constructed.
- `Mathlib.FieldTheory.Separable`: the general algebraic-extension theorem handles
  separable closedness directly.
- `Mathlib.FieldTheory.IsSepClosed`: the required API is already provided by the retained
  `Mathlib.FieldTheory.PurelyInseparable.Basic` import.

Removed direct DAG proof dependencies
`lem-weil-pbc-filtered-colimit-henselian-pair`,
`def-weil-pbc-category-colimit`, `def-pc-separable-polynomial`, and
`def-pc-separably-closed`. The last definition remains part of strict henselian
terminology; it no longer requires a separate polynomial root argument in this proof.
The obsolete top-level `tool_uses` entry for
`lem-weil-pbc-filtered-colimit-henselian-pair` is removed.
The finite-extension leaf remains used through its recorded Mathlib theorem in the
stronger algebraic-extension form. These removals concern this item's proof only;
no source-library declarations or modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original seven-step plan is mathematically sound but unnecessarily constructs a
categorical filtered colimit of henselian pairs. The simple-root definition of
`HenselianLocalRing` needs only one finite subalgebra for each lifting problem.
The residue-field algebraicity already proved in the theorem also makes the original
finite-coefficient separability descent unnecessary, because the recorded Mathlib leaf
applies to arbitrary algebraic extensions. The existing unit route is preserved.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
