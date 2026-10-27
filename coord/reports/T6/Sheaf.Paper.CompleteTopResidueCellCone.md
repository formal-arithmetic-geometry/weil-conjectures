## What changed

Proved `WeilConjectures.complete_top_residue_cell_cone` in
`Sheaf.Paper.CompleteTopResidueCellCone`, preserving every public declaration's
statement and data definition. The proof reuses the proved lifting, completeness,
projective cohomology and prescribed residue cone APIs. Private proved helpers identify
the coproduct free modules with the product presentation, normalize the canonical
adjoint reduction comparison on each generator, identify the two split complexes,
and detect zero directly from the quotient completion tower. Proof imports use
`import` or `import all`; the public imports are preserved.

Added the fully proved module `Sheaf.Paper.CompletedFreeCoproductReduction`
for normalized finite-free coefficient reduction, with explicit aliases for the
actual free modules and the canonical category structures at the coefficient sizes. Their instance
registrations are local to the new module. This is a genuine subargument,
with no additional holes. The quotient-tower zero criterion remains a private
proved helper in the item.
Updated the item's node proof, proof dependencies and proof origin accordingly.
No other existing module or node is changed. Large predicates stay locally
irreducible during assembly; these local attributes change no exported interface.
Both files passed the remote compilation check.
The original public data declarations and theorem statement were compared verbatim
with the repository source and are unchanged.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.complete_top_residue_cell_cone`
(`lem-sf-complete-top-residue-cell-cone`). No holes remain in the item and no holes
are added. The new public theorem and all private helpers are proved. This is one hole closed, zero split off.
The singleton interval, zero top rank and empty scheme are included.

## No longer needed

Removed the unused plain proof imports
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact`,
`Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`, and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`.

The singleton zero-detection argument does not use
`det-prop-sfb-qlbar-colimit-x-integral-limit`,
`sk-def-pe-derived-completion`, or `det-pe-derived-nakayama-first-reduction`:
DVR quotient triangles and the existing completion tower prove it directly.
Mathlib's distinguished-triangle zero criterion replaces
`lem-kun-distinguished-cone-zero`. The lifting proof uses projectivity directly
from the evaluation hypothesis, so it does not call
`lem-weil-pbc-proetale-weakly-contractible-evaluation-exact`.
The obsolete evaluation-exact, integral-limit and Nakayama entries are removed
from the item's top-level `tool_uses`; the derived-change-of-rings entry stays.
These changes prune this proof's dependencies; no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was required. The two planned lemmas use different
Lean presentations: the lifted-cell module uses finite products, while this item
fixes coproduct free modules and an adjunction-defined comparison; the residue cone
module uses a piecewise split complex and intrinsic slice tensor conventions.
The proof supplies the generator-normalized comparisons and obtains the requested
ordinary pro-etale pullback Tor bound from exact pullback and the existing field
Tor theorem. The blueprint unit route is unchanged.

## New nodes

`lem-sf-completed-free-coproduct-reduction` realizes
`WeilConjectures.completed_free_coproduct_reduction` in
`Sheaf.Paper.CompletedFreeCoproductReduction`. It proves generator-normalized
finite-free reduction and its derived single-cell comparison, without the
complete complex, top-cell lift, cone, or Tor conclusions of the item.

No change records are needed because no existing public statement or data changed.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
