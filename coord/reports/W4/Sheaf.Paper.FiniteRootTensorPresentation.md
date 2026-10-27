## What changed

Filled `existsUnique_finiteTensorPositivePresentation` in
`Sheaf.Paper.FiniteRootTensorPresentation` by constructing the ratio at one primitive
root, proving that the two scalar changes cancel, and evaluating the normalization
at that root for uniqueness. Added two proof imports for independent power-equivariance
lemmas, and a proof import for algebraically closed fields having enough roots of unity.
Every existing public signature, definition body, and public import is unchanged.
The private categorical cancellation lemma is fully proved.

Validation: both split-lemma modules compiled through lcompile.py. The main module
compiled after repairing its scalar-cancellation simplification and the final
mapIso/symmetry equality (exit code 0, compiled). The combined DAG dependency reach
was checked and no path from a new dependency returns to the item node. Width and
hole-location checks pass; the new-node proof_deps equal the union of proof-step uses.

The two missing power calculations are separate public theorems, one per new module:
`Sheaf.Paper.FinitePublishedRootChartPower` and
`Sheaf.Paper.FinitePositiveRootChartPower`. Neither mentions the desired presentation
or its existence. The first concerns the published ordered shifted tensor recursion;
the second concerns the integral-reduced ordinary basis normalization and its single
complex. Their combination in the item is a complete Lean proof.

## Proved and sorry left

Original holes: 1. Closed in the item:
`WeilConjectures.PurityFiniteSetting.existsUnique_finiteTensorPositivePresentation`
(node `def-pur-finite-root-tensor-presentation`). No `sorry` remains in the item.

Added holes: 2, both whole named public theorem proofs:

- `WeilConjectures.PurityFiniteSetting.finiteReductionPowerTrivialization_pow`
  (node `lem-pur-finite-published-root-chart-power`).
- `WeilConjectures.PurityFiniteSetting.finiteTensorPositiveChart_pow`
  (node `lem-pur-finite-positive-root-chart-power`).

This is a decomposition of one hole into two strictly smaller independent chart
calculations, not a claim of a net proof gain. Each new theorem has its source,
full proof in words, and DAG attachment. No arbitrary data are chosen from either
new theorem: the existing canonical presentation still uses the unchanged unique
normalization theorem, whose proof now constructs its witness explicitly.

Edge cases checked mathematically: d=0 gives scalar a^0=1 and the fixed coefficient
unit charts; a=1 and identical roots give identity changes; both statements hold on
empty schemes because the same module-morphism equations hold there. The exponent
is nonzero, and the field has a primitive root because it is algebraically closed
and the exponent is invertible. For d=1 and zeta=eta^a, the chart at eta is a times
the chart at zeta (the charts use inverse root trivializations); this checks the
direction of both formulas. No finite-type or connectedness hypothesis is added.

## No longer needed

None. No existing module, node, or public import is withdrawn. The original node had
no proof dependencies or numbered proof plan; its statement dependencies are retained.
All five definition dependencies still supply the actual charts, lines and reduction
used by the module. The existing source-chart scalar transition and coefficient
reduction source-chart independence theorems are not imported: their statements concern
purity source charts and do not compare the integral-reduced positive chart to the
published shifted root chart. They are not claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The item's DAG proof and proof_deps were empty even though its docstring proposed
root-independent chart cancellation. Existing chart APIs did not state the two
power laws that cancellation needs. Added these laws and updated the item proof
and proof_deps to match the Lean argument. No statement or definition repair was
needed. The unit route is preserved: this is the twist-presentation comparison
inside finite-reduction Step 2, not a replacement of any unit's statement or step.
The latest blueprint finite-reduction proof Step 2 and the purity-transport unit
were read; the new calculations expand that step's invertible-twist compatibility.

Searches: LeanFinder and LeanSearch returned primitive-root/cyclotomic-character
facts and linear tensor-power facts; Loogle returned mapIso_trans; Mathlib grep
returned no chart hits. Local searches found no existing statement of either
power law. Blueprint searches for root chart scalar and primitive root found no
equivalent blueprint theorem.

## New nodes

`lem-pur-finite-published-root-chart-power`: the change-of-root equation for the
published shifted root tensor recursion. Its proof in words starts with the
section-normalized ordinary root trivialization, then uses induction on d and
additive exact comparison inverse image. This is independent of the integral-reduced
line and of the presentation theorem.

`lem-pur-finite-positive-root-chart-power`: the change-of-root equation for the
integral-reduced positive chart. Its proof in words transfers the first-root
normalization to ordinary sheaves, then checks ordered basis powers and applies
the additive degree-zero single functor. This is independent of the published
shifted tensor recursion and of the presentation theorem.

Both nodes inherit sec-smooth-purity/sk-thm-purity-transport, cite the nearest
blueprint ancestor thm-pur-finite-reduction-of-purity, and record actual Mathlib
searches. No change record is required: no existing public interface changed.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
