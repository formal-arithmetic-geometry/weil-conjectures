## What changed

Proved `WeilConjectures.PurityFiniteSetting.finiteReductionLineChart_scalars`.
The proof-only import `Sheaf.Paper.FiniteRootLinePowerTransition` supplies the
already proved ordinary root-chart power formula. A proved private helper
`lineChart_hom_power` transports that formula through single complexes, shift,
comparison inverse image and intrinsic realization, including their shift maps.
Mathlib supplies a common power exponent for the two compatible root pairs.
Additivity of finite reduction and bilinearity of composition then reduce both
sides to that exponent times the supplied arrow. The statement and all public
definitions are unchanged. Updated the node's proof and dependencies to record
this route. No new public declarations or modules were added. Validation uses the remote
single-file compiler and the delivery tool’s declaration and axiom probes.

## Proved and sorry left

Closed one of one original holes:
`WeilConjectures.PurityFiniteSetting.finiteReductionLineChart_scalars`
(node `lem-pur-finite-reduction-line-chart-scalars`).
No holes remain in the item, and no holes were added or split off.
The private helper `lineChart_hom_power` is proved completely.

## No longer needed

None: no existing imports or dependencies were removed. The proof uses the
existing ordinary root-line transition rather than repeating its section
calculation. It does not need an inverse integer, a coprimality lemma, ordered
tensor-power source-chart independence, or a flatness hypothesis. These were
not imported or deleted. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The original plan proposed inverse scalar and coprimality calculations. They are
unnecessary: choose the exponent in the direction zeta = zeta_prime^c and both
inverse-chart changes become c times the identity directly. Compatible reduced
roots satisfy the same relation by commutation of powers. The already proved
`finiteReductionRootTrivialization_inv_power` provides exactly the needed
ordinary calculation. The proof works for any supplied arrow, including zero,
for the empty scheme, and for m = n, without finite-type assumptions or quotient
flatness. No statement correction or consumer adaptation is required.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
