## What changed

Replaced the hole in AlgebraicGeometry.Etale.sfEtaleGraphExchangeTensor by the
exchange/projection theorem already proved in
WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange, followed by
naturality and cancellation of the canonical isomorphisms. Added that module as a
private proof import; the original statement and public imports are unchanged.
Six private lemmas handle cancellation, the categorical tensor transport and its
component form, component normalization, projection naturality, and geometric
specialization. Two private component abbreviations expose functor composition.
A private graph-map construction records the existing formula with general
coefficients. The geometric proof supplies the actual component expressions
directly, avoiding slow kernel conversions through nested local data definitions.
The public theorem specializes the geometric identity to modules and identifies the graph
map by its defining formula. No existing definition or attribute is changed.
Updated the node proof and dependencies to this route.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.Etale.sfEtaleGraphExchangeTensor
(lem-sf-etale-graph-exchange-tensor): one of one holes closed, zero holes added,
zero holes remaining in the delivered module. All private helpers are proved.
No new public statement or node is added. The complete proof compiled in 33.4
seconds before final formatting and removal of profiling output. The delivery
probe subsequently compiled in 16.9 seconds; its sole documentation-line warning
has been fixed. Delivery checks validate the cleaned file again.

## No longer needed

No existing import is removed, and no module is withdrawn. The proof uses the
already proved ordinary etale specialization lem-kun-proj-formula-natural instead
of importing Sheaf.Paper.RingedExchangeTensorCoherence
(lem-weil-pbc-ringed-exchange-tensor-coherence). It does not import
Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal
(lem-kun-derived-pullback-composition-monoidal): the square tensor compatibility is
already part of the proved specialization, and the compactification comparison
only occurs as a morphism moved through exchange by naturality.
The exact tensor construction is used directly from
Sheaf.AlgebraicGeometry.ExactPullbackTensorComparison
(def-sf-exact-pullback-tensor-comparison), so the broader
Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons module
(def-pur-supported-localization-comparisons) is not a proof dependency here.
These are local dependency omissions; no global pruning count is claimed.

## Where the brief, the DAG or earlier work was wrong

The planned mathematics is correct. Its ordinary etale exchange/projection
alternative is already proved and avoids constructing a general ringed-topos model.
The private geometric helper keeps the coefficient instances abstract during the
naturality calculation. No target or other statement is changed.
Mathlib searches ran with leanfinder, loogle, and grep; none supplied the full
identity. Source search found the proved ordinary etale theorem above.
The proof uses naturality and invertible tensor comparisons only; it needs no
proper-exchange invertibility, boundedness, coefficient finiteness, or etaleness.
Empty schemes, zero coefficients, and zero complexes impose no extra conditions.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
