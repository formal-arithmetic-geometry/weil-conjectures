## What changed

Proved `Padic.exists_integral_basis` in
`Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis`, with its signature unchanged.
The shorter route constructs `C = integralClosure (coefficientExtensionIntegers l E) F`,
uses the existing `Padic.padic_integers_integralClosure` to identify its elements with
those of the upper unit ball, and applies Mathlib's `IsIntegralClosure.finite`,
`IsIntegralClosure.module_free`, and `IsIntegralClosure.rank`. The lower integer ring's
PID and fraction-field properties come from `Padic.extension_integers_dvr`.
Characteristic zero of E follows from the injective map from Q_l, so separability adds
no hypothesis. The existing compatibility hypothesis is retained verbatim.

`Module.finBasisOfFinrankEq` supplies the basis with the requested index set. The proof
then constructs its coefficient tuple, maps its expansion into F, and proves uniqueness
by applying the basis coordinate equivalence to any competing integral tuple.
All choices are bases of actual constructed modules; no hollow definition or arbitrary
witness from a holed mere-existence theorem was introduced.

Added proof-only imports of `Sheaf.NumberTheory.Padics.PadicIntegersIntegralClosure` and
`Mathlib.RingTheory.DedekindDomain.IntegralClosure`. Removed the redundant proof-only
import of `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`, which is already publicly
available through `CoefficientExtensionFinite`. The public import remains unchanged.
Updated the item's proof, proof_deps, and proof_origin to describe this route.

The unit's finite-torsion-free/free argument and its rank d conclusion are retained;
this changes only how the arithmetic input below its step 3 is implemented. No statement,
definition, target, consumer, or public visibility changed, and no change record or
forced adaptation is needed.

Validation: the single-file compiler accepted the complete proof. The Mathlib rank
attachment was separately checked with its full signature and `#print axioms`; it uses
only `propext`, `Classical.choice`, and `Quot.sound`. The delivery preflight checks the
item's axioms and exact remaining-hole inventory. Edge cases E = F, x = 0, l = 2,
ramified extensions, and distinct universes introduce no extra assumptions; existence
and uniqueness use the full module-basis API, including zero coefficients.

## Proved and sorry left

Closed 1 of 1 original holes: `Padic.exists_integral_basis`
(node `lem-sfb-local-field-integral-basis`). No sorry remains in the delivered Lean module.
Added 0 holes and split off 0 theorems.

The imported, pre-existing `Padic.padic_integers_integralClosure`
(node `lem-sfb-padic-integers-integral-closure`) still has its own sorry. It is used as
the existing declared dependency intended by stage 3; it is not changed or duplicated.
Consequently the delivered theorem is proved from project declarations, while its
transitive axiom closure still includes that pre-existing obligation.

## No longer needed

Removed direct import: `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`; its theorem is
still used through the unchanged public coefficient-extension import.

The original direct proof dependencies `lem-weil-l-adic-extension-complete`,
`lem-weil-pbc-finite-dimensional-linear-homeomorphism`, and
`lem-weil-pbc-noetherian-submodule-finite` are no longer used by this module's proof and
were removed from its node's direct proof_deps. The direct bounded-coordinate lattice
construction and separate scaling argument for the rank are replaced by the existing
integral-closure bridge and Mathlib's rank theorem. Some of these nodes remain needed
inside the imported bridge, so this is not a claim that they are globally unreachable.
No Lean module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original node's plan is valid but longer
than the available route: `Padic.padic_integers_integralClosure` is already declared in
the same unit, and it supplies the missing bridge for the Mathlib candidates recorded
in the node. Its own sorry is not an obstacle to this proof. This delivery introduces
no new analytic or arithmetic obligation.

The DAG lacked an attachment for the exact generic rank theorem already in Mathlib.
A search of all DAG matches for IsIntegralClosure.rank found only candidates/search
records, not a matching node. The blueprint search for integral closure rank returned
zero blueprint nodes. Existing generic finiteness and PID torsion-free-freeness nodes
are reused, rather than duplicated.

## New nodes

`lem-sfb-integral-closure-rank` is a Mathlib leaf attached to the existing theorem
`IsIntegralClosure.rank` in `Mathlib.RingTheory.DedekindDomain.IntegralClosure`.
It adds no Lean module and no sorry. Its full statement includes the fraction field,
finite separable extension, integral-closure identification, and compatible scalar
towers. Source lines 192-200 and the theorem's standard axiom closure were checked.
LeanSearch, Loogle, and grep all returned this exact theorem; their actual queries are
recorded in the node. The node includes the basis-localization argument for review.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
