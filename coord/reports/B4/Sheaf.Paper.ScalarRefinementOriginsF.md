## What changed

Proved `WeilConjectures.PurStrictScalar.scalar_refinement_origins_F` in
`Sheaf.Paper.ScalarRefinementOriginsF`, with its signature unchanged. Added private
proof imports of `Sheaf.Paper.ScalarRefinementOriginsE`,
`Sheaf.Paper.CompactSupportCoefficientModels`, and `import all
Sheaf.Paper.CompletedIntegralFiniteFree` for its already proved
`integral_ramification` helper. The positive ramification factorization gives the
ideal equality required by `compactSupportCoefficientModels_scalar`. Its first
conclusion supplies finite-Tor integral constructibility of the completed scalar
extension. The E-side origin theorem, instantiated at F, then gives exactly the
required family of witnesses. Updated the proof docstring and the item's DAG proof,
proof dependencies, and proof origin to describe this route. No other existing
module, interface, definition, or target statement changed.

The single-file server compile passed in 6.8 seconds, with no warnings or errors.
The new proof imports are all used. Original public imports are retained for the
existing statement context and public interface.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.PurStrictScalar.scalar_refinement_origins_F`
(node `lem-pur-compact-support-strict-scalar-refinement-origins-f`).
There are zero holes left in the item and zero holes added anywhere. No split-off
statements were created. This proof uses the already stated
`WeilConjectures.PurStrictScalar.scalar_refinement_origins_E`, whose existing hole
belongs to node `lem-pur-compact-support-strict-scalar-refinement-origins-e` and is
not changed by this delivery. No claim of axiom-free transitive closure is made.

## No longer needed

No imports or modules are removed. The item's proof no longer applies
`lem-sf-proetale-constructible-origin` directly: the existing E-side origin theorem
already encapsulates that argument over any coefficient field. It also no longer
unpacks `def-weil-derived-complete-integral-detailed` and
`def-weil-finite-tor-amplitude` directly: the coefficient-model scalar theorem
returns exactly the input predicate needed by the E-side origin theorem. These
three nodes remain needed through the reused theorems or by the item's statement;
no global pruning or withdrawal is claimed. No unit statement or realized unit
step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier proof plan repeated the single-field origin argument on the scalar
extension. Reusing the existing E-side statement is shorter. The original plan
also left preservation of integral finite-Tor constructibility implicit; this
proof explicitly obtains it from the existing scalar clause of the recorded
coefficient-model dependency. No mathematical statement was corrected. The private
ramification helper is fully proved: its DVR and absolute-value argument supplies
an exponent even though this item's hypotheses do not specify one. Units only
change a principal ideal by equality, so chosen uniformizers need not map to each
other. The identity coefficient extension, the zero input, and an empty scheme
introduce no extra restriction in either reused theorem.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
