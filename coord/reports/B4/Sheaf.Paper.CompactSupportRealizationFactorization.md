## What changed

In `Sheaf.Paper.CompactSupportRealizationFactorization`, proved
`WeilConjectures.CompactSupportRealizationFactorization.q_naturality` without changing
its signature. Three private helpers assemble the specified proper/open system map
as a natural transformation, identify its components with `rho`, and assemble `q`
from the reduction unit, total limit and inverse strict-tower presentation.

The sole added proof import is
`import all Sheaf.SixFunctors.OpenReconstructionEffectivity`. It supplies the already
proved private helper `WeilConjectures.GeneratorReduction.fixedOpenReduction_isIso`.
That helper applies to every integral object and every open immersion, so the proof
needs no new Tor, quasi-compactness or geometric-field hypothesis. Pointwise
`inverseOrZero` agrees with the inverse natural transformation by this invertibility.
The canonical bridge and all reconstruction components retain their existing values.

The existing proved `coefficientFactorization` now applies
`CompactSupportFactorNormalization.coefficient_factorization` twice instead of
expanding the projection paste. Added local irreducibility attributes for large
ambient category and derived-functor constructions, matching the normalization
module, to avoid expensive conversion during elaboration. These are local; public
definitions, signatures, imports and instances are unchanged.

The module compiled in 28.7 seconds before the final line-width correction. The
final delivery command compiles the corrected file and runs the declaration probes.
Only the item module and its own DAG node are changed.

## Proved and sorry left

Closed 1 of the original 5 holes:
`WeilConjectures.CompactSupportRealizationFactorization.q_naturality`.
Added 0 holes and split off 0 statements. The existing coefficient-factorization
proof remains proved. All private helpers have complete proofs.

The following 4 holes remain unchanged, all attached to
`lem-pur-compact-support-realization-factorization`:

- `WeilConjectures.CompactSupportRealizationFactorization.compactSupport_realization_factorization`
- `WeilConjectures.CompactSupportRealizationFactorization.identityProperReduction`
- `WeilConjectures.CompactSupportRealizationFactorization.identityProperRealization`
- `WeilConjectures.CompactSupportRealizationFactorization.identityProperCoefficient`

This is a partial delivery for a module with several holes, as allowed by the brief.

## No longer needed

None. No imports or dependency nodes are removed. In particular, the original
proof dependencies remain needed by the four untouched obligations. No upstream
source declarations or modules are removed or changed. The naturality proof uses
the existing open-reconstruction node as a tool for the fixed open-reduction mate;
it does not replace any step of the purity-transport unit route.

## Where the brief, the DAG or earlier work was wrong

The naturality explanation must justify that pointwise `inverseOrZero` is natural:
this does not hold for an arbitrary natural transformation with noninvertible
components. The already proved `fixedOpenReduction_isIso` provides precisely the
needed unconditional component invertibility here. The item node's final step now
records this justification and the actual natural-transformation construction.
No statement or definition correction was necessary.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
