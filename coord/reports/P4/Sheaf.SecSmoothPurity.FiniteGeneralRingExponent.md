## What changed

The statement, binders and public import of `finiteGeneralRingExponent` are unchanged.
Its proof constructs the common maximum annihilator with `pow_dvd_pow` and the
characteristic-divisibility criterion. The exponent clause of
`Scheme.etaleFiniteTwistPullback` supplies both root-power maps and their normalized
Tate-line isomorphisms. The other orientation is the explicit composite
`alpha ≪≫ e.symm ≪≫ e'`, where e and e' are the prescribed ordered shifted tensor
powers. No orientation is chosen from an unproved mere existence statement.

The private, proved `bundle_exponent` transports the integration identity through
`Adjunction.homEquiv_naturality_left`, then through zero-section pullback using
naturality of `leftDerivedUpperStarCompSectionIso`. The main proof reuses exactly
the supplied normalized Rees-family isomorphism and cone/bundle square. The two
bundle-adjunct identities establish its normalization at the new exponent;
isomorphism cancellation proves the final common-line equality.

A new proof-only import, `Sheaf.SecSmoothPurity.FiniteGeneralRingIntegrationExponent`,
is the sole new geometric input. It isolates actual bundle integration, before any
adjunction transpose, zero-section restriction, smooth diagonal, Rees comparison,
or orientation. The node proof and dependencies now describe this assembly.
No existing dependency module, source-library declaration, definition, public
signature, attribute or instance is changed.

Validation: both delivered Lean modules compiled through `lcompile.py`; the final
item compile completed with exit code zero and no errors or warnings (18.7 s).
The public item signature was compared verbatim with the repository, and the new
node signature was compared with its Lean declaration. The existing node changes
only `proof`, `proof_deps` and `proof_origin`. A dependency traversal found no path
from the new node back to its parent. Both Lean files have no line over 100 characters.

## Proved and sorry left

Original hole: `AlgebraicGeometry.ProEtale.finiteGeneralRingExponent`
(`lem-sp-general-ring-exponent`). Its body is now a complete Lean proof from the
named inputs. The common-exponent construction, both generator comparisons, the
adjunction/zero-section transport, the new orientation normalization and the final
orientation equality have no local holes.

One new hole: `AlgebraicGeometry.ProEtale.finiteGeneralRingIntegrationExponent`
(`lem-sp-general-ring-integration-exponent`), the actual arbitrary-finite-ring
vector-bundle integration equation. Its entire proof is `by sorry`, with the
source and complete Kummer-to-projective-to-affine-to-frame-gluing argument in
its docstring and node. This is one hole closed and one added: a decomposition,
net zero holes, rather than a claim that the geometric comparison is finished.
There are zero sorries in the item and one in the added module. No other hole is
added. `bundle_exponent` is private and completely proved.

The new assertion was checked mathematically at equal exponents (the power map
and normalized line map are identities), rank zero (the empty tensor and identity
counit), N=1 (A is the zero ring), the zero ring, and the empty base. It does not
assume A is flat over Z/N or divide by an element of A.

## No longer needed

No original import was removed: the item originally publicly imported only
`FiniteGeneralRingData`, which still supplies its unchanged public statement.
No module is claimed globally pruned or withdrawn.

The direct proof dependencies `det-sp-reduction-exceptional` and
`lem-pur-dnc-coefficient-transport` are removed from this node's proof route.
The coefficient ring and geometric objects do not change, and the supplied kappa
and its normalization can be reused verbatim; no scalar exceptional comparison or
uniqueness comparison of independently chosen Rees maps is needed.
`ReductionExceptional` remains in the existing public import closure of
`FiniteGeneralRingData`; this delivery does not claim its removal from that closure.

`lem-amb-kummer-any-base`, `def-amb-p1-trace`,
`lem-amb-affine-space-top-trace` and `def-amb-vector-integration` remain needed
inside the new integration node. `lem-asd-etale-finite-twist-pullback` is used
explicitly in the item and retained below the integration step as well. None of
these nodes is withdrawn. The unit's Kummer/integration route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan concealed the arbitrary-finite-ring exponent
compatibility of actual bundle integration. The supplied `vectorExponentIndependence`
in `VectorIntegrationSiteComparison` handles only the coefficient quotients
`finiteTateCoefficient ell E n`. It does not specialize to arbitrary finite A.
`integratedSpecialization_scalar` changes coefficients and includes scalar
functors and section mates; it does not directly give the fixed-coefficient
bundle trace identity used here. `normalizedOrientation_scalar` additionally requires
invertibility on Y, which this statement does not assume; invertibility on X alone
does not imply it. The new node isolates precisely that missing
geometric step rather than duplicating the whole orientation statement.

The existing coefficient-transport declarations named in the original plan also
use finite-field/finite-type presentations absent from this item's general
Noetherian-scheme hypotheses. They are unnecessary for this proof: alpha's
existing Rees witness already has the required coefficient-independent type.
The original target-level statement has not been weakened or changed.

## New nodes

`lem-sp-general-ring-integration-exponent`, module
`Sheaf.SecSmoothPurity.FiniteGeneralRingIntegrationExponent`, states the
Kummer-normalized equality of actual vector integration arrows for a finite
ring A and positive annihilators N dividing M. This is strictly a part of the
source's exponent-independence argument. It neither asserts the existence of an
orientation nor compares diagonal/Rees constructions. The item itself proves
all root-map existence, annihilator arithmetic, transposition, zero-section
naturality, orientation construction and final cancellation. No change record is
needed because no existing public interface or definition was changed.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
