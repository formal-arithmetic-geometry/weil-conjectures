## What changed

Proved `WeilConjectures.coefFiniteHomSiteDescent_descent` in the item module,
without changing its statement or any definition. The proof supplies all five
clauses of `CoefFiniteHomDescent`: exactness, finite-Tor constructible etale
antecedents, reflection for every bounded constructible antecedent, and preservation
of every ordered Tor interval. Proved private helpers bound finite cohomological
support and transport the intrinsic Tor predicate along an isomorphism by composing
the representative isomorphisms.

The coefficient prime is shown invertible in the residue fields from the finite
field datum. The existing intrinsic finite-ring essential-image criterion gives
the etale antecedent directly, after bounding the finite cohomological support.
The existing Tor comparison lemmas supply preservation and reflection. This keeps
the constructible-origin route and handles empty cohomological support by taking
the minimum and maximum of arbitrary lower and upper bounds.

Expanded the remaining coherence theorem's docstring with the source proof steps.
Updated the descent node's proof and dependencies to this argument. No other
existing module is adapted, and no public statement, definition, instance,
attribute, or public import changes.

Validation: the final module, after removal of ten unused private imports,
compiled through `lcompile.py` without errors or warnings in 21.3 seconds.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.coefFiniteHomSiteDescent_descent`
(node `lem-coef-finite-hom-site-descent-core-descent`).

One original hole remains:
`WeilConjectures.coefFiniteHomSiteDescent_coherence`
(node `lem-coef-finite-hom-site-descent-core-coherence`). It still asks for the
specified monoidal and symmetric structures, coefficient/site tensor squares,
quotient coherence, internal-Hom squares, and transport of equations. Its statement
and the main assembly theorem are unchanged. The coherence proof requires
identifying the abstract comparison lemmas with the fixed normalized tensor and
Hom records; this delivery does not claim those identifications.

Added zero holes and zero split-off statements. This is a proof of one existing
component, not a decomposition. The main theorem remains the existing conjunction
of the two components.

## No longer needed

For the completed descent component, the direct dependencies
`lem-sf-comparison-pullback-exact` and `lem-sf-proetale-constructible-origin`
are replaced by the existing exact intrinsic comparison instances and
`lem-weil-pbc-finite-ring-constructible-derived-origin`, respectively. The latter
is used as a tool for precisely the same bounded constructible etale-origin step;
its statement already uses the intrinsic constant-ring category of the item.
No unit statement or unit proof step is bypassed.

Removed unused private proof imports:

- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.PullbackTensorCanonicalShiftUnit`
- `Sheaf.SixFunctors.FiniteDualitySiteComparison`
- `Sheaf.SixFunctors.CoefMonoidalSquareHomTransport`

No module is withdrawn. Dependencies still belonging to the unproved coherence
component are not asserted to be unnecessary to its future proof.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The current server queue lists this as a two-hole
proof item, not a rework assignment. The build-error file records an older missing
source path; the current source exists and is the basis of this delivery.

The descent plan's recorded constructible-origin theorem uses a different
coefficient presentation. The already stated intrinsic finite-ring derived-origin
theorem avoids rebuilding the conversion and yields the exact antecedent needed.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.Paper.CoefFiniteHomSiteDescent": "d216ec2ea619bb3b2624649255a34f2b606fcbaa"}, "results": {"Sheaf.Paper.CoefFiniteSiteHomTransport": {"hash": "25a7089419505644db4b0e43dac819a1a1a1de9d", "status": "OK"}, "Sheaf.Paper.FiniteCoefficientHomChange": {"hash": "6040c31ddad1fd61407da5e854c90f3fc5f5636b", "status": "OK"}, "Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds": {"hash": "7626d3590cf3bc4e79653aa04822e4946e4c7c0c", "status": "OK"}}, "seconds": 113, "time": "2026-10-28T06:46:19+0800", "transitive": 0, "version": 1}
```

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
