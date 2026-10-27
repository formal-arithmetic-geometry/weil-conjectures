## What changed

Proved `CategoryTheory.dm_isom_space_unramified` in the assigned module from the existing unramified-diagonal theorem. Private helpers construct cartesian sections, normalize the iso-comma presentation, prove section bijections and restriction compatibility, and establish chartwise unramifiedness after the actual sheaf pullback. The existing public theorem signature and public imports are unchanged. The node now records the implementation and its actual dependencies. To prevent repeated kernel expansion, private comparison isomorphisms have proved equation interfaces. The value wrapper is chosen from a fully proved equality to the explicit construction, which uniquely determines its value; it introduces no opaque declaration or unproved data. Existing limit instances are cached privately.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.dm_isom_space_unramified` (node `lem-sfb-dm-isom-space-unramified`). No new holes or public statements are added. All private constructions and helpers are proved. No `sorry` remains in the delivery. Existing imported theorem holes are used as permitted by stage 3. The complete development compile reached all declarations in 34 seconds; the delivery compile and axiom probe passed in 34.6 seconds; an unused-variable warning was then removed before resubmission.

## No longer needed

Removed the private proof import `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`. The proof does not need node `lem-weil-pbc-etale-smooth-zero-dimensional-fibres` or its zero-dimensional-fibre assertions: Mathlib supplies etale implies smooth directly. Removed that obsolete top-level `tool_uses` entry from the assigned node. This is local pruning; other source declarations and other consumers are preserved. Also removed the unused private proof import `Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests` added during development; its declarations are not used directly. Its existing consumers are unchanged. No other declared dependency of the original plan is pruned.

## Where the brief, the DAG or earlier work was wrong

The informal plan describes the diagonal theorem as already testing every scheme map into the product stack. Its Lean definition supplies two independent scheme tests, a representative over their product, and comparison isomorphisms for both projections. An additional actual pullback along the scheme diagonal is therefore necessary. The proof supplies that pullback and proves chartwise unramified base-change stability from scheme etale locality; it does not silently assume the stronger every-test formulation. The section bijections also require normalizing the two specified projections and transporting arbitrary cartesian lifts.

The launcher paused this session to reduce the compile queue and resumed it with unchanged work. The reference metadata changed from start `1792748899.489006` to `1792774004.8801231`; the worker did not edit budget metadata. Work continued on the saved proof.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
