## What changed

Filled `AlgebraicGeometry.Etale.SupportedTrace.contractions` by a Lean assembly of the
coordinate identities before a trace. The first-coordinate identity is postcomposed
with the scalar trace, then projection and tensor-unit naturality give the desired
contraction. The second-coordinate identity is postcomposed with the pulled-back
trace; the proved shuffle normalization gives exactly the specified second trace.
The first coordinate needs neither the line condition nor its identification e.
The second uses the existing `CoordinateTrace.evenLineSelfSymmetry` theorem.
The proper-support normalization is proved for general coefficient categories, then
specialized to modules. This avoids expensive kernel conversion through the
module-specific derived-category presentation. Only local unfolding controls are
used; no shared definition or interface was changed.

Added `SfSupportedFirstExtraction` and `SfSupportedSecondExtraction`. Each has one
remaining identity of canonical isomorphisms, stated before choosing any trace.
`extractionShuffle` is an explicit associator, symmetry and inverse tensor-pullback
comparison, defined for general coefficient categories whose inverse images preserve
flat objects. Module coefficients have the existing required instance. No arbitrary
data is chosen.
All proof imports of the item are private. Its existing public import and statement
are unchanged. Updated its node to follow the actual assembly.

Validation: the item compiled without warnings in 43.1 seconds using lcompile.py.
The first extraction compiled in 30.5 seconds and the second in 46.5 seconds.
The delivery tool performs the required final compile and preflight.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Etale.SupportedTrace.contractions`
(node `lem-sf-supported-trace-contractions`). The item has zero remaining holes.

Added two holes:

- `AlgebraicGeometry.Etale.SupportedTrace.firstExtraction`, node
  `lem-sf-supported-first-extraction`.
- `AlgebraicGeometry.Etale.SupportedTrace.secondExtraction`, node
  `lem-sf-supported-second-extraction`.

This is a decomposition, not a complete proof of the geometric comparison calculus:
one upper hole closed and two strictly separate pretrace identities added. The
proved private helpers are `swap_trace`, `shuffle_trace`, `proper_trace`,
`projection_iso_hom`, `ordinary_trace` and `supported_projection_trace`; they
contain no holes. No other existing module was
changed. The extraction obligations contain no scalar trace or diagonal datum;
they are the Kunneth and exchange/tensor stages of the argument, rather than either
of the original contractions under another name.

## No longer needed

No existing import was removed and no module is globally pruned. The inherited
public import `SfSupportedDiagonalData` still publicly imports the ordinary
coordinate contraction theorem, so this delivery does not claim to remove that
module from the library's import closure.

The item proof no longer applies `CoordinateTrace.contractions` (node
`lem-sfb-etale-coordinate-trace-contractions`). Its first-coordinate proof instead
uses the generic Kunneth identity with arbitrary B, while the ordinary theorem's
interface specializes B to a pullback. The new extraction nodes retain the needed
proper-base-change, projection/tensor composition, tensor symmetry and monoidal
comparison inputs. In particular, `lem-kun-proper-base-change-torsion-ring` is used by the first and
second extraction nodes, and `lem-sfb-ringed-projection-tensor-composition` is used
by the second extraction node. These two nodes are removed only from the parent's
direct proof dependencies. They are not claimed to be unnecessary globally.

## Where the brief, the DAG or earlier work was wrong

No statement correction. The old docstring describes a large transport of the
already-stated ordinary contractions. It does not supply equalities identifying
all the compact-support and ordinary canonical maps. Their mere invertibility is
insufficient to perform that transport by simplification. The delivery isolates
the trace-free Kunneth and exchange/tensor identities and proves the scalar
normalization and the complete assembly in Lean. The unit's route is unchanged.

For the new statements, checked f equal to the identity: the first identity reduces
to symmetry, and the second to reassociation with interchange of the two copies
of B. Its self-symmetry hypothesis is therefore essential to this argument. Empty
schemes and zero coefficients impose no excluded case. The coefficient L in the
second extraction need only have identity self-symmetry; the existing even-line
lemma provides exactly this property for the original theorem.

## New nodes

`lem-sf-supported-first-extraction`: the Kunneth coordinate interchange before a
trace, for arbitrary B and M. Its natural-language proof records the two mates,
proper support comparisons and cancellation of the invertible projection maps.

`lem-sf-supported-second-extraction`: the inverse exchange/projection square with
the two common coefficients extracted, before a trace. Its natural-language proof
specifies the self-symmetry cancellation and the explicit remaining shuffle.
Both inherit the item's chapter and unit. LeanSearch, Lean Finder and source grep
found no matching Mathlib theorem; the blueprint searches found no duplicate.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
