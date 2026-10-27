## What changed

Proved `WeilConjectures.PointSystemTransport.tensorTransition_existsUnique` by
specializing a fully proved arbitrary-automorphism construction in
`Sheaf.Paper.PointSystemTensorTransition`. The assigned module adds only a private
proof import and replaces this theorem's proof; its existing public signatures,
definitions, public imports, and file options are unchanged.

The construction identifies the completed-restricted reindexed system at each
level with its tensor-pullback model, then conjugates the original horizontal
transition by those isomorphisms. The inverted coefficient reduction square proves
the formula on scalar multiples of insertions. The comparison is invertible on
section carriers, so the formula at scalar one proves uniqueness. No condition
on the characteristic, normalization, boundedness, or the original transitions is
added. Identity automorphisms, exponent one, zero modules, and zero transitions
are covered by the same construction.

Three small proof modules isolate the ordinary finite comparison, scalar actions
on insertions, and the conjugated transition. This follows the profiler after the
combined proved file exceeded 60 seconds. All local definitions are actual
constructions and all helper theorems are proved. No profiling or timing-limit
options are delivered.

Validation: `lcompile.py --all` compiled all four delivered modules successfully
with no warnings. The checked sources contain no profiling options and exactly
one remaining `sorry`, the original `finite_evaluation`.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.PointSystemTransport.tensorTransition_existsUnique`, belonging
to `lem-trf-point-system-transport-descent`.

One original hole remains unchanged:
`WeilConjectures.PointSystemTransport.finite_evaluation`, belonging to
`lem-trf-point-system-transport-descent`. Its original statement, source, and full
proof docstring are retained.

All three new public theorems are fully proved:
`WeilConjectures.PointSystemTensorTransition.finite_tensor_comparison_iso_existsUnique`,
`WeilConjectures.PointSystemTensorTransition.tensor_insertion_smul`, and
`WeilConjectures.PointSystemTensorTransition.tensor_transition_existsUnique`.
All three new modules have zero holes. Added zero holes and split off zero
unproved statements; no previously proved declaration became a hole.

## No longer needed

The declared proof dependency
`lem-trf-automorphism-tensor-reduction-comparison` is removed from this node's
proof and proof dependencies. The direct construction uses the already available
finite comparison and finite-evaluation comparisons, so it does not need a
system-wide comparison of tensor sheafifications or that theorem's invertibility
hypothesis on the prime.

No existing Lean imports were removed and no modules were withdrawn. This removes
a dependency from the assigned proof; it does not claim that the automorphism
comparison module has no other consumers. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned automorphism tensor comparison requires an invertibility hypothesis
on the prime, while the assigned tensor-transition theorem has no such hypothesis.
The actual original transition can instead be conjugated through the finite
comparison, which is invertible for every scheme automorphism and finite level.
The statement needs no correction.

The small-complex argument used to establish ordinary component invertibility must
be indexed by integers; `CochainComplex.single₀` defaults to natural indices.
Explicit section carriers and underlying additive-presheaf maps avoid expanding
scalar-restriction structures during elaboration.

## New nodes

`lem-trf-point-system-tensor-transition`, realized by
`Sheaf.Paper.PointSystemTensorTransition`, states and proves the unique normalized
completed-linear tensor transition for an arbitrary point automorphism and any
strict coefficient system. This is a proved compilation split, with no new
unproved obligation. Its source is the tensor-transition step of the parent
argument and Stacks Tags 03CZ, 03EK, and 0941. No change record is needed because
no existing public interface changes.

`lem-trf-point-system-finite-tensor-comparison`, realized by
`Sheaf.Paper.PointSystemFiniteTensorComparison`, proves the ordinary finite
comparison isomorphism with its unique section normalization. It obtains ordinary
invertibility from the existing complex comparison on a single-term complex.
This is a proved compilation split; no unproved statement is added.

`lem-trf-point-system-tensor-insertion-scalars`, realized by
`Sheaf.Paper.PointSystemTensorInsertionScalars`, proves the inverse-coefficient
scalar formula for insertions using the original strict-system action. It proves
that evaluation's coefficient-ring cast acts identically on sections, then applies
linearity of the ordinary comparison. This is a proved compilation split; no
unproved statement is added. Neither additional module changes an existing public
interface, so no change record is required.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
