## What changed

Implemented `exists_ring_left_refinement` by two geometric steps and an explicit
categorical calculation. The inverse proper compositor and proper pushforward of
the inverse open-unit comparison form `ringRefinementWord`. Conjugating it by
`R.left` and lifting through the fully faithful ring-stage inclusions constructs
the required natural isomorphisms. The generic constructor
`properOpenRefinementWord` supplies the explicit objectwise isomorphisms and proves
their naturality. This avoids nested associator terms in the coefficient construction.
No shared definition or exported attribute changes. A proved private helper reflects shift
compatibility through a faithful shift-compatible functor. Cancellation of the
realization isomorphisms proves `RingRefinementNormalized`.

For the integral scalar square, the proof applies the ordinary scalar-word square
to the scalar object already supplied by R. Its scalar realization identifies that
object with ordinary scalar extension. Mapping into the ordinary category, the
proof uses scalar-realization naturality, the two `R.comparison_normalized`
equations, the formula for the lifted refinement, and inverse identities. It does
not require a new scalar-extension object or an absolute separatedness hypothesis.

Added `Sheaf.Paper.RingOpenRefinement` (explicit word and open-unit geometric step)
and `Sheaf.Paper.RingRefinementScalarWord` (scalar naturality of that ordinary word).
The assigned module imports the latter privately. Both new geometric theorems
have full source-based proof descriptions and corresponding nodes.

Validation: the remote `lcompile.py --all` run compiled all three modules. The original
nested associator construction timed out; after the componentwise construction,
the profiler recorded 3.86 seconds of type checking for the parent. Temporary
profiling settings and the diagnostic trace were removed before delivery.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_ring_left_refinement`.

Added two strictly smaller named holes:

- `WeilConjectures.ConstructibleExceptionalCoefficients.exists_ring_open_refinement`:
  the natural open-unit comparison on the intermediate scheme d.Z, with its
  normalization and the shift equation of its proper pushforward word.
- `WeilConjectures.ConstructibleExceptionalCoefficients.ring_refinement_scalar_word`:
  scalar naturality of the supplied ordinary word, before any chosen exceptional
  operations or scalar realizations are used.

This is a decomposition: one original hole closed and two smaller holes added,
net minus one. The full-subcategory lift, faithful shift reflection, normalization,
and conjugation of the ordinary scalar square into the required exceptional
scalar square are complete Lean proofs with no further holes. No data definition
contains a sorry or chooses data from the new existence theorem. Its witness is
eliminated only inside the proof of the original proposition.

## No longer needed

No original public import was removed, and no existing module is withdrawn.
The assigned node's direct proof dependencies are now the two new geometric steps.
The finite-operations, compactification-coherence, coefficient-site mate,
integral-system realization, system-transport and diagram open/clopen shift
steps are retained below `lem-sf-ring-open-refinement`. The system proper/open
scalar square and integral-system realization are retained below
`lem-sf-ring-refinement-scalar-word`.

The original direct dependencies `lem-sf-exceptional-integral-reconstruction`,
`lem-pur-integral-realization-shift-coherence` and
`lem-sf-exceptional-integral-scalar-mates` are not used: the new steps work with
the normalized ordinary open/proper word and its primitive system realization,
not the entire chosen exceptional-operation or Weil-shift packages. Their modules
were never imported by the assigned module. This prunes proof-plan edges; it does
not claim these modules leave the targets' global import closure.

## Where the brief, the DAG or earlier work was wrong

The first attempted shortcut used `PurCompactSupport.refinementProperOpen_existsUnique`
and `comparison_refinement`. Compilation showed that these existing declarations
require absolute separatedness of X and Y. The assigned theorem assumes only
relative separatedness of f, which does not imply those hypotheses. The delivered
proof therefore does not use that shortcut or strengthen the assigned statement.

The original dependency plan has circular paths from exceptional integral
reconstruction and integral realization shift coherence through Weil-shift data
back to the assigned node. The new geometric steps use primitive ordinary
open/proper operations and their system realization instead of those packages.

The splits are distinct parts of the source argument. The first concerns the
open-unit map over d.Z before the outer proper pushforward and lift to R.operation;
it has no chosen exceptional operations or scalar-extension conclusion. The second
is an equality for a supplied ordinary word, with no existential refinement family,
shift conclusion or exceptional-operation data. The parent supplies the actual
lift and combines these steps through a nontrivial normalization calculation.

## New nodes

- `lem-sf-ring-open-refinement`: natural normalized open-unit comparisons at finite
  and integral stages, with shift compatibility of the explicit word.
- `lem-sf-ring-refinement-scalar-word`: scalar naturality of that ordinary word,
  including transport of the scalar target vertex by a supplied isomorphism.

Both nodes retain the original sources, relative scheme hypotheses, finite-Tor
input domain and complete proof plans. Identity refinements, zero objects and
identity coefficient extensions use the same canonical maps. System equalities
are established before total-limit realization, never inferred from evaluations.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
