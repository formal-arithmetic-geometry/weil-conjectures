## What changed

Proved `Module.injective_flat_cokernel_of_localized_directed_limit` in
`Sheaf.RingTheory.LocalizedArrowInjectiveFlatCokernelLimit` without changing its statement.
The proof follows the existing three-step DAG plan: detect a kernel representative at a
later injective stage; use Mathlib's algebra-linear tensor quotient equivalence and
`LinearMap.lTensor_range` to identify the canonical cokernels; apply
`Module.flat_quotient_localized_baseChange` with the zero ideal and transport flatness.
A proved private helper removes the zero-ideal quotient tensor from the flatness conclusion.
No definitions or public interfaces were changed. The unused-variable linter is disabled
only for the existing theorem, whose redundant contextual hypotheses are preserved verbatim.

The canonical comparison is constructed at every index, including indices before the
eventual tail. Its pure-tensor formula follows from `h_beta` and linearity of the quotient
map. The argument uses no nontriviality, finiteness, locality or Noetherianity assumptions,
and covers zero rings/modules and a singleton index set.

## Proved and sorry left

Closed the one existing hole:
`Module.injective_flat_cokernel_of_localized_directed_limit`
(node `lem-trf-localized-arrow-injective-flat-cokernel-limit`).
Added zero holes; zero holes remain in the delivered module. The private helper is proved.

## No longer needed

None. Both existing proof imports are used: Mathlib tensor right exactness provides
`LinearMap.lTensor_range`, and the localized base change quotient flatness module provides
the flatness theorem. The original DAG proof dependencies and the unit route are retained.
No modules or nodes are withdrawn.

## Where the brief, the DAG or earlier work was wrong

None. The existing plan is implemented using the stronger algebra-linear form of
Mathlib's tensor quotient equivalence, avoiding a manual construction of inverse maps.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
