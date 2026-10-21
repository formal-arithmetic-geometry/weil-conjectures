## What changed

Proved `AlgebraicGeometry.Etale.exceptional_domain_and_counit` and
`AlgebraicGeometry.Etale.exceptional_naturality_and_cocycle` in
`lean/Sheaf/Paper/ExceptionalCoefficientComparison.lean`. All existing public
signatures, definitions and public imports are unchanged. Added only a private
proof import of
`WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek`.

The domain proof constructs `HasInvertibleExponent` using the actual annihilator
`l^r`, then applies the source library's smooth preservation theorem. The counit
identity is the inverse/apply identity of the exceptional adjunction. Private
proved helpers package the existing compact-support components as a natural
isomorphism and identify the existing total inverse with its inverse components.
They introduce no new public coefficient comparison. Naturality is naturality of
the Mathlib mate. A private generic, pointwise mate-pasting calculation proves
the quotient cocycle after cancelling the assumed compact-support cocycle.
Both quotient associators remain in precisely their original directions.

Updated the proof plans, proof dependencies and proof origins of
`b3-exceptional-domain-counit` and `b3-exceptional-naturality-cocycle` to match.
The unit route is unchanged. No other module was adapted, and no source-library
interface was edited.

Validation: `lcompile.py` compiled the full file after both proofs were completed
(45.1 seconds with profiling enabled to investigate one earlier timeout).
Profiling has been removed from the delivered file; `deliver3.py` runs the final
clean compile and axiom/direct-hole probe. The arguments also cover empty schemes,
the zero complex and identity quotient indices; no cancellation of sections,
nonempty scheme hypothesis or flatness of the quotient map was introduced.

## Proved and sorry left

Closed two of the three original holes:

- `AlgebraicGeometry.Etale.exceptional_domain_and_counit`
  (`b3-exceptional-domain-counit`).
- `AlgebraicGeometry.Etale.exceptional_naturality_and_cocycle`
  (`b3-exceptional-naturality-cocycle`).

One original hole remains unchanged, as the whole proof of its named theorem:

- `AlgebraicGeometry.Etale.exceptional_tensor_and_base_change`
  (`b3-exceptional-tensor-base-change`).

Added zero holes and split off zero statements. The assembly theorem
`AlgebraicGeometry.Etale.exceptional_coefficient_comparison` keeps its existing
complete proof from the three intermediate results; its tensor and base-change
conclusions still depend on the remaining hole. This is a partial proof delivery
of a module with several original holes, not a claim that all six conclusions
are now axiom-free.

## No longer needed

Removed `lem-pur-finite-reduction-constructibility` from the domain/counit node's
proof dependencies. The direct ordinary-etale smooth preservation theorem already
supplies its domain assertion, so this proof needs neither a pro-etale origin
choice nor finite-reduction constructibility. The existing public import of
`Sheaf.Paper.FiniteReductionConstructibility` is preserved; the delivery makes no
claim that its module is globally pruned.

No Lean imports or modules were removed. No new proof-dependency import was
added for any unused planned lemma. The proper coefficient-extension input,
smooth tensor input and ambient exceptional adjunction remain needed. The
naturality/cocycle node now explicitly records its use of domain preservation to
apply `hb` at the exceptional image.

## Where the brief, the DAG or earlier work was wrong

The former domain/counit proof plan unnecessarily routed its domain calculation
through finite reduction. The source library already proves smooth preservation
using exactly the flat rank-one line argument required here.

For the remaining hole, the three currently declared proof dependencies supply
proper projection isomorphisms, compact-support exchange and geometric smooth
base change, but do not themselves state the mixed scalar compatibility
identities for the particular `tensorIso`, `scalarPullbackIso` and
`compactSupportMap` used here. The tensor part has a relevant stronger declared
input, `etaleCompactScalarCoherence` in
`Sheaf.Paper.EtaleCompactScalarCoherence`; that module publicly imports this item,
so importing it back would create a cycle. It is held by E3 in the claim snapshot
read during this session. I did not change that group's module or replace the
remaining theorem with a renamed copy or with additional holes. The remaining
work is the actual compact-support scalar/projection square and the mixed
scalar/geometric exchange square, followed by their exceptional-adjunction
transposes, as described in the existing docstring and node source.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
