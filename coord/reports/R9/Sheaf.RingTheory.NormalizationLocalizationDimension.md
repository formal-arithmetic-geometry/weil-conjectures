## What changed

Proved `IsUniversallyCatenary.ringKrullDim_localization_integralClosure_eq` in
`Sheaf.RingTheory.NormalizationLocalizationDimension`, with its signature unchanged.
The proof specializes the declared `height_add_trdeg_residueField_eq` dimension
formula. It constructs the canonical residue-field algebra and checks the scalar
tower explicitly. Finite modules and integrality make both transcendence degrees
zero. Mathlib's localization-height and local-maximal-height identities finish.

Added proof imports `Mathlib.RingTheory.AlgebraicIndependent.Transcendental` and
`Mathlib.RingTheory.Algebraic.Integral`. Updated the docstring and the node's proof,
proof dependencies and proof origin to describe the implementation. No definitions,
statements, public imports or consumer modules changed.

Validation: the complete proof compiled using lcompile.py. The argument includes
height zero and needs no positivity or finite-height cancellation. The residue map
uses precisely the supplied contraction equality; injectivity into the normalization
follows by composing with the given fraction-ring map.

## Proved and sorry left

Closed 1 of 1 original holes:
`IsUniversallyCatenary.ringKrullDim_localization_integralClosure_eq`
(node `lem-exc-weakly-etale-normalization-dimension`). Added 0 holes, split off 0
statements, and left 0 holes in this module. The existing imported dimension-formula
theorem `IsUniversallyCatenary.height_add_trdeg_residueField_eq` remains a dependency;
its proof is outside this item. This delivery proves the requested specialization
from that stated declaration, as required by stage 3.

## No longer needed

Removed proof imports `Mathlib.RingTheory.AlgebraicIndependent.Basic` (replaced by
its Transcendental extension), `Mathlib.RingTheory.FiniteType` (the existing public
imports already provide the finite-type instance), and `Mathlib.RingTheory.Ideal.Maximal`.

Pruned proof dependency `lem-weil-pbc-proper-ideal-contained-in-maximal`: the explicit
chain-appending and maximal-ideal-existence argument is replaced by Mathlib's
`IsLocalRing.maximalIdeal_height_eq_ringKrullDim`. No Sheaf module is withdrawn.
All other declared proof dependencies remain in use. There is no need to construct
or identify the fraction field of the normalization: its integrality already gives
zero transcendence degree.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The planned fraction-field identification and explicit
chain manipulations were unnecessary. Applying `trdeg_eq_zero` generically inside
simp caused expensive instance search; explicit zero-degree equalities compile
quickly. No statement or definition repair, forced adaptation, or new node was needed.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
