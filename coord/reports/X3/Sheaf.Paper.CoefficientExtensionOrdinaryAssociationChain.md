## What changed

Implemented `WeilConjectures.coefficientExtensionOrdinaryAssociationChain` with its
original signature. Its finite comparisons are the explicit composite of rho,
finite scalar extension of `M.evaluation`, balanced association, and inverse
`directEvaluation`. The proof derives their successor squares from the source
and direct tensor formulas, then constructs the ordinary natural isomorphism.

The private gluing helpers prove compatibility for every n <= m by induction,
factor arbitrary product-site arrows into horizontal and vertical arrows,
construct the actual inverse module maps on each object, and lift the presheaf
isomorphism through the fully faithful sheaf-module forgetful functor. They
check the differentials and naturality by finite evaluation. The generic
product-site construction adapts the proved private helpers of
`Sheaf.Paper.TransportedReductionPullbackNormalized`, adding successor
induction. The final evaluation equation follows by
cancelling `directEvaluation` and projecting the explicit composite degreewise.

Added the new proof import `Sheaf.Paper.CoefficientExtensionAssociationSuccessor`.
The existing public imports are retained. Updated the assigned node's proof and
proof dependencies to match this construction.

Both modules compiled through `lcompile.py` within the 60-second per-file limit.
The complete parent compiled in 42.9 seconds with profiling enabled; those debug
options have been removed for delivery. The original theorem signature was also
compared verbatim with the shared source. Each Lean line is at most 100 characters.

## Proved and sorry left

This is a decomposition: one upper hole is replaced by one strictly smaller
successor calculation, for a net change of zero holes.

- Closed the original proof body of
  `WeilConjectures.coefficientExtensionOrdinaryAssociationChain`
  (`stage3-pur-extension-ordinary-association-chain`). Its proof contains no sorry.
- Added one whole named theorem hole:
  `WeilConjectures.coefficientExtensionAssociation_successor`
  (`stage3-pur-extension-association-successor`). This is the concrete local tensor
  transition calculation for the source model. It applies to arbitrary complexes
  and contains no `direct` functor, `directEvaluation`, good-complex condition,
  existential comparison, cochain gluing, or input-naturality conclusion.

All private helpers are proved. No other existing module is changed.

## No longer needed

No original public import was removed, and no module is claimed pruned.

The parent no longer directly uses `lem-pur-system-scalar-generators` or
`lem-pur-system-scalar-coherence`; those two dependencies belong to the remaining
source successor calculation and are recorded on its new node. The declared
dependency `lem-pur-system-ringed-sequence-site` is not needed: direct presheaf
gluing avoids the strict-system equivalence and its import. The parent retains
`def-coef-ringed-sequence-site` for the actual finite-transition section formulas.
These are dependency-edge reductions, not withdrawals of those shared modules.

## Where the brief, the DAG or earlier work was wrong

The original node's first step required a concrete normalized successor identity
beyond the signatures of its named generic scalar-generator and coherence
lemmas. The new node states that calculation precisely. The rest of the original
plan is implemented in Lean, including all-level compatibility, inverse maps,
differential squares, naturality, and the exact finite evaluation equation.
The unit route and the assigned theorem's signature are unchanged.

The new statement was checked on zero terms, n=0, arbitrary cochain degrees,
empty sites and ramified inclusions. Its argument is termwise and uses no
flatness or derived comparison.

## New nodes

`stage3-pur-extension-association-successor`, in
`lean/Sheaf/Paper/CoefficientExtensionAssociationSuccessor.lean`, isolates the
local tensor calculation of the parent's first proof step. Its source is Stacks
03D7 and 03EK, together with the sequence-site construction preceding 0941.
Its docstring and node give the generator argument and its normalization data.
LeanSearch, LeanFinder, Loogle and project/Mathlib text searches found the generic
scalar and gluing APIs, but no theorem giving this concrete successor formula.
The node inherits the parent's chapter, unit and blueprint ancestry. There is
no existing interface change requiring a change record.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
