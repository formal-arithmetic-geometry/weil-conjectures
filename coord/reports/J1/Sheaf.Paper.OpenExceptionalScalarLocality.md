## What changed

Filled `AlgebraicGeometry.ProEtale.OpenScalarLocality.openExceptionalScalarLocality`
from the two declared proof dependencies, preserving every existing statement and
definition. Added private proved helpers for counit transport through exact
localization, full-subcategory restriction, the identity compactification refinement,
and the final categorical cancellation. Added private proof imports and file-local
elaboration controls only. The controls keep derived scalar and adjunction constructions
folded during categorical calculations; they change no exported construction. Updated
the item node's proof to record the coordinate transport and the clauses used.

Validation: the complete module compiled through `lcompile.py` without errors or
warnings in 47.2 seconds. The original theorem signature and existing definition
bodies were checked unchanged; the module contains zero `sorry`s.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.OpenScalarLocality.openExceptionalScalarLocality`:
1 of 1 holes closed. No holes added or split off. No `sorry` remains in this module.
The two existing proof-dependency theorems remain used as stated; this packet does
not claim their proofs or an axiom-free transitive target closure.

## No longer needed

None of the declared dependency modules is pruned. The proof uses the open-counit
clause of `openScalarRestrictedTransposeExpansion` and the coefficient-composition
square clause of `openScalarInverseTransposeFactorization`; their other clauses
need not be unfolded or reproved here. No public import was removed.

## Where the brief, the DAG or earlier work was wrong

The two dependencies and this module use different pullback coordinates: intrinsic
realization pullback versus canonical constant-ring pullback. Their adjunction
counits are therefore not definitionally identical. The proof explicitly transports
them along `openSquareDerivedPullbackModel` and `reductionOpenModel`, using the
standard localization factors. The inverse-factorization comparison also contains
a self-refinement, whose identity is proved from its normalization and uniqueness.
These are interface bridges, without statement or definition repairs. The original
module exists live and its quarantined copy is preserved; neither is withdrawn.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
