## What changed

Proved `WeilConjectures.CompactSupportRealizationFactorization.identityCoefficient`
in `Sheaf.Paper.CompactSupportRealizationIdentity`. A proof-only
`import all Sheaf.Paper.IntegralSupportNormalizationData` exposes the existing proved
private theorem `IntegralSupportNormalization.ringDirectImageId`. After that identity,
sectionwise functoriality and the inverse-hom identity finish the proof. Both explicit
unitor definitions, all signatures, and all public imports remain verbatim.

Updated the existing node's proof, proof dependencies and proof origin to record this
reuse. The identity calculation from `def-zl-ordinary-open-support-normalization` is
used solely as a proved tool; it does not replace any step of the purity-transport unit.
No other module is edited and no interface/change record is needed.

## Proved and sorry left

Closed 1 of 1 holes:
`WeilConjectures.CompactSupportRealizationFactorization.identityCoefficient`
(node `def-pur-compact-support-realization-identity`).

Zero holes remain in the item. Zero holes added; zero statements split off.
The existing `ordinaryPushId` and `integralPushId` constructions now use this proof.

## No longer needed

None. No imports, modules or nodes are withdrawn. The original node had no proof
dependencies; the finite-projection calculation is reused from its already proved
implementation rather than duplicated. The existing public bridge import remains
needed by the unitor signatures and definitions.

## Where the brief, the DAG or earlier work was wrong

The node's proof list was empty, but its docstring's finite-projection argument already
exists as proved private lemmas in `IntegralSupportNormalizationData`. Its
`ringDirectImageId` has precisely the completed coefficient datum required here.
LeanFinder returned only generic identities; Loogle did not resolve the specialized
pushforward-transformation name; Mathlib grep located generic pushforward unitors.
Project `rg` found the exact existing coefficient identity. No mathematical statement,
edge case or unit route needed correction: arbitrary schemes, including the empty
scheme, use the same inverse-hom equation.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
