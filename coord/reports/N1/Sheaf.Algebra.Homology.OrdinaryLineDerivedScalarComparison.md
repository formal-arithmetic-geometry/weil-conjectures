## What changed

Proved `SheafOfModules.OrdinaryLineScalar.comparison_identity` without changing
its statement, any definition, or any import. Specialize the recorded arbitrary
identity-ring comparison to identity signed-power maps. The resulting cochain map
is identity in each degree. Cancel the comparison factors and scalar unitor,
then use `Localization.natTrans_ext` for the cochain quasi-isomorphism localization.
Updated the existing node's final proof step and proof origin to record this route.

## Proved and sorry left

Closed one of the five original holes:
`SheafOfModules.OrdinaryLineScalar.comparison_identity`.
No holes added and no statements split off.
The already proved `exists_presentations` remains proved.

Four original holes remain, all attached to
`lem-pur-ordinary-line-derived-scalar-comparison`:

- `SheafOfModules.OrdinaryLineScalar.exists_lineData`.
- `SheafOfModules.OrdinaryLineScalar.ordinary_line_derived_scalar_comparison`.
- `SheafOfModules.OrdinaryLineScalar.comparison_tower`.
- `SheafOfModules.OrdinaryLineScalar.comparison_identity_arbitrary`.

The proof compiles cleanly through the prescribed remote compiler
(35.4 seconds). It depends on the existing arbitrary-comparison theorem, which
remains an original named hole; this delivery is a partial proof, not a claim
that the whole comparison module is closed.

## No longer needed

None. No import, module, declaration or node is withdrawn. The remaining clauses
still need the existing planned dependencies. The identity clause itself needs
only `comparison_identity_arbitrary`, identity cochain maps, and localization
extensionality, rather than a second pure-tensor computation.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The final multiplication identity does not need a new
chain-level calculation once the more general identity-ring comparison is stated.
The proof uses its original hypotheses without requiring boundedness, completeness,
flat coefficient maps, a nonzero ring, or positive signed exponents.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
