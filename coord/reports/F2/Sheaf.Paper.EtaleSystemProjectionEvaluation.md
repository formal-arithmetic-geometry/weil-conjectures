## What changed

Replaced the hole in `Sheaf.Paper.EtaleSystemProjectionEvaluation` with the scalar
adjunction calculation. The signature and its original docstring are unchanged.
The proof reuses the already proved `etaleSingleCoefficientProjection`: its
canonical restriction isomorphism and transpose formula identify the single-ring
mate. `ScalarEvaluation.mate` and the definition of `projection` identify the
other three mates. `mateEquiv_app_cube_converse` transports the restriction cube
to the scalar cube; postcomposition and inverse cancellation give the original
five-factor equation.

Added `Sheaf.Paper.EtaleSystemRestrictionEvaluation` for the remaining restriction
comparison. It compares actual restriction/evaluation words on C-coefficient
systems, independently of `q`, scalar-extension units and `compactScalarMap`.
This is the restriction-evaluation step of the original proof, rather than the
original scalar projection equation under another name. The single-ring
proper/open normalization and the scalar-adjunction assembly are discharged in
the item. The remaining theorem has its source and a proof in words, and a new
DAG node. Updated the item's proof route to match the Lean argument. All added
imports of the item are private proof imports; its public import is preserved.

Validation: `lcompile.py --all` typechecked both modules. Temporary profiling
showed 140 ms elaboration for the restriction statement, about 2 s of tactic
execution for the main proof and 200 ms of type checking for that proof. The
profiler settings were removed before delivery; the delivery tool checks the
final files and their axiom/sorry probes.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Etale.SystemProjection.etaleSystemProjection_evaluation`
(`lem-pur-etale-system-projection-evaluation`). Its complete proof uses the
following new, strictly intermediate restriction-evaluation statement.

Added one hole:
`AlgebraicGeometry.Etale.SystemProjection.etaleSystemRestriction_evaluation`
(`lem-pur-etale-system-restriction-evaluation`) in
`Sheaf.Paper.EtaleSystemRestrictionEvaluation`.

This is a decomposition: one upper hole closed and one lower hole added, net
zero holes. There are no holes left in the assigned module and one in the new
module. No definition contains a hole; no axiom declarations or data definitions were added.

## No longer needed

No original Lean import was removed: the sole original public import
`Sheaf.Paper.EtaleSystemProjectionData` is needed by the statement.

The item's direct proof dependencies no longer include
`lem-coef-semilinear-derived-sections`, `lem-coef-etale-open-tensor`, or
`lem-pur-ringed-coefficient-restriction-counit`. The scalar calculation uses the
already proved single-ring theorem and the generic cube of mates instead of
instantiating those larger calculus/presentation interfaces. The residual
restriction-evaluation lemma uses ordinary section normalization, exact cube
localization, the canonical restriction maps and mate identities. The generic
mate dependency `def-weil-pbc-adjunction-mate` remains. These are dependency-edge
prunings only; the statement data and other consumers may still need the listed
modules, so no whole-library module withdrawal is claimed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original plan combined the actual restriction
comparison and the scalar-adjunction assembly into one step. The already proved
`etaleSingleCoefficientProjection` supplies the latter's single-ring input and
was absent from the item's old dependency list. Its normalization permits a
shorter assembly using the converse cube theorem directly, without constructing
another scalar adjunction evaluation calculus.

The remaining cube has been checked for typing and orientation: its input N is
a C-system, its equation is in the B_n category, and hd fixes d to the published
forward restriction comparison. Thus d is not a freely chosen comparison.
Identity coefficient maps, zero modules, zero rings and exponent-zero torsion
are included. The proof uses no division, nonzero-rank assumption, flatness,
boundedness, completeness or faithfulness of derived evaluation. The unit's
route is unchanged (its realized statement and step lists are empty).

## New nodes

`lem-pur-etale-system-restriction-evaluation` records the ordinary
restriction/evaluation compatibility for compact support, with the precise
inverse-cube equation in its Lean attachment. Its proof first compares ordinary
section maps, takes geometric inverse-image mates, localizes exact comparisons,
and takes proper/open mates before pasting. It is strictly the restriction
portion of the original argument. Mathlib searches with LeanSearch, LeanFinder,
Loogle and grep found generic mate/localization tools but no direct theorem for
these normalized system and single-ring operations. No existing interface was
changed, so no change record or consumer adaptation is needed.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
