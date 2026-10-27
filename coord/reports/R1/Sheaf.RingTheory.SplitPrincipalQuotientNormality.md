## What changed

Proved `RingHom.split_principal_quotient_normality` in
`Sheaf.RingTheory.SplitPrincipalQuotientNormality` with its signature unchanged.
The quotient ring map is `Ideal.quotientMap`; its additive retraction is the
`QuotientAddGroup.lift` of the original retraction followed by quotient projection.
Principal-ideal contraction proves injectivity, and calculations on representatives
prove the splitting and quotient linearity.

A proved private helper implements the DAG's fraction-field argument once, then
applies it to both the quotient rings and the original rings. It pulls back the
domain structure, uses `IsFractionRing.lift` and `IsIntegral.map_of_comp_eq`, and
uses integral closedness in the larger fraction field. Applying the retraction
to the cleared-denominator equality shows that the integral fraction lies in the
smaller ring. The final cancellation takes place in the smaller fraction field.
The node's final proof step records this reuse instead of transporting through
zero-ideal quotients. No public definitions, signatures or instances changed.

## Proved and sorry left

Closed the one original hole: `RingHom.split_principal_quotient_normality`
(node `lem-trf-split-principal-quotient-normality`).
Added zero holes; split off zero statements. No `sorry` remains in the delivery.
The private helper `RingHom.normality_of_linear_retraction` is fully proved.

## No longer needed

Removed the proof imports `Mathlib.RingTheory.Localization.FractionRing`
(already publicly available through the integral-closedness import) and
`Mathlib.RingTheory.SimpleRing.Basic` (the proof cancels in the smaller fraction
field and does not use injectivity of a ring map out of a field).
Both public imports remain necessary for the statement.

No mathematical dependency node or project module is pruned. Both declared DAG
dependencies remain used: `lem-weil-pbc-fraction-field-lift` via its Mathlib
`IsFractionRing.lift` declaration, and `def-weil-pbc-normal-ring` via `IsDomain`,
`IsIntegrallyClosed`, and its elementwise fraction-field criterion.
The unit route is unchanged; this item does not realize a unit statement or step.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. Read Stacks `algebra.tex`,
`definition-domain-normal` (Tag 0309) and `lemma-descent-normal` (Tag 033G),
including the fractional-ideal argument. The retraction supplies precisely the
principal-ideal contraction supplied there by faithful flatness. Multiplicativity
of the retraction and flatness are never assumed.

Checked the argument for zero and unit parameters, zero divisors, trivial rings,
and additive retractions that are not multiplicative. The quotient construction
does not require domain hypotheses; normal-domain descent uses the stated
nontrivial domain hypothesis only in the larger ring. A unit parameter has a
trivial larger quotient, so its normal-domain implication has false antecedent.

Searches through `msearch.py` used LeanFinder (linear-retraction normality descent),
Loogle (`IsIntegral, RingHom`), and grep
(`IsIntegral.map_of_comp_eq|isIntegrallyClosed_iff`). LeanFinder returned relative
integral-closedness descent, whose extra hypothesis is not supplied by a linear
retraction. Loogle found `IsIntegral.map_of_comp_eq`, used in the proof. Local
searches of Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` found no existing
complete splitting-and-normality theorem for this statement.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
