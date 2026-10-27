## What changed

Proved the equal-level quotient identity `compactSupportQuotient_self` and the
successive quotient identity `compactSupportQuotient_comp` using
`Ideal.Quotient.factor_eq` and `Ideal.Quotient.factor_comp`.
Added local irreducibility attributes for `HasDerivedCategory.standard`,
`SheafOfModules.monoidalCategory`, and the completed coefficient sheaf. Profiling
identified 34.7 seconds of kernel checking in `CompactSupportQuotientModuleSpec`;
these local attributes prevent unfolding the large category and coefficient
constructions while checking the section formulas. The quotient definitions and
all declaration signatures are unchanged.

## Proved and sorry left

Closed 2 of the 4 original holes: `WeilConjectures.compactSupportQuotient_self`
and `WeilConjectures.compactSupportQuotient_comp`. Added zero holes.
Two original holes remain: `WeilConjectures.compactSupportQuotient_representatives`
and `WeilConjectures.compactSupport_quotient_cocycle`, both attached to
`lem-coef-compact-support-quotient-cocycle`. Their original source citations and
complete natural-language proof plans are retained.

## No longer needed

None. No imports, modules or DAG dependencies were removed. The quotient identities
implement the quotient calculation in the existing proof plan; the representative
and compact-support arguments remain needed for the two remaining theorems.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped before Lean started because temporary storage was full.
This session's initial delivery check reached Lean and exposed unverified errors in
its exploratory adjunction normalization helpers. Those helpers are preserved in the
sandbox scratchpad, outside the delivery. The packet retains only the completed
quotient proofs; no mathematical statement correction was needed.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
