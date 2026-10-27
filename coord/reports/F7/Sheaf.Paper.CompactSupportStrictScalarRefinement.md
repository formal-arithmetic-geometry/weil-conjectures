## What changed

Completed `WeilConjectures.PurStrictScalar.compactSupportStrictScalarRefinementCoherence`
in `Sheaf.Paper.CompactSupportStrictScalarRefinement`, following Steps 9--11 of
`lem-pur-compact-support-strict-scalar-refinement`.

The common-refinement scalar square follows by cancellation from the two
single-refinement squares of `compactSupportStrictScalarRefinement`. Parallel
refinements give equal isomorphisms after equalizing them and cancelling the
invertible further-refinement map. Common domination then proves independence
of the two refinement legs; a common domination and cancellation of the middle
isomorphism prove the cocycle. Finally the total-limit square is conjugated by
the prescribed `scalarSupportLimit` isomorphisms, giving exactly the canonical
integral-support square.

Added a private proof import of
`WeilConjectures.Compactification.Cofiltered` for its cofiltered-or-empty
instance. The helpers are private and proved. Public statements, definitions,
existing docstrings and the unit route are unchanged. Local irreducibility
attributes keep large support and limit constructions folded during proof
elaboration. Private, proved equations expose only the hom maps of the common
and integral comparisons, so the final proof rewrites by these equations instead
of unfolding the underlying derived constructions. No other module is edited.

Validation: the complete module compiled in 20.7 seconds with all four clauses
of the coherence theorem proved. Profiling options and diagnostic tactics were
removed before delivery.

## Proved and sorry left

Closed 1 of the 5 original holes:
`WeilConjectures.PurStrictScalar.compactSupportStrictScalarRefinementCoherence`.
Added 0 holes; split off 0 statements. This is a proof from existing declarations,
including the still-unproved `compactSupportStrictScalarRefinement`, rather than
a decomposition into new assumptions.

The 4 remaining original holes, all attached to
`lem-pur-compact-support-strict-scalar-refinement`, are:

- `WeilConjectures.PurStrictScalar.scalar_clopen_projection`
- `WeilConjectures.PurStrictScalar.scalar_properOpen_alpha`
- `WeilConjectures.PurStrictScalar.scalar_compactification_composition`
- `WeilConjectures.PurStrictScalar.compactSupportStrictScalarRefinement`

## No longer needed

None. No existing import is removed, and no node or module is withdrawn.
The prospective dependencies of the four unfinished clauses stay needed.
The completed coherence proof uses the existing normalized refinement equations
and the existing scalar squares; it does not need a separate Roos-coordinate
calculation because `scalarLimitArrow` already contains those prescribed maps.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. Mathlib search found generic isomorphism
cancellation lemmas, while the repository already supplies the required
cofiltered compactification category and normalized refinement equations.
The existing node's common-domination, cancellation and conjugation plan is
realized directly; no route or node update is necessary. Uncontrolled unfolding
of the support and limit constructions exceeded the compile limit; keeping
those constructions locally irreducible and rewriting by their proved hom-map
equations avoids that normalization cost.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
