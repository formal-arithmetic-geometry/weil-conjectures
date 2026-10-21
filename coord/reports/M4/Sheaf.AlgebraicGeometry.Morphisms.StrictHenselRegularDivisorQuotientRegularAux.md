## What changed

Retired the listed zero-hole duplicate
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux`.
Its mathematical node now points to the proved upstream theorem with the same name,
which uses the full affine-neighbourhood colimit. No upstream file was edited.

Adapted its sole direct consumer,
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart`,
without changing its theorem signature, visibility or existing docstring. The proof
identifies the small and full colimits and their structural maps, applies the upstream
auxiliary theorem, and transports regularity across the induced principal-quotient
ring equivalence using Mathlib `IsRegularRing.of_ringEquiv`. Its only added helper is
private and proved. The structural-map public import uses its upstream owner to avoid
a duplicate declaration. The consumer is unclaimed; no other group's module is changed.

Updated the auxiliary node's Lean attachment and proof, and the consumer node's actual
proof dependencies and transport argument. Expanded the auxiliary node's contextual
statement with its existing hypotheses and replaced its parent-as-statement-dependency
with its definition dependencies, preventing a false circular dependency. Change record:
`coord/changes/M4-retire-strict-hensel-regular-divisor-quotient-aux.md`.

## Proved and sorry left

Zero holes before; zero holes after. Holes closed: none. Holes added: none. Split off: none.
The retired theorem
`AlgebraicGeometry.Scheme.strictHenselizationRing_divisor_quotient_noetherian_and_local_regular`
is already proved in the retained upstream module. The adapted
`AlgebraicGeometry.Scheme.strictHenselizationRing_regular_divisor_quotient_part`
is completely proved, as is its private `comparison_base` helper. No declaration in
the delivery contains `sorry`; this delivery completes a retirement, not a new hole closure.

The adapted consumer compiles without warnings in 3.9 seconds. A counterfactual check
with the withdrawn item replaced by `module` confirms that the original consumer fails
at line 35 with `Unknown identifier strictHenselizationRing_divisor_quotient_noetherian_and_local_regular`.
All twelve downstream modules compiled as single files against the adapted sandbox
consumer and withdrawn stub (2.5–15.4 seconds each; adapted consumer 6.1 seconds in
this set). The upstream auxiliary and adapted consumer axiom probes each report
exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Pruned module:
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux`.
Removed its sole consumer import and replaced it with
`WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux`.
Also replaced the consumer's public import of
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap` with its upstream owner.
This does not withdraw the structural-map module, which has other consumers.

The retired file's imports of `StrictHenselDivisorQuotientPresentation`,
`StrictHenselizationRegular`, and `RegularLocalLocalization` are supplied inside the
retained upstream proof; none of their mathematical nodes is pruned. All three
auxiliary dependencies remain needed. The retired file's public imports of the
upstream structural-map module and `Mathlib.RingTheory.RegularLocalRing.Defs` remain
needed by the consumer. The parent's auxiliary edge is retained explicitly
in the DAG, including the unfinished-parent case. No unit statement or step is bypassed,
no source-library declaration is removed, and no additional module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief names an item that currently has no holes. Its current
`coord/retire-items.tsv` row supplies the concrete work: retire a proved duplicate.
The two theorem signatures are not definitionally identical: small versus full colimit
rings and their canonical structural maps require actual transport. A direct import
replacement alone would not repair the consumer. The parent's earlier proof record
also omitted the auxiliary theorem its Lean proof actually used; it now records that
edge and the transport. The auxiliary node’s contextual statement is expanded with the same hypotheses,
and its mistaken parent-as-statement-dependency is replaced by the actual definitions.
This prevents a false cycle when recording the parent’s real auxiliary proof edge.
The mathematical content is unchanged; no base node cites the auxiliary in its
statement or proof dependency list, so the statement-clarification citer list is empty.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
