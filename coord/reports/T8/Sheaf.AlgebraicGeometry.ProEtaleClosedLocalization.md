## What changed

Proved `AlgebraicGeometry.ProEtale.proEtale_closed_localization` without changing its
signature. The direct-image comparison is the existing weakly etale base-change
map, whose section formula is exactly the specified pullback-comparison restriction.
Constructed the inverse-image isomorphism by conjugating `squareLowerStarIso` under
the composite adjunctions. Mathlib's iterated-mates identity identifies its mate with
the direct-image comparison. `unit_mateEquiv` and `mateEquiv_counit`, followed by the
two inverse laws, prove the required unit and counit equations.

Added a private proof import of
`WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale`. Replaced the unused
public finite-coefficient direct-image import with the concrete coefficient instances
needed for the statement. Updated the node's proof, proof dependencies and proof
origin to this route. The unit's `realized` record has no statement or step assigned
to this node; no unit statement or unit route was changed.

Change record: `coord/changes/T8-proetale-closed-localization-imports.md`.

Validation on this continuation: the required dry run passed compilation and
preflight (commit `f777678914`, review class CODEX). A separate server compile
of the final module passed in 53.4 seconds with no warnings or errors. Its theorem
signature matches the current source verbatim. Only the node's proof, proof
dependencies, proof origin, and obsolete tool-use list differ. All Lean lines meet
the 100-character limit. The declaration docstring now describes the actual mates
proof rather than the discarded comma-colimit plan. No axioms or holes are added.

The retained consumer checks passed for both direct importers, and their source
files still match the current repository. A fresh source import inventory found
505 transitive consumers and the same two direct private importers. The change
record covers this inventory, including the newly found
`Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology`. No consumer adaptation
is required. No checking tool was changed.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.ProEtale.proEtale_closed_localization`
(node `lem-exc-closed-localization`). No holes added, no split-offs, and no `sorry`
left in the delivered Lean module. This is a proof, not a decomposition.

## No longer needed

Removed import `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`.
Its finite continuous-function coefficient sheaves, realization equivalences and
derived direct-image construction do not occur in this fixed-ring underived theorem.
This reports an unused dependency of this item, not a claim that every module below
that import is absent from the targets' full closure.

The actual proof does not use `def-weil-proetale-inverse-image`
(`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`) or
`lem-weil-pbc-proetale-restriction-injectives`
(`Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives`). Both modules are now
proof imports in the current baseline; removed these unused imports, their planned
proof-dependency edges, and the obsolete
`tool_uses` entry for restriction-injectives. The explicit source-library restriction
adjunction and base-change comparison supply everything needed; no injective,
derived-evaluation, or comma-colimit computation is needed.

Also removed the unused proof import
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`, inserted in the current
baseline for `def-weil-pbc-proetale-operations`. The source-library closed adjunction
already supplies the fixed-ring adjunction used in this statement; the arbitrary
ring-sheaf and derived operations of that module are not used. The node retains
`def-weil-pbc-proetale-operations` as the conceptual adjunction dependency.

No modules are withdrawn. No other dependency edge is removed.

## Where the brief, the DAG or earlier work was wrong

The planned comma-colimit construction is unnecessary for the published statement:
the source library already gives the correctly normalized direct-image comparison
and its mate. Double mates and adjoint conjugation construct the inverse-image
comparison and prove both compatibilities. The original statement is true, including
the zero ring and empty scheme, with no finiteness restriction. The construction in
fact does not use the closed-immersion hypothesis, which is retained verbatim.

Searches performed through msearch: LeanFinder for restriction commuting with direct
and inverse image returned scheme-module restriction adjunctions, with no exact
match; Loogle on `CategoryTheory.mateEquiv`
returned the unit, counit, and iterated-mates identities; grep on
`localizationRestrictionBaseChangeMap|conjugateIsoEquiv` returned the categorical
conjugation API. Repository search found the existing pro-etale weakly etale
base-change module. Its import direction is allowed. No new statements or nodes
were needed.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
