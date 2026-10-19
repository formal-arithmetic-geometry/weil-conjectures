## What changed

Proved `integralExceptionalRestriction` with its original signature and definitions.
The proof identifies Dctf with Dbc, chooses a finite affine open cover, proves
constructibility on each chart, uses only clause (1) of `integralRestrictionGlue`,
and restricts the actual Brown adjunction through explicit natural Hom equivalences.

Retained and rechecked both completed chart lemmas from the earlier sandbox attempt. `integralExceptionalAffineFactorization`
constructs the finite polynomial presentation using the existing source-library affine-space
criterion, obtains Brown adjoints for the affine projection and closed immersion, restricts
the actual open adjunctions, and compares the composite right adjoints using compact-support
composition and `Adjunction.rightAdjointUniq`. `integralExceptionalAffineChart` combines
pullback preservation with the existing integral affine-space and closed-immersion theorems.
Private proved helpers establish isomorphism invariance of finite constant models directly.

All three sandbox modules compile cleanly through `lcompile.py --all` against the current
library, rechecked in this resumed session on 2026-10-19. No signatures, definitions or
visibility of existing declarations changed. No change record or consumer adaptation is needed.

## Proved and sorry left

Closed 1 of 1 original holes: `integralExceptionalRestriction`
(`sk-thm-int-restriction`). Added 0 holes; split off 0 unproved obligations.
Both `integralExceptionalAffineChart` (`lem-sfb-integral-exceptional-affine-chart`) and
`integralExceptionalAffineFactorization`
(`lem-sfb-integral-exceptional-affine-factorization`) are proved. There is no `sorry`
in any delivered Lean file. Existing imported theorem holes remain their existing items.
This is a proof from the stated dependencies, rather than a decomposition with new holes.

## No longer needed

Removed the item's direct imports `Sheaf.Paper.MateOpenRestriction`,
`Sheaf.SixFunctors.IntegralRestrictionLine`, `Sheaf.SixFunctors.IntegralRestrictionClosed`,
and `Sheaf.SixFunctors.IntegralTensorInverseImage`, replacing them with the proved
`IntegralExceptionalAffineChart` module. The affine-space and closed-immersion results are
used in the chart proof; the open comparison definition is used in the factorization proof.
The compact-support construction's `constructible_pull` clause supplies pullback preservation,
so the chart needs no direct tensor theorem import. The unit's geometric route is retained.
Removed the main file's redundant direct Mathlib imports `Morphisms.FiniteType` and
`Morphisms.ClosedImmersion`; the geometry remains available through other imports.
Removed unused line, closed and tensor imports from the new factorization module, and
unused mate and tensor imports from the chart module. No existing module or node is claimed
to leave the targets' import closure. No mathematical node is retired.

The old direct proof dependencies `lem-weil-pbc-qcqs-over-affine`,
`lem-weil-pbc-affine-scheme-qcqs`, and `lem-weil-pbc-qcqs-morphism-permanence`
are not invoked: Mathlib's `QuasiCompact.compactSpace_of_compactSpace`,
`quasiSeparatedSpace_of_quasiSeparated`, affine-open instances and composition
instances supply the required geometric properties directly. The definitions
`sk-def-sfb-dc-setting` and `sk-def-localizing-closure` remain statement prerequisites.
`def-weil-finite-type-morphism`, `def-weil-closed-immersion`,
`det-sf-mate-open-restriction`, `det-thm-int-restriction-line`, and
`det-thm-int-restriction-closed` are retained through the two chart helpers.
`sk-lem-int-tensor` is no longer a direct dependency of this argument: the existing
compact-support theorem supplies the exact constant-model pullback assertion;
its own dependencies are unchanged.

## Where the brief, the DAG or earlier work was wrong

The retained sandbox already completed the local chart calculation and its
geometric/adjunction factorization, with no new holes. This resumed session checked
the retained proofs against the current sources and recompiled all three modules.
The original `integralTensorInverseImage` theorem uses the older bounded-constructible
predicate, whereas this item uses finite constant models. The existing compact-support
construction's explicit `constructible_pull` clause has precisely the needed predicate.
No repair of that tensor theorem is made or required here.

The earlier attempt recorded LeanSearch, Loogle/LeanFinder and grep searches for
both new nodes. Those search records and their retained results are included unchanged.

The gluing theorem's clause (2) repeats the global preservation assertion. The proof uses
only clause (1), and proves the local chart preservation by the unit's line and closed
route. Empty charts, zero complexes and dimension zero are included by the finite generating
set construction, existing preservation statements and categorical adjunction arguments.

## New nodes

`lem-sfb-integral-exceptional-affine-chart`, in
`lean/Sheaf/SixFunctors/IntegralExceptionalAffineChart.lean`, proves bounded constructibility
on one affine chart over an affine target chart. Its proof uses the following proved
factorization and the declared affine-space and closed-immersion preservation theorems.

`lem-sfb-integral-exceptional-affine-factorization`, in
`lean/Sheaf/SixFunctors/IntegralExceptionalAffineFactorization.lean`, proves existence of a
finite closed affine-space presentation and the induced object comparison for every object
of the localizing category. It asserts no bounded-constructibility preservation and assumes
none. The adjoints are eliminated inside the proof of a proposition; no definition chooses
nonunique data from an unproved existence theorem.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
