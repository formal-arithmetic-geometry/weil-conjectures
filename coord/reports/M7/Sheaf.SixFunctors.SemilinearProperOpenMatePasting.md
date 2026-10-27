## What changed

Filled `AlgebraicGeometry.ProEtale.SemilinearProperOpen.rhoJInv_isIso`.
The section-normalized ordinary scalar package `VaryingRing.ordinaryScalarComparison`
is compared with the actual `rhoOrdinary` at every level and transition
(`scalar_rho_iso`). Localizing its open-extension isomorphism (`scalar_open_existsIso`)
puts the target in the essential image of tower open extension. That functor is fully
faithful because its unit is invertible, so its counit is invertible there. The
specified inverse mate is then a composite of three isomorphisms
(`inverse_mate_support_isIso`). The new helpers are private and fully proved.

Reviewer correction (2026-10-24): the delivered version also redefined the item's
public operations (`coefficients`, `transition`, `Modules`, `push`, `pull`,
`ordinaryAdj`, `P`, `R`, `adj`, `pushComp`, `pullComp`, `pComp`, `sComp`, `extension`,
`ordinaryOpenAdj`, `J`, `levelTower`) as abbreviations of the `VaryingRing`
operations. It also rewrote the proofs of `evalR_isIso`, `evalJInv_isIso` and
`compositor_associativity`. That refactor broke three importers that compile against
the published item: `Sheaf.Paper.FiniteFreeSystemRestriction`,
`Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` and
`Sheaf.SixFunctors.SemilinearEvaluationRingSquare`. The reviewer withdrew it. The module
is now the published one plus the proof above and the plain import
`Sheaf.AlgebraicGeometry.SemilinearScalarOrdinaryComparison`. The change record
`coord/changes/M7-semilinear-canonical-operations.md` records the withdrawal. The
corrected module compiles in about 36 s.

## Proved and sorry left

Closed one of the original seven holes: `rhoJInv_isIso`. Added zero holes;
split off zero statements. The six original holes below remain, all in
`AlgebraicGeometry.ProEtale.SemilinearProperOpen`, attached to
`lem-sf-semilinear-proper-open-mate-pasting`:

- `semilinearProperOpenMatePasting`
- `gamma_identities`
- `rhoPullInv_isIso`
- `rhoR_isIso`
- `gamma_scalarRestriction`
- `gamma_evaluation`

`rhoJInv_isIso` depends on `sorryAx` only through `rhoP`, which uses the open hole
`rhoPullInv_isIso`, and through the unchanged holes of its declared dependencies.

## No longer needed

Nothing. The proof of `rhoJInv_isIso` adds a use of
`lem-sf-semilinear-scalar-ordinary-comparison`, already a proof dependency of step 5.

## Where the brief, the DAG or earlier work was wrong

No false statement found. Equality of functors alone does not identify distinct
adjunction structures. The open-invertibility proof avoids such an identification:
full faithfulness and an independently constructed essential-image isomorphism
suffice for the specifically defined mate.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
