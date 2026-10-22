## What changed

Completed the listed zero-hole retirement of
`Sheaf.AlgebraicGeometry.ConstantStrictFibreStalkComparison` (retire-items row 2826).
The existing upstream theorem already proves the canonical constant-coefficient stalk
comparison. Migrated the sole Sheaf consumer, `NormalConstantGenericUnit`, to it.
All public and private consumer signatures and public imports are unchanged. The
private proof base-changes the small/full strict-henselization colimit isomorphism,
uses its existing `small_toBase` equation, and transports connectedness through the
resulting homeomorphism before applying the full-model theorem. An explicit proof
import supplies the small structural-map API formerly visible through the retired file.

The consumer compiles cleanly with lcompile.py (7.3 s). The original comparison also
compiled cleanly before retirement (15.0 s). Delivery preflight checks the retained
consumer and its declaration axioms. No upstream source file is edited.

The comparison node now names the adopted declaration and its verbatim full-model
signature. Its proof metadata drops the obsolete section-restriction transport; the
parent node records the connectedness transport actually used. Change record:
`coord/changes/D3-constant-strict-fibre-stalk-comparison-retirement.md`.

## Proved and sorry left

This is a retirement repair with zero initial holes, zero holes closed, zero holes
added, and zero holes left. The existing proved upstream
`AlgebraicGeometry.Etale.constant_strict_fibre_stalk_comparison` is retained unchanged.
The consumer's
`AlgebraicGeometry.Etale.isIso_unit_constantSheaf_generic_unit` and every private helper
remain fully proved. No split-off statement is added.

## No longer needed

Withdraw `Sheaf.AlgebraicGeometry.ConstantStrictFibreStalkComparison` through deleted.txt;
remove its import from `Sheaf.AlgebraicGeometry.NormalConstantGenericUnit`, replacing it
with the adopted upstream module. Its node is retained on the upstream declaration.
The retired file's private `coefficient_two_pullbacks` is no longer duplicated; the
upstream proof already supplies its own proved helper.

The comparison proof no longer needs
`def-weil-pbc-small-strict-local-section-maps` or
`lem-weil-pbc-etale-unit-section-restriction-comp`; remove those two proof dependencies
and the obsolete transport step from its node. The retired copy's imports
`Sheaf.AlgebraicGeometry.SmallStrictLocalSectionMaps` and
`Sheaf.AlgebraicGeometry.EtaleUnitSectionRestriction` therefore leave this route.
Those modules/nodes can still serve other consumers and are not withdrawn here.
The qcqs comparison, constant-pullback, constant-transition, stalk and
strict-henselization dependencies used by the upstream proof remain needed.
The unit's statement and steps are preserved.

## Where the brief, the DAG or earlier work was wrong

The item has no current sorry: it is a listed duplicate retirement, authorized by the
human's retirement instruction. The retire-items shorthand says the statements match,
but the current Lean signatures use distinct strict-henselization presentations.
A bare import replacement is insufficient. Explicit connectedness transport repairs
the sole consumer while preserving its complete interface.

Searches ran through msearch.py (LeanFinder, Loogle, grep) and direct rg of both roots.
LeanFinder found Zariski stalk lemmas, not the requested etale comparison; Loogle found
the generic germ API. Direct source inspection found the exact adopted theorem and
verified its proof and its existing qcqs, constant-pullback and generator dependencies.
Read Stacks etale-cohomology.tex, theorem-higher-direct-images (03Q9), and
lemma-push-constant-sheaf-from-open (09Z5). No mathematical statement is weakened.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
