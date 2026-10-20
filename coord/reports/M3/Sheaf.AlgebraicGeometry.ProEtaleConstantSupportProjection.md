## What changed

Completed `AlgebraicGeometry.ProEtale.isIso_constantSupportProjection` in
`Sheaf.AlgebraicGeometry.ProEtaleConstantSupportProjection`, preserving its statement
and the existing constant-sheaf exactness instance. All added imports are private.
Restored the node after the concurrent batch take-out, with current M3 creation and
Lean authorship metadata and without stale review stamps. Updated its proof to record the concrete coproduct, shift, and unit arguments;
its two proof dependencies and its statement are unchanged.

The proof follows the node's generation argument. Private lemmas establish shift
compatibility and the tensor-unit calculation for the canonical derived tensor
comparison of an exact monoidal functor, adapting the already-proved private
calculations in `Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula`. Taking its adjunction mate gives the same
properties for projection. The isomorphism locus after restriction along derived
constant sheaves is closed under coproducts, distinguished triangles, and retracts;
`derivedModuleFreeGeneration` therefore proves the assertion from the regular module.
The unit identification uses monoidality of constant sheaves and the degree-zero
single-functor unit isomorphism.

Private data interfaces are definitionally equal to the canonical projection mate and
the constant-generator unit isomorphism. The support argument is proved for an abstract
coefficient category before specialization, avoiding repeated unfolding of the concrete
sheaf localization structures. No shared definition or public interface was changed.

The coproduct hypothesis is used precisely on compact-support pushforward. The open
projection isomorphism and the compactification pullback-composition isomorphism
identify the target coefficient functor with `Lf* ⋙ (K ⊗ -) ⋙ Rf!`. No preservation
of coproducts by unrestricted proper pushforward is assumed.

Validation: the cleaned module compiled without warnings through `lcompile.py` in
24 seconds, with normal compiler settings.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.ProEtale.isIso_constantSupportProjection`
(node `lem-exc-proetale-constant-support-projection`).

Relative to the assigned module: holes closed 1, holes added 0. The current delivery
base no longer contains that module, so the delivery restores it fully proved. Holes remaining in the delivered module: 0.
Every private helper is proved; no statements were split off.

## No longer needed

No existing node, module, or public import is pruned. Removed unused candidate proof
imports from the working proof:

- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`
- `WeilConjectures.CategoryTheory.Adjunction.ProjectionMapUnit`
- `WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable`
- `WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction`

Both declared proof dependencies
are used: derived tensor closedness and generation by the regular module.

## Where the brief, the DAG or earlier work was wrong

The generation theorem does not itself require the noetherian hypothesis; the assigned
statement retains that hypothesis verbatim. The node's coproduct step needs the open
projection identification described above, because the hypothesis concerns `Rf!`,
whereas the projection map is expressed using `Rg*`.

The shared repository removed the V7 parent adaptation, this item module and its node
while this proof was being developed (batch `20261020T211611` dependency take-out).
The first preflight therefore treated this as a new module/node. The restoration keeps
the assigned mathematical interface and original dependencies, updates creation/authorship
metadata, and records the public interface addition relative to that changed base.

## New nodes

`lem-exc-proetale-constant-support-projection` is restored under its original id and
Lean attachment in `dag/nodes/sec-smooth-purity/`. Its statement, source, unit and two
proof dependencies are unchanged from the assignment; its Lean theorem is now proved.
It is not a split-off obligation. Change record:
`coord/changes/M3-proetale-constant-support-projection-restoration.md`.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
