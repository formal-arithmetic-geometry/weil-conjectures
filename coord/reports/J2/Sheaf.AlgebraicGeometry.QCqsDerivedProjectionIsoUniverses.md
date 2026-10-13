## What changed

Proved the body of
`AlgebraicGeometry.nonempty_qcqs_derivedProjection_iso_universes` in
`Sheaf.AlgebraicGeometry.QCqsDerivedProjectionIsoUniverses`, without changing its
signature, universes, visibility, or existing docstring.

The proof obtains the derived adjunction and monoidal pullback model, constructs the
projection mate, and conjugates it by the shared derived tensor symmetries to match
the factor order in the statement. It covers the target by all affine opens. For
each open it explicitly constructs the inverse-image scheme and restricted morphism;
Mathlib proves this source compact and quasi-separated from the morphism hypotheses
and the affine target. The existing `qcqsDerivedProjectionMate_isIso` applies to
these two qcqs schemes in localization universe u. An arrow comparison transfers its
isomorphy to the restricted global mate. Restriction maps the symmetry isomorphisms
to isomorphisms. Open-cover detection and `asIso` finish the proof.

Added proof-only imports of `DerivedAdjoint`, `DerivedPullbackMonoidalModel`,
`DerivedTensorSymmetry`, `ProjectionFormulaLocality`, `QCqsDerivedProjectionMate`,
and the new `DerivedProjectionMateOpenRestrictionComparison`. The original public
imports remain. No existing dependency interface changed and no consumer was adapted.
Updated the item's DAG proof, proof dependencies, and proof origin to this route.

The one new module isolates comparison of arrows under open restriction, including
transport to the local small derived categories. Its statement makes no isomorphy
claim about the projection mates and imposes no compactness or quasi-separatedness
hypothesis. The scheme and restricted morphism are inputs identified by hZ and hg,
not data selected from an unproved existence theorem. Its remaining existential
witnesses are eliminated only inside a proof of IsIso; no public definition obtains
data from this theorem.

Validation: both delivered modules compiled individually/in import order using
lcompile.py. An initial version that expanded the restricted morphism inside the
statement timed out; explicitly parameterizing the scheme and morphism fixes that
elaboration problem while keeping their identifying equalities. The final modules
compile in seconds without increasing the compiler's time limit. The delivery dry
run supplies the static checks and axiom probe.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.nonempty_qcqs_derivedProjection_iso_universes`
(node `lem-pc-qcqs-derived-projection-iso-universes`). No sorry remains in the item's
module.

Added one hole:
`AlgebraicGeometry.exists_derivedProjectionMate_openRestriction_comparison`
(node `lem-pc-derived-projection-mate-open-restriction-comparison`), with its whole
proof exactly `:= by sorry` in its own module. This is a decomposition: one hole
closed and one added in the delivered files, not a complete sorry-free proof of the
projection formula. The existing qcqs mate theorem also still depends on its own
recorded lower obligations; those are reused, not re-added or proved in this delivery.

The comparison lemma is strictly the restriction/transport part of the argument:
it gives an isomorphism of arrows, not invertibility of either arrow. The actual
invertibility is obtained separately from the existing qcqs theorem, and the global
conclusion is obtained separately by open-cover detection. Affine generation is
therefore not moved into the new hole.

Edge cases checked against the mathematical comparison: empty opens give zero
module categories and the unique commuting square; zero factors are preserved by
exact restriction and the additive derived operations; identity morphisms give the
usual restriction comparison of the unit/counit mate. No boundedness, coherence,
Noetherianity, or global quasi-compactness assumption was added. The unit record's
realized lists are empty, and no unit-level route was bypassed.

## No longer needed

None: no original import was removed and no module is claimed pruned. The original
plan's affine-equivalence/free-generation/coproduct/QCoh lemmas are no longer invoked
directly here, but remain needed through `QCqsDerivedProjectionMate` and its recorded
lower lemmas. In particular `lem-pc-affine-qcoh-derived-equivalence`,
`lem-pc-derived-module-free-generation`, `lem-sc-derived-tensor-right-coproducts`,
`lem-pc-derived-direct-image-preserves-direct-sums`, and
`lem-pc-derived-pullback-tensor-qcoh` must not be marked globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The existing qcqs mate theorem requires both schemes to be globally compact and
quasi-separated. Those assumptions are absent from this item, so applying it to the
original X and Y would be invalid. They do hold for the constructed restricted
morphism over an affine open, as proved in Lean. No change to that existing theorem
is needed.

For direct image commuting with open restriction the precise source is Stacks Tag
08FE, Lemma 20.32.4. Tag 08BV, used in some adjacent module descriptions, states an
unbounded Mayer-Vietoris triangle. The new comparison cites 08FE and the locality
sentence of 08EU. The literature files are absent on this machine; the two cited
Stacks pages were read directly online. No missing-source claim is inferred from
this local absence.

The open comparison still needs a formal proof of descent of the supplied tensor
comparison and adjunction and its commuting square. The existing open restriction
and tensor/direct-image comparisons do not themselves state that square. This
precise glue is the new obligation. The proof constructs the inverse-image scheme
before invoking it and does not choose an arbitrary scheme from a holed theorem.

## New nodes

`lem-pc-derived-projection-mate-open-restriction-comparison`, in
`dag/nodes/sec-picard-framework/lem-pc-derived-projection-mate-open-restriction-comparison.json`,
is stated in `Sheaf.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison`
by `AlgebraicGeometry.exists_derivedProjectionMate_openRestriction_comparison`.
It records the exact Lean signature, a five-step restriction/localization/adjunction
comparison argument, source, searches, and the parent's chapter/unit. Its docstring
spells out the source and target comparisons and the commuting-square equation.
The statement is independent of the projection mate's invertibility. Blueprint and
repository searches found no exact existing comparison: the existing affine descent
lemma concludes invertibility and assumes globally qcqs schemes. There are no change
records because no existing interface changed.

## Second reading by J2

1. Compared the delivered item's existing declaration with the repository version. The theorem signature, universes, visibility, and docstring are unchanged; the added proof only replaces the original `sorry`.
2. Compiled both delivered modules with `lcompile.py --all`; they compile without errors. The item has no remaining `sorry`; the new comparison theorem is the single explicitly split named `sorry`. No prohibited declarations or hollow definitions occur.
3. Reviewed the split comparison statement and node. It is a genuine restriction and arrow-comparison obligation, with no invertibility claim or extra qcqs hypotheses, and its docstring records the source and proof route.
4. Checked the proof route against the DAG and unit. The proof uses the existing adjunction, monoidal model, symmetry, locality, qcqs mate, and the new comparison; no unit-level route is bypassed and no imports were removed.
5. The DAG proof, proof dependencies, proof origin, and new node metadata match the Lean declarations. No statement or definition changed.

Changed during second reading: no Lean or DAG repairs were needed; this review section was added.
