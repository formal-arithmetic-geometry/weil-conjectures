## What changed

`Sheaf.Paper.FieldShriekCompositionQcqs` now proves
`WeilConjectures.sfFieldShriekCompositionQbar_existsUnique` from a strictly smaller
coefficient-square obligation and the existing upstream stage-system descent API.
The proof forms the compatible finite natural transformation, descends it,
proves it is an isomorphism, identifies its literal-pair component by a proved
equality-transport helper, and proves uniqueness with Iso.ext and NatTrans.ext.
The existing rationalization proof is unchanged.

The eight proper/open definitions and normalization predicates were moved verbatim
into `Sheaf.Paper.FieldShriekCompositionNormalization` and publicly re-exported by
the item. This enables an acyclic new proof dependency without changing the
objects, operations, or existing consumer interface. The new module
`Sheaf.Paper.FieldShriekCompositionCoefficientSquare` states the scalar square
for supplied normalized integral compositors and their supplied rationalizations.
It does not assert their existence, invertibility, naturality, uniqueness or descent.

All three modules compile cleanly through `lcompile.py`; the final item compile
completed in 21.7 seconds. No source-library file or target statement is modified.
Change record:
`coord/changes/H1-field-shriek-coefficient-descent.md`.

## Proved and sorry left

The item began with two direct holes. One upper hole is closed in Lean:
`WeilConjectures.sfFieldShriekCompositionQbar_existsUnique`
(node `lem-zl-field-shriek-composition-qcqs`). One lower hole is added:
`WeilConjectures.sfCompositionOnCoefficientStage_comm`
(node `lem-zl-field-shriek-composition-coefficient-square`).
This is a decomposition, with net zero direct holes removed, not a complete proof
of coefficient compatibility. The actual new Lean combination proves all of descent,
invertibility, the component formula and uniqueness from that coefficient equation.

The existing hole left untouched is
`WeilConjectures.sfFieldShriekCompositionIntegral_existsUnique`
(node `lem-zl-field-shriek-composition-qcqs`). There are two direct holes across the
three delivered modules: that integral theorem and the new coefficient square.
There are no holes in definitions or private helpers. The rational theorem was
already proved at the base and is not counted as a newly closed hole.

## No longer needed

No declaration or module is withdrawn. The integral proof plan remains open, so
its still-needed geometric, refinement and realization dependencies remain in the
DAG. They are not declared unnecessary solely because their unfinished proof has
no Lean references yet. The following private proof imports are unused by the
actual present Lean proofs and are removed from this module:

- `WeilConjectures.Compactification.NagataCompactification`
- `Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle`
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.IntegralResidueTor`
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.FiniteTorAmplitude`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`
- `Sheaf.Paper.SfDerivedComplete`
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`
- `WeilConjectures.Compactification.CategoryBaseChange`
- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`
- `Sheaf.Paper.SfScalarExtensionComposition`
- `Sheaf.CategoryTheory.StageSystemFunctorDescent`
- `Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars`
- `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`
- `Sheaf.AlgebraicGeometry.CompactificationRefinementCoherence`
- `Sheaf.Paper.BasicOperationsCoefficientReduction`
- `Sheaf.Paper.SfIntegralCompactSupportConstructible`
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`
- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`

The Qbar descent uses `StageSystem.Morphism.descNatTrans`,
`isIso_descNatTrans` and `functorCompIso` from the already imported upstream API;
it needs neither a second quotient-category construction nor a Karoubi extension.
The parent DAG no longer directly cites `lem-fix-operation-reduction` or
`lem-weil-scalar-extension-composition` for Qbar descent: those dependencies are
retained under the new coefficient-square node. No mathematical branch of the
integral unit route is bypassed. Obsolete direct `tool_uses` approvals for
`lem-fix-operation-reduction` and `lem-weil-scalar-extension-composition` are removed
from the parent; their proof dependencies remain at the new scalar-square node.

## Where the brief, the DAG or earlier work was wrong

The module has two holes, because the rational theorem was already proved by R3.
The current parent DAG describes a direct completed-ring integral route, whereas
the existing integral docstring and private imports still mention the older full
system-realization route. This delivery does not claim to have completed either
integral route; it preserves that theorem, its signature, docstring and hole.

The stated general descent interfaces are sufficient for the common-stage part,
but do not supply the geometric coefficient square. In particular,
BasicOperationsCoefficientReduction does not have the displayed equation for
this supplied compactification compositor as a direct clause. The new lemma makes
exactly that step explicit, conditional on the existing normalization.

The scalar-square statement was checked on the identity inclusion, a zero input,
empty schemes, arbitrary compactifications and independent coefficient/scheme
universes. It imposes no separated structure morphisms. It uses no faithfulness
claim for finite derived evaluations. All constructions and the formal descent
remain on the recorded raw categories.

Searches used LeanFinder (compatible families), LeanSearch (coefficient compatibility),
Loogle (NatIso.ofComponents) and grep, plus direct reads of the local stage-system,
coefficient-action, scalar-mate and refinement APIs. The latest blueprint's
compact-support composition proof and operation-reduction final paragraph were
read, as was Stacks more-etale.tex, lemma-shriek-composition.

## New nodes

`def-zl-field-shriek-composition-normalization` attaches the existing proper/open
arrows and normalization predicate to their new shared module. It introduces no
new mathematical condition and has no holes.

`lem-zl-field-shriek-composition-coefficient-square` is step 7 of the parent proof:
one scalar square for supplied integral compositors normalized on compatible
towers, after raw rationalization and relabeling the finite actions. Its proof in
words follows the source's unit/counit scalar compatibility, pasting, normalized
refinements and localization. It is strictly a part of the argument; the parent
performs actual stage-system descent, establishes isomorphism and proves uniqueness.
Both nodes inherit the chapter, unit and nearest blueprint ancestor. Neither
points back to the parent existence theorem, so this creates no DAG cycle.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
