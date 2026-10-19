## What changed

Changed only proofs in lean/Sheaf/Paper/PbcVerdierAxioms.lean.
CategoryTheory.StageSystem.qbarStageInclusionAdditive now follows from the
normalized addition formula of pairPreadditive_exists and additivity of the
identity-stage transition. AlgebraicGeometry.Scheme.pbcVerdierAxioms projects
triangulation and exact stage inclusions from the existing
commonStage_verdier_existsUnique witness used to define qbarPairPretriangulated;
its final component uses the existing qbarTransIsoCommShift instance.
CategoryTheory.StageSystem.qbarTransIsoCommShift is now proved componentwise:
the canonical inclusion comparisons are identities; both sides are common-stage
representatives, and pbcStageShift_coherence followed by cancellation of the
shift comparison proves equality. No auxiliary statement is added.
The chosen pretriangulation, public signatures, instances and imports are unchanged.
A declaration-local unused-section-variable linter setting preserves the original
signature of both generic instance theorems while their proofs use fewer hypotheses.

## Proved and sorry left

Closed 3 of the original 5 direct holes:
- CategoryTheory.StageSystem.qbarStageInclusionAdditive.
- CategoryTheory.StageSystem.qbarTransIsoCommShift.
- AlgebraicGeometry.Scheme.pbcVerdierAxioms.

Added 0 holes and split off 0 statements. The two original holes remain:
- AlgebraicGeometry.Scheme.qbarStageTriangulated
  (thm-weil-pbc-verdier-axioms).
- AlgebraicGeometry.Scheme.qbarScalarExtensionExact
  (thm-weil-pbc-verdier-axioms).

The main theorem still depends on these named obligations and on the existing
holed generic Verdier theorem; this is not a claim of axiom-free target completion.
The stage proofs still need transport between the separately chosen normalized
rational shift and integral-image pretriangulation and the scalar-localization
triangulation; the scalar-extension module uses a separate coefficient-stage
interface and is not a direct instance application for this category.

## No longer needed

No imports, nodes or modules withdrawn. All original public imports are retained
for the existing public interfaces, and the original DAG route is retained.
The main theorem reuses the generic Verdier declaration already named by its
original docstring and DAG lean.note, rather than repeating its axiom checks.
No new dependency imports are needed by the completed proofs.
The proof-dependency imports added since the earlier attempt are retained for
the two remaining finite-stage obligations; none is claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned source was initially absent while the shared checkout updated, then
became available and was copied unchanged before proof edits. A compile request
also timed out waiting for the server; retrying returned ordinary Lean diagnostics.
No mathematical statement or definition was changed. The generic Verdier theorem
already specifies exactly the pretriangulation chosen in this module, so its
chosen witness directly supplies the first two conjuncts of the main theorem.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
