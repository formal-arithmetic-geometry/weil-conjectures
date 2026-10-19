## What changed

Proved `CategoryTheory.frame_dual_mate` in
`Sheaf.CategoryTheory.DerivedCategory.FrameDualMate`, preserving every existing
signature, definition and docstring. No additional import is needed. Removed the redundant direct `ModuleHomComplex` import: the retained public
`ModuleHomPrecompHomotopy` import already supplies it. The delivery base renamed
this module from `Sheaf` to `WeilConjectures` during the interruption; using the
existing transitive import preserves the public interface through that rename.

The evaluation equation is checked degreewise. The zero components handle nonzero
total degrees. Total-tensor extensionality and pure-tensor extensionality reduce
degree zero to the given evaluation formulas. Explicit `zero_cochain_comp_v` and
`ofHom_v` rewrites identify both sides with φ(f(x)). The given triangles install
local exact pairings. Applying `tensorRightHomEquiv` identifies any solution with
`rightAdjointMate f`; its coevaluation identity proves the second equation.
Caching the existing monoidal instances locally avoids repeated instance searches.

A declaration-local `linter.unusedVariables false` keeps the original redundant
hypotheses without warnings. The checker requires an interface-command record for
this scoped option: `coord/changes/frame-dual-mate-linter.md` records its unchanged
mathematical interface and downstream users. There are no consumer adaptations.

Updated the proof and proof origin of `lem-trf-frame-dual-mate` to this argument.
Its proof-dependency set remains empty. The unit `sk-p-trace` has no realized node
attached to this item; its trace and transported-duality route is preserved.

Earlier turns ran msearch leanfinder searches for uniqueness and naturality of
right duals, loogle searches for `rightAdjointMate` and the tensor-Hom equivalence
lemmas, and grep searches for total-tensor extensionality and inclusions; the
queries and results remain in `searches.jsonl`. Read the corresponding Mathlib
rigid-category, total-tensor and homogeneous-cochain APIs, the definitions used
here, the node, and the current blueprint proof.

## Proved and sorry left

Closed 1 original hole: `CategoryTheory.frame_dual_mate`
(node `lem-trf-frame-dual-mate`). Zero holes remain in the item and zero holes are
added elsewhere. No statements were split off. The precomposition chain map uses
the existing `CochainComplex.moduleHomPrecomp_comm`, now proved in the shared
library; its definition and all other dependencies are unchanged.

Validation: the final single-file server compile through `lcompile.py` passed
cleanly in 11.1 seconds. The preceding uncached version also compiled cleanly,
in 59.5 seconds. The scoped cache changes only proof elaboration and reuses the
existing monoidal instance verbatim. Delivery preflight checks the final packet.

## No longer needed

Removed the redundant direct public import of
`WeilConjectures.Algebra.Homology.ModuleHomComplex` (originally under `Sheaf`);
`ModuleHomPrecompHomotopy` already publicly imports it. No modules or nodes pruned. Removed the redundant
proof import `Mathlib.CategoryTheory.Monoidal.Rigid.Basic` introduced during earlier
development; the original public imports already supply its declarations.
There were no declared proof dependencies to remove. The explicit coevaluation
sum expansion and functional-by-functional uniqueness calculation in the old
plan are unnecessary: the assumed triangles and Mathlib's tensor-Hom equivalence
supply these conclusions. All original frame, boundedness, finiteness,
projectivity and coevaluation-component hypotheses remain verbatim.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The original plan was valid
but longer than necessary given the assumed triangle identities. The argument
also covers zero complexes, empty frames, nonfree projectives and characteristic
two, without extra hypotheses. On resumption after the provider interruption,
the latest saved compile had an unfinished simplification in the evaluation
calculation; the explicit component rewrites above repair it. No previous push
was recorded or active for this item when work resumed.

The first resumed push was refused before pushing because the shared library had
renamed `ModuleHomComplex` during the interruption. Updated the sandbox import
to the current upstream path. That exposed old pre-rename cached dependencies,
which duplicate the same declarations if both module paths are imported.
Removed the redundant direct import, whose declarations the retained public
precomposition import already supplies; the change record documents this public
import removal and its unchanged transitive interface. Reran delivery checks.

A later delivery compile timed out before pushing. A diagnostic profiler compile
passed in 34.8 seconds and identified repeated monoidal instance inference.
An additional `MonoidalCategoryStruct` cache made elaboration worse and was
removed. The restored single `MonoidalCategory` cache compiled cleanly in
7.6 seconds. No profiler option remains in the delivered file.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
