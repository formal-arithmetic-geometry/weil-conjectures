## What changed

Reduced `AlgebraicGeometry.fpqc_affine_effective_models_glue` to the pairwise Cartesian
comparison of two local effective models. The existing statement and visibility are unchanged.
`Sheaf.AlgebraicGeometry.FpqcAffineModelTransitions` is a new module containing the single
remaining comparison theorem. The parent node now follows the Lean proof.

The proof chooses the local models from the given effectivity hypotheses, proves their
projections are fpqc effective epimorphisms, obtains pairwise transitions, and proves their
identity and composition laws by cancellation. It constructs relative gluing data explicitly,
glues the projections on the twice-pulled-back directed affine cover, and proves the global
pullback square using `Scheme.isPullback_of_openCover`. It finally derives the requested
local transport invariance from the local model invariance and the gluing restriction equation.
All three private helpers are proved; no definition or private theorem contains a hole.

The complete sandbox compiles with the launcher's `lcompile.py --all`.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.fpqc_affine_effective_models_glue`
(node `lem-galois-fpqc-affine-models-glue`). No sorry remains in the item's module.

Added one hole: `AlgebraicGeometry.fpqc_affine_model_transition`
(node `lem-galois-fpqc-affine-model-transitions`) in
`Sheaf.AlgebraicGeometry.FpqcAffineModelTransitions`. It asserts only the existence of a
Cartesian transition for ONE inclusion between supplied local models. It asserts neither
functor laws, nor a global model, nor a global projection, nor local invariance of that
projection. Those parts are proved in the parent. This is a decomposition, with one hole
closed and one added (net zero), not a sorry-free proof of fpqc affine model gluing.

## No longer needed

Removed the parent's direct proof import `Sheaf.AlgebraicGeometry.FpqcMorphismsDescend`.
Its lemma remains needed in the plan for the new pairwise-comparison item, so it is not a
mathematical dependency pruned from the overall argument. No original DAG dependency
becomes unnecessary: relative gluing and morphism gluing are used through Mathlib, and
morphism descent is used by the remaining comparison node. No globally pruned module is claimed.

The separate construction and gluing of inverse pullback identifications in the old proof
plan is unnecessary: Cartesian locality checks the pasted local squares directly.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The old proof plan left the nested-affine comparison and
coherence as one informal step. The comparison is now isolated, while coherence, gluing,
the global pullback check, and transport invariance have compiling Lean proofs.

The local Stacks source files are absent on this machine. Read the official sources at
https://stacks.math.columbia.edu/tag/02W3 and https://stacks.math.columbia.edu/tag/01LH.
The relevant paragraph of 02W3 compares models over nested affine opens before gluing.
LeanSearch was unavailable (HTTP Internal Server Error); its failure is recorded accurately.
LeanFinder, Loogle and Mathlib grep were run through `msearch.py`; logs are in searches.jsonl.
Blueprint searches for glue, affine descent, 02W3 and transition found no equivalent pairwise
statement. The existing generic invariant-open gluing theorem uses opens in V over a fixed
base, so it does not directly supply this transition between models over different affine bases.

Edge cases: no nonempty index set or nonempty scheme is assumed; the cover-gluing and
Cartesian-locality APIs handle empty V and S. The new comparison permits the empty affine
open and i = identity. It assumes no separatedness, quasi-separatedness, affineness of
intersections, or global quasi-compactness of the given fpqc singleton. The unit's realized
statement and steps are untouched.

## New nodes

`lem-galois-fpqc-affine-model-transitions` states the Cartesian transition and reconstruction
for one affine inclusion. Its source is the nested-affine paragraph of Tag 02W3 and full
faithfulness from Tag 02W0. The node records the actual searches and a complete proof plan;
its Lean signature is copied verbatim from the compiling new module. It is strictly the
local comparison step, rather than a rewording of the parent theorem. No change record
or forced adaptation is needed because no existing interface changed.

## Second reading by B3

1. I compared the delivered parent module with the repository version. The theorem
   `AlgebraicGeometry.fpqc_affine_effective_models_glue` has the identical signature and
   conclusion; only its proof and proof-only imports changed. The new transition module has
   a distinct declaration and does not alter an existing interface.
2. I compiled both modules with the launcher. The parent theorem is fully proved. The only
   remaining `sorry` is the named public theorem
   `AlgebraicGeometry.fpqc_affine_model_transition`; it has a source, complete proof plan,
   docstring, and matching DAG node. No definition contains `sorry`, and no forbidden
   declarations occur.
3. The split statement is the one-inclusion Cartesian comparison required by the parent
   proof. It does not assert coherence, global gluing, or invariance, so it is strictly
   smaller than the parent target and is true in the stated edge cases. Searches recorded in
   the node found no existing equivalent declaration.
4. The parent proof uses the shortest available local route: fpqc base change and effective
   epimorphism, the split transition result, cancellation for coherence, and Mathlib's
   directed relative gluing and open-cover pullback checks. The removed direct import of
   `Sheaf.AlgebraicGeometry.FpqcMorphismsDescend` is no longer needed by this module; that
   dependency remains recorded for the transition node. The unit's realized route is kept.
5. The DAG proof and dependency lists match the Lean proof, and the new node records its
   statement, source, searches, proof steps, and Lean declaration verbatim. I changed only
   the report by adding this review section; no Lean statement or definition was changed.
