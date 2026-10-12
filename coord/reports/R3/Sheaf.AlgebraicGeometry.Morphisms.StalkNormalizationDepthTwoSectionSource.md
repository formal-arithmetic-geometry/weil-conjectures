## What changed

Replaced the sole sorry of `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_depth_two_section_source` with a compiling assembly proof. Its signature and existing docstring are unchanged.

The proof obtains the depth bound from the proved normal-local-depth theorem, obtains a flat target neighbourhood from a new formal-section lemma, pulls that neighbourhood back to a source open, proves membership using the fibre equation, proves flatness using the restriction identity and composition with the open immersion, and applies the new purity criterion. The existing node now records these steps.

Added two modules, each with one public theorem and one DAG node: `StalkNormalizationDepthTwoSectionFlat` supplies a target open with flat restriction; `StalkNormalizationFlatEtale` states the independently reusable flat-to-etale criterion, with no section, group, rational point, or connected-fibre assumption. Their docstrings contain the full source arguments. Only the first statement uses torsor data; even there invertibility of the group order is unnecessary in the depth-two case. No existing signatures, definitions, public imports, or other modules were changed.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_depth_two_section_source` (node `lem-sbc-stalk-normalization-depth-two-section-source`). No sorry remains in the assigned module.

Added and left as whole named theorem proofs:

- `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_depth_two_section_flat`, node `lem-sbc-stalk-normalization-depth-two-section-flat`.
- `AlgebraicGeometry.Scheme.finiteEtale_stalk_normalization_etale_of_flat`, node `lem-sbc-stalk-normalization-flat-etale`.

This is a decomposition: one upper hole closed, two strictly smaller holes added, net holes closed minus added = -1. It does not claim an unconditional proof or a reduction in total holes. The first outstanding statement obtains only flatness on a target neighbourhood; the second is the separate purity step turning flatness into etaleness without any torsor or section assumptions.

All three modules compile together with lcompile.py without warnings. The deliver3.py --no-push dry run printed OK: compilation and preflight passed except for the second-reading section, which is reserved for the independent reader. Nothing was pushed. Edge cases checked in the arguments: relative dimension zero, empty cover/source open, disconnected finite covers, and an arbitrary finite group in the depth-two formal calculation. The finite assumption is retained to identify the concrete normalization with the coherent depth-two extension; completion is used faithfully flat only after localization at the section point.

## No longer needed

Removed direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull`.
- `Sheaf.AlgebraicGeometry.Morphisms.GenericFibreActionExtension`.
- `Sheaf.RingTheory.FlatLocalDepthFormula`.

These remain dependencies of the new formal/purity statements, so no node or module is globally pruned. Their original nodes `lem-sbc-normal-integral-generic-hom-full`, `lem-sbc-generic-fibre-action-extension`, and `lem-weil-pbc-flat-local-depth-formula` are no longer immediate dependencies of the assigned node. `Sheaf.RingTheory.NormalLocalDepthTwo` is still used directly. No unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing four declarations do not state the formal-completion or depth-two purity steps. Their signatures provide generic morphism/action extension and ring depth results, but cannot alone assemble the entire section calculation. The delivery exposes those two missing portions instead of treating the cited Stacks tags as already formalized results.

The local source argument must use going down over the normal base, together with incomparability, for equality of prime heights. Localizing a finite algebra at just one source prime must not be described as still a finite integral local map. The new proof descriptions make this distinction explicit.

Mathlib searches found normalization constructions, smooth flatness and etale descent/locus results, but no theorem for either new statement. LeanSearch returned an internal server error and is recorded as unavailable. Blueprint searches for depth-two flat-etale purity, completion sections, 0EY6 and 0EY9 found no matching blueprint node. The ancestor tool returned None for this module-created item; the new nodes retain the explicit blueprint ancestor already recorded by the assigned node, `sbc-thm-spreading-finite-etale-galois`.

## New nodes

`lem-sbc-stalk-normalization-depth-two-section-flat`: the formal calculation of Stacks 0EYJ using 0EY6 and 0EY9, ending at flatness on a target neighbourhood. Module `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionFlat`.

`lem-sbc-stalk-normalization-flat-etale`: Stacks 0EY6(3) for the concrete local normalization, with the geometric depth conditions supplied in its hypotheses. Module `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFlatEtale`.

No change records are needed: existing statements and interfaces are unchanged. The second reader has not yet reviewed or delivered this work.

## Second reading by R3

1. **Statements and interfaces.** Compared the assigned module byte-for-byte with the repository version. The target theorem signature and docstring are unchanged. The two added theorem signatures match their DAG `lean.statement` fields; no existing declaration or definition was altered. Verdict: pass.

2. **Proof and compilation.** Compiled all three sandbox modules with `lcompile.py --all`; compilation completed without errors or warnings. The assigned target has no `sorry`; the only remaining holes are the two explicitly named split-off theorems, each a public theorem with a source-backed docstring and matching DAG node. No forbidden declarations or hollow definitions occur. Verdict: pass, subject to the two documented split holes.

3. **Truth and strength of split statements.** The flat-neighbourhood theorem and the flat-to-etale theorem are strictly smaller than the target, retain the hypotheses needed by their stated local arguments, and do not weaken the target. Edge cases described in their proofs (empty source, dimension zero, disconnected finite cover) are compatible with the statements. Searches found no existing library or Mathlib theorem matching either statement. Verdict: pass.

4. **Pruning and proof route.** The target proof uses the normal depth theorem, the new flat-neighbourhood theorem, the elementary open-restriction flatness step, and the new purity theorem. The former direct imports `NormalIntegralGenericHomFull`, `GenericFibreActionExtension`, and `FlatLocalDepthFormula` are removed from the target because they are only used inside the split-off flatness theorem; the DAG proof dependencies are updated accordingly. Verdict: pass; no unit route is bypassed.

5. **DAG and unit consistency.** The target and both split-off nodes record their declarations, statements, source, proof steps, dependencies, and blueprint ancestry. The target remains in unit `sk-prop-input-spreading`; its realized route is preserved. Verdict: pass.

**Changes made during second reading:** added this section only; no Lean code, DAG node, import, or public interface required repair.
