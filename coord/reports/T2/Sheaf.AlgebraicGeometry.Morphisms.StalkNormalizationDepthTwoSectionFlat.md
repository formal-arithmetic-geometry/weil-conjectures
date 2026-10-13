## What changed

Added the proof-only import of `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionFlatCore` and reduced the target theorem to the formal-neighbourhood core theorem. The target proof now unfolds its local definitions and applies the core result; all original hypotheses and the target signature are unchanged.

## Proved and sorry left

The target declaration `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_depth_two_section_flat` is proved from the new core declaration. The new declaration `AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core` remains a single named `sorry`, carrying the formal-neighbourhood calculation described in its docstring and node `lem-sbc-stalk-normalization-depth-two-section-flat-core`.

## No longer needed

No existing proof dependency imports were removed; the target's generic-fibre and normalization dependencies remain part of the stated route and context. No existing nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan compresses the formal-neighbourhood calculation into one very large step. The delivery makes that step explicit as a strictly stronger local core theorem, while preserving the target statement and its unit route.

## New nodes

`lem-sbc-stalk-normalization-depth-two-section-flat-core` is the named intermediate theorem for the completion, split punctured algebra, faithfully-flat descent, and open flat-locus argument. Its module is `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionFlatCore`.

## Second reading by T2

1. Compared the delivered target module with the repository version. The target
   declaration has the same signature byte for byte; only its proof and one
   proof-only import changed. Verdict: pass.
2. Compiled both sandbox modules with `lcompile.py --all`. The target is proved;
   the only remaining `sorry` is the named core theorem, and there are no
   axioms, unsafe declarations, or hollow definitions. Verdict: pass.
3. Checked the core theorem against the target and searched the library and
   Mathlib for an existing declaration. The core removes the generic-fibre
   torsor bookkeeping while retaining the local flatness conclusion, and is
   documented with its Stacks Project source and node. Verdict: pass.
4. The proof follows the formal-neighbourhood core step in the DAG and keeps
   the target's stated route and imports; no unused existing proof dependency
   was removed. Verdict: pass.
5. The target and core node records agree with the Lean declarations and proof
   dependencies. Verdict: pass.

Changed only the target proof/import and the documented split core theorem; no
existing statement or definition was altered.
