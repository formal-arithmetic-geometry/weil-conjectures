## What changed

Completed `Sheaf.CategoryTheory.SingleHomologyShiftComparison` without changing any existing signature, visibility, definition, docstring, or import. Retained and cleaned the previous attempt's proved private cochain comparison, added a proved private derived-category comparison, and used both to prove `singleFunctor_homology_shift_comparison`.

The cochain calculation cancels the epimorphic homology projection and uses naturality of cycles maps. The derived calculation uses `singleFunctorsPostcompQIso.hom.comm`, `shiftMap_homologyFunctor_map_Q`, and the definition of `singleFunctorCompHomologyFunctorIso`; the quotient homology comparisons cancel. The final proof uses `map_lift_shiftIso_hom_app` and the composition shift sequence for the fully faithful bounded-below inclusion. This is the existing node's route, so its proof and dependencies remain accurate and need no update.

Single-file compilation passes without warnings. The final normalization unfolds Mathlib's generated instance wrapper `_aux_1`; the auxiliary-name linter is disabled only for this theorem. This is a maintenance sensitivity, not a new assumption or proof hole.

## Proved and sorry left

Closed the one original hole: `singleFunctor_homology_shift_comparison` (node `lem-pc-single-homology-shift-comparison`). Both private helpers, `cochain_comparison` and `derived_comparison`, are proved. No `sorry` remains and no holes were added. This is a proof, not a decomposition. All mathematical comparisons are supplied by Mathlib; no unproved Sheaf theorem is used.

## No longer needed

None. No imports were added or removed, and no existing proof-dependency node or module is bypassed. The sole public import remains necessary for the existing statement.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The previous sandbox attempt had already closed the cochain calculation but left quotient and bounded-below transport unfinished. Its cochain helper had an unused derived-category instance and a flexible-tactic warning; the instance warning is locally suppressed and the tactic warning was fixed. Edge cases degree zero and zero objects require no extra hypotheses and are covered by the same natural comparisons. The unit route is unchanged, and no new nodes or forced adaptations are needed.


## Second reading by D4

1. **Interface unchanged: pass.** Read the complete diff against the repository module.
   The sole existing public declaration, `singleFunctor_homology_shift_comparison`, has
   exactly the original signature, including its category assumptions, arbitrary object
   `Y`, integer `n`, the specified transport `d`, and both canonical comparison maps.
   Its signature was also compared byte for byte by script. Existing definitions,
   visibility, public import, and docstring are unchanged; no change record is needed.

2. **Proof and axioms: pass.** Compiled the supplied module cleanly with `lcompile.py`.
   Compiled a scratch copy with `#print axioms` for
   `cochain_comparison`, `derived_comparison`, and the public theorem: each reports only
   `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry`, new axiom,
   prohibited implementation attribute, or definition containing a hole. Read both
   cancellations in the derived helper: the shift hom is an isomorphism, so cancellation
   is valid; the quotient comparison is canceled with its own inverse. The cochain
   cancellation uses the epimorphic homology projection, not an arbitrary map.

3. **Split statements: pass, none.** No new open statements or nodes are delivered.
   Both private helpers are proved and strictly intermediate: the first is the cochain
   calculation and the second its unbounded derived-category transport. The cochain
   helper uses only the abelian-category assumptions; its unused derived-category
   section instance is locally suppressed. At `n = 0` the same canonical
   shift comparisons cancel, and for a zero object the cycles and homology maps still
   exist and the projection remains epi; no exceptional case is excluded.

4. **Route and pruning: pass.** Read Mathlib's `CochainComplex.singleFunctors`,
   `CochainComplex.ShiftSequence.shiftIso_hom_app`,
   `DerivedCategory.singleFunctorCompHomologyFunctorIso`,
   `DerivedCategory.shiftMap_homologyFunctor_map_Q`, and the lifted single-functor and
   homology definitions on `DerivedCategory.Plus`. The proof realizes exactly these
   constructions. Independent Loogle search for `homologyFunctorSingleIso`, and `rg`
   searches for single/homology/shift comparisons in Mathlib, the upstream library, and
   `lean/Sheaf`, found constituent comparisons rather than an existing replacement for
   the target equation. The only import supplies public signature constants and is
   necessary. The old sole `proof_deps` entry, `def-weil-abstract-derived-category`, is
   still used, so `No longer needed` is complete. Read `dag/units/sk-thm-picard-rr.json`:
   no realized unit node or step is bypassed and no unit route is changed.

5. **DAG agreement: pass.** Read `lem-pc-single-homology-shift-comparison.json` in full
   and its dependency `def-weil-abstract-derived-category`. Its first proof step matches
   bounded-below inclusion and quotient transport; its second matches projection
   cancellation and the literal single-complex coefficient calculation. Its
   `proof_deps` and `proof_origin` remain accurate. No node edits or new node fields
   are required.

**Changed by this reading:** added this independent review report; no Lean proof or
interface changes were retained. Tried replacing the private cochain helper's local
unused-section-variable warning suppression with an explicit `omit`; it compiled
cleanly with standard axioms, but the preflight classified the command as a visible
interface change. Restored the original, correct local suppression rather than
introducing an unnecessary interface-change delivery. Kept the correct mathematical
proof, including its documented generated-instance wrapper dependency. Closed one
original hole, added zero holes; this is a proof, not a decomposition.
