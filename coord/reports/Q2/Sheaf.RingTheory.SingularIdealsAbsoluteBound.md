## What changed

Proved `Algebra.singularIdeal_map_le_absolute_of_annihilator_bound` in
`lean/Sheaf/RingTheory/SingularIdealsAbsoluteBound.lean`, preserving its complete signature
and visibility. Added proof-only imports of `Sheaf.RingTheory.SingularIdealsRelativeBound`
and `Sheaf.RingTheory.SingularIdealLocalizationSmooth`.

Apply the existing relative bound, then reduce the absolute inclusion to mapped smooth
localization generators. For each generator f, the relative inclusion and the existing
localization-smoothness theorem give smoothness of B_(dB f) over D. The localization map
D_f -> B_(dB f) gives compatible scalar towers. Mathlib's formal-smoothness localization
base theorem and finite-presentation restriction theorem give smoothness over D_f.
Composition with R -> D_f finishes the generator argument; span and radical monotonicity
finish the ideal inclusion. The node proof and dependencies now record this route.

Validation: the assigned module compiled cleanly through lcompile.py. Both proof-only
imports pass import_direction.py. All new lines are at most 100 characters. The proof
requires no nontrivial ring hypothesis and works with zero or nilpotent generators.

## Proved and sorry left

Closed the sole original hole:
`Algebra.singularIdeal_map_le_absolute_of_annihilator_bound`
(node `lem-weil-pbc-singular-ideals-absolute-bound`).

No sorry remains in the assigned module. No holes, new declarations or nodes were added.
This is a proof from existing statements, not a new decomposition. It still depends on
the existing unproved `Algebra.singularIdeal_map_le_relative_of_annihilator_bound`
(node `lem-weil-pbc-singular-ideals-relative-bound`), which is the next mathematical item;
the absolute theorem is not claimed to have a sorry-free transitive axiom closure.

## No longer needed

None: no original imports were removed and no original proof dependency was pruned.
The absolute step needs no additional prime-support or primewise smooth-composition
statements: it uses the existing relative bound and explicit principal localization
composition. The original absolute node had no named proof dependencies to prune.
The blueprint unit's statement and steps are unchanged.

## Second reading by Q2

1. Compared the delivered module with the repository version. The theorem signature and
   visibility are byte-for-byte unchanged; only proof-only imports and the proof body changed.
2. Compiled the module with `lcompile.py`; it succeeds with no errors. The only `sorryAx` in
   the axiom report comes transitively from the still-open relative-bound theorem. There are
   no new sorries, axioms, unsafe declarations, or hollow definitions.
3. The proof uses existing declarations and adds no statements or nodes. The reductions handle
   zero and nilpotent localizations, and no hypothesis or conclusion was weakened.
4. The route is shorter and explicit: relative containment, localization smoothness, formal
   smoothness under localization, finite presentation restriction, and smooth composition.
   The unit route and its statement remain unchanged; no imports or proof dependencies were
   pruned.
5. The DAG proof, dependencies, and origin match the Lean proof, including the relative-bound
   and localization-smoothness steps. No changes were needed during this second reading.

Changed during second reading: added this review record only.

## Where the brief, the DAG or earlier work was wrong

The original absolute node had a one-sentence proof with no named dependencies, although
the relative bound was already stated in a separate module. Its route is now made explicit
in the DAG and Lean. The original docstring still describes the formerly postponed proof;
its statement, source and blueprint reference are preserved. No mathematical statement
or definition was changed, and no forced adaptations were necessary.
