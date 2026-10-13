## What changed

Proved `completedRingMap_kernel_torsion` from a finite-generator local torsion lemma and a proved ideal-power annihilation argument. Added `CompletedMatchingRingMapKernelLocalTorsion` with the localization step left as a named theorem. Added the required proof imports. The Mathlib finiteness import and the new local-torsion import are private to proofs; the existing public matching-map import is unchanged.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.CompletionGluingData.completedRingMap_kernel_torsion`.
Added one hole: `AlgebraicGeometry.Scheme.CompletionGluingData.completedRingMap_kernel_local_torsion` remains `sorry` (node `lem-sbc-completed-matching-ring-map-kernel-local-torsion`).

This is a decomposition: one original hole closed, one lower hole added, net zero. The generic ideal-power annihilation helper is fully proved; the item still depends on `sorryAx` through the localization lemma.

## No longer needed

No existing import or module is pruned. Removed from the parent node's direct `proof_deps`: `def-sbc-completed-matching-ring-map`, `def-sbc-punctured-completion-matching-sections`, `def-weil-finite-integral-morphism`, and `lem-weil-pbc-formal-glueing-H0-localization`. These remain in the statement context or in the new localization node's route; they are not removed from the overall argument. The parent now directly uses the new local-torsion node and Noetherian finite generation. The Mathlib finiteness import was changed from `public import` to `import`, because only the proof needs it.

## Where the brief, the DAG or earlier work was wrong

The planned localization argument requires a separately stated local annihilation result before the elementary ideal-power argument can be expressed in Lean; this was split as the new node above.

## New nodes

`lem-sbc-completed-matching-ring-map-kernel-local-torsion` is the localization component of the proof; its change is represented by the new module `Sheaf.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapKernelLocalTorsion`.


## Second reading by M1

1. Compared the entire delivered parent module with the repository version using
   `diff -u`. The existing declaration `completedRingMap_kernel_torsion` has its
   signature byte for byte unchanged, including universes, Noetherian and local
   hypotheses, the exact punctured-open hypothesis, both finite morphisms, the
   overlap datum, and multiplication through `D.baseMap ≫ pushout.inl`. No existing
   definition changed, no target changed, and no change record is required.

2. Compiled both delivered modules in dependency order with `lcompile.py --all`.
   Both compile without warnings after changing `letI` to `let`. There is exactly
   one remaining `sorry`, in the new named public local-torsion theorem; no axiom,
   unsafe declaration, opaque declaration, implementation override, extern, or
   hollow definition was added. In a scratch copy, `#print axioms` for the private
   ideal-power helper gives only `propext`, `Classical.choice`, and `Quot.sound`.
   The parent and the local theorem additionally have `sorryAx`, as expected for
   this decomposition. Removed the scratch copy before delivery.

3. Read the new theorem against the explicit matching ring and pushout comparison
   definitions and the sources [05ER](https://stacks.math.columbia.edu/tag/05ER),
   second paragraph, and [0BLH](https://stacks.math.columbia.edu/tag/0BLH), the affine
   chart construction. Also read [05EC](https://stacks.math.columbia.edu/tag/05EC):
   it concerns torsion base change, not the local comparison, so corrected the new
   theorem's citation to 05ER/05EP/05EQ applied in 0BLH. The finite generating family
   exists by Noetherianity; the conclusion is individual generator powers, not a
   common ideal-power annihilator. The parent genuinely proves the remaining
   algebraic step by placing the generators in the radical of the annihilator of
   the cyclic submodule and applying `Ideal.exists_pow_le_of_le_radical_of_fg`.
   Thus this is the localization component plus a proved algebraic reduction,
   rather than a one-application renamed copy of the item. Checked empty generator
   families (maximal ideal zero), an empty punctured open, nilpotent generators,
   zero chart rings, and `x = 0`; none needs an added nonzero or nonempty assumption.
   Expanded the new docstring with the sheaf equalizer, flat completion, pushout
   identification, compatibility of the two factors, localization equality
   criterion, and those edge cases, and added its missing blueprint marker.
   Ran fresh leanfinder, loogle, grep, and leansearch queries, recorded in the new
   node; leansearch is explicitly unavailable (HTTP 500), not evidence of absence.
   Local `rg` on Sheaf and the upstream algebraic-geometry source found the proved
   `exists_unique_bijective_h0_localization`, the private `prime_kernel_torsion`,
   and `idealPowerTorsion_iff_localMap_bijective`. Their statements do not provide
   the scheme matching-ring/H0 identification. The holed punctured chart theorem
   is also not the completed pushout comparison. No shorter ready-made proof or
   duplicate of the new scheme statement was found. The lower lemma is not a
   few-minute closure: it needs the scheme-to-module interface and remains open.

4. Read the parent route and `dag/units/sk-prop-input-spreading.json`, including
   `realized`. This change is below the unit level and keeps its formal-gluing
   localization route; no realized unit node is bypassed. The helper uses the
   existing Mathlib radical-power lemma directly, and its import is now a plain
   proof import. The two remaining imports of the parent are needed for its
   public statement and the lower theorem used in its proof. No old module can
   be pruned from the overall route. Updated `No longer needed` to name every
   removed direct dependency, distinguishing delegation from module pruning.

5. Compared both node records with the Lean declarations. The existing node's
   statement and Lean signature are unchanged. Replaced its copied full informal
   proof by the actual two-step reduction: local generator torsion, then the
   proved radical/annihilator argument. Set `proof_deps` to the union of those
   steps' uses and updated `proof_origin`. The new node now introduces all its
   objects and hypotheses, has the exact Lean signature, source, full proof step,
   dependency union, creation and blueprint records, and actual search results.
   No data is chosen from an unproved existence statement in a definition.

Changes made in this reading: proof-only import visibility, the `let` linter fix,
removal of a redundant final obtain/refine block, the new theorem's proof
explanation and citation, DAG proof-route and search records, and this report.
No additional hole was closed beyond the first worker's decomposition.
