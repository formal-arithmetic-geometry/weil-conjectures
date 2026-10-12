## What changed

Replaced the target theorem's anonymous proof hole with a complete construction using the stated inverse-image Cech compatibility theorem. Added an import of `AffineCechInverseImage`, which isolates the double-complex comparison as a named intermediate statement.

## Proved and sorry left

Closed the one original hole, `exists_cechBaseChange_cocycle_comparison`. The previously proved `extendedCechCycles` is unchanged. This is a decomposition: one hole closed and one hole added, net zero. The target proof constructs the geometric hypotheses and proves coordinate matching at scalar one before applying the general inverse-image theorem. The added declaration `exists_affineCech_inverseImage` remains `sorry` as a strictly smaller intermediate theorem; its node is `lem-pc-affine-cech-inverse-image`.

## No longer needed

Removed proof-only imports of `FlatCohomologyComparison` (already public through `FlatCohomologyCechBaseChange`), `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray`, and `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech`. Removed duplicate imports of `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde` and `Mathlib.AlgebraicGeometry.Morphisms.Affine`. The direct dependency `lem-sc-cech-spectral` (module `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech`) and `lem-pc-cech-computes` (module `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray`) are no longer used directly by the target proof; they remain in the new general inverse-image theorem’s proof plan. The separated-affine-intersection Mathlib leaf, module pullback quasi-coherence, and flat-cohomology comparison definitions remain used. No whole module is asserted globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The original item’s proof plan omitted a Lean-level declaration for the functoriality of the augmented Cech comparison. This is now split into the named intermediate theorem above.

## New nodes

`lem-pc-affine-cech-inverse-image` records the inverse-image compatibility theorem and its source proof by comparison of augmented Cech double complexes.

## Second reading by T2

1. Compared both delivered modules against the repository: `AffineCechInverseImage` is new; the existing definition and theorem signatures and their docstrings in `FlatCohomologyCechCocycles` are byte-for-byte unchanged. No definitions or public imports of the existing module changed; no change record is needed. Verdict: pass.
2. Compiled both modules in import order with lcompile.py. The only remaining local hole is the named theorem `exists_affineCech_inverseImage`; no forbidden declarations or data holes occur. Explicit scratch-copy `#print axioms` checks show only propext, Classical.choice, Quot.sound for `extendedCechCycles`, and these plus sorryAx for the two comparison theorems. Verdict: pass as a decomposition, not a completed cohomology proof.
3. Read the new theorem and its node against Stacks Tag 01FD, including its comparison-through-a-resolution diagram. This is inverse-image naturality for matching section cocycles and affine-intersection Leray comparisons, a genuine intermediate step: the target separately proves affineness, cover preservation, quasi-coherence, and the tensor-cycle coordinate identity. Checked degree zero, zero coefficient map, empty covers, repeated indices, and zero base ring: no finiteness, flatness, or scalar compatibility between R and S is needed for this equality of underlying abelian cohomology classes. Independent LeanFinder query “Cech cohomology comparison with derived cohomology commutes with morphisms of ringed spaces” returned only sheaf-gluing and coefficient-map lemmas. Broad rg searches in Mathlib, upstream, and lean/ found `cechComparisonMapNaturality` and `moduleCechComparison_natural_affine`, but these concern coefficient maps on a fixed scheme and module-derived cohomology, not the required cross-scheme exact-inverse-image Ext map. No direct replacement was found. The new docstring gives the complete source argument and its node matches its statement. Verdict: pass; this substantial remaining comparison cannot be closed in a few minutes.
4. Reviewed the target top down: it performs the geometric reduction before using the generic comparison, then proves matching coordinates using liftCycles_i and hc at scalar one. Pruned unused and duplicate imports and recompiled successfully. The sk-thm-picard-rr unit record has empty realized slots; this delivery changes none of them and continues the original separated-case Cech route through Leray and inverse-image comparison. Every old proof dependency is either retained or listed under No longer needed. Verdict: pass below the unit level; no unit bypass.
5. Read both node files: the target proof steps and proof_deps match the geometric reduction and comparison application; the new node has its source, proof plan, origin, searches, Lean record, creation record, chapter and unit. The new theorem is genuinely still open and remains recorded as split. Verdict: pass.

Second-reading changes: removed duplicate imports and three unused proof-only imports; clarified pruning and validation here. No proof body, declaration signature, definition, or statement changed. One original hole closed and one intermediate hole added: net zero, decomposition only.
