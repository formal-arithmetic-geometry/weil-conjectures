## What changed

The original theorem now has a complete Lean proof: form the common prefix from the global-sections unit, the composite direct-image unit, and the inverse normalized composition isomorphism; prove that prefix invertible using direct-image global-sections acyclicity and K-injectivity; identify both precomposed paths using two normalization lemmas; cancel the prefix. Its signature, universes and visibility are unchanged.

Two new modules isolate the left and right path calculations before cancellation. Each states an equality with the same explicit scalar-factor path, for any cochain complex, without a K-injectivity hypothesis. The parent imports these only for its proof. The parent node and the new nodes record precisely this reduction.

`lcompile.py --all` compiled all three modules (9.1 s, 10.6 s, 7.0 s before removing an unused new-module import). No existing module beyond this item is adapted. No definition or target statement changes.

## Proved and sorry left

Closed the original hole: `AlgebraicGeometry.mixedSections_composition_coherence_on_kInjective` (one of one original sorries).

Added, and left exactly `:= by sorry`:

- `AlgebraicGeometry.mixedSections_left_unit_normalization`, in `Sheaf.AlgebraicGeometry.MixedSectionsLeftUnitNormalization`, node `lem-sc-mixed-sections-left-unit-normalization`.
- `AlgebraicGeometry.mixedSections_right_unit_normalization`, in `Sheaf.AlgebraicGeometry.MixedSectionsRightUnitNormalization`, node `lem-sc-mixed-sections-right-unit-normalization`.

This is a decomposition, not an axiom-free mathematical proof: one hole closed, two holes added, net minus one before the ledger's import-closure accounting. The upper theorem depends transitively on the new holes. There are no holes inside definitions, private declarations, or the upper proof. The original statement is not renamed or repackaged as a lower lemma: the two lower statements concern different individual paths, do not assert their equality, do not use K-injectivity, and do not perform cancellation.

## No longer needed

No original import, planned dependency, node or module is pruned. The mixed Leray comparison, normalized direct-image composition equation, and scalar comparison remain needed in the lower normalization calculations. The original acyclicity theorem remains needed directly for cancellation. The unused `GlobalHomPullbackComparison` public import was removed from the new left-normalization module; the new right-normalization module needs it for its statement. Scratch experiments are not part of the delivery.

## Where the brief, the DAG or earlier work was wrong

No false statement or incorrect mathematical step was found. The route is the existing pinned-unit calculation, decomposed into its two path normalizations and its final cancellation. It never asserts that direct image preserves K-injectivity.

The generic pasting and scalar-factor calculations, and the simplified mixed-unit calculation, were explored and compiled separately in scratch. Concrete instantiation in a single proof repeatedly exceeded the 60-second file limit or the local heartbeat limit, especially while identifying global-ring presentations and derived-factor maps. These scratch proofs are not claimed as delivered proofs. The two new nodes preserve the unresolved concrete calculations with their full source and proof in words.

The parent blueprint ancestry points to `lem-sc-mixed-sections-composition-coherence`; the new nodes preserve that ancestry via the present item. No blueprint unit's realized proof step is bypassed.

## New nodes

`lem-sc-mixed-sections-left-unit-normalization`: paste the direct-image composition unit equation, use naturality of the mixed comparison for g, apply its unit equation at Df(K), then apply the unit equation for f at K. Functoriality gives the iterated scalar-factor path. This is one path of the argument, before any cancellation.

`lem-sc-mixed-sections-right-unit-normalization`: cancel only the mutually inverse composition-isomorphism maps, apply the mixed unit equation for fg, then use scalar-composition naturality and `mapDerivedCategoryCompIso_fach` / `mapDerivedCategoryNatIso_fach` to identify the scalar factors. This is the other path, before any derived-unit cancellation.

Both calculations are elaborations of the parent's source, Stacks Project Cohomology, [Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T) and [Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W), together with the named library unit equations. These tags supply composition of derived direct images and global-sections compatibility; the detailed normalization diagram is the project's calculation, not a verbatim Stacks lemma.

Edge cases checked at the statement level: identity morphisms give the identity comparison and factor equations; zero complexes give the same equations on zero objects; empty schemes require no nonemptiness assumption. No cancellation of a potentially noninvertible unit occurs in either new lemma. No flatness, boundedness, or preservation of K-injectivity is assumed, and the two localization universes are independent.

Recorded searches in `searches.jsonl`: LeanSearch for pasted normalized Leray units returned an internal-server-error unavailability; Loogle for right-derived composition found generic comparison and natural-transformation composition lemmas; Mathlib grep for Leray/mixed units and scalar factors found unrelated results. The initial LeanFinder search likewise found generic sheaf-composition/localizer results. No exact mixed unit-normalization statement was found in Mathlib or in the project's Lean modules. These actual searches are recorded in both new nodes.

## Second reading by Q3

1. **Visible declarations and statements.** Compared the delivered parent module byte for byte with the repository version: the existing theorem signature, universes, visibility, and definition references are unchanged. The two added modules contain only the separately named normalization statements; no existing declaration is altered.

2. **Compilation and proof hygiene.** Compiled all three sandbox modules with `lcompile.py --all`; each compiled without errors. The parent theorem has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition. The two split-off normalization theorems intentionally remain named `sorry` theorems, each documented and represented by a DAG node. The parent cancellation uses an explicitly constructed invertible prefix and `cancel_epi`.

3. **Truth and strength of new statements.** Checked the edge cases stated in their docstrings (identity maps, zero complexes, and empty schemes) and verified that neither statement assumes K-injectivity, flatness, boundedness, nonemptiness, or preservation of K-injectivity. Each theorem describes one distinct path after precomposition by `p`; neither restates the parent equality or performs the final cancellation.

4. **DAG and route.** Checked that the parent and both new node files record the exact Lean declarations, proof dependencies, proof origin, source, and split status. The parent proof uses the direct-image global-sections acyclicity dependency and both normalization nodes. The unit route remains the pinned mixed Leray/direct-image composition calculation; no unit step is bypassed. No import was removable: the parent needs both normalization modules, and the right normalization statement needs `GlobalHomPullbackComparison`.

5. **Search and pruning.** Reviewed the recorded LeanFinder, Loogle, LeanSearch, and grep searches; no existing theorem duplicates either normalization statement. No definition or target statement was changed, and no downstream module required adaptation. The only change made during this second reading is this report section; no proof or DAG edits were needed.
