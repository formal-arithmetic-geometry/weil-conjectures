## What changed

Decomposed `zariski_etale_pushed_resolution` into its finite-limit and fixed-augmentation quasi-isomorphism conjuncts, in two new helper modules. The existing theorem's signature is byte-for-byte unchanged. Both helper imports in the item are proof-only `import`s.

The second reader removed unused `HasExt`, additivity, coefficient-sheaf and local-vanishing hypotheses from the new finite-limit helper, and its three unnecessary public imports. Expanded both new helper docstrings into complete sourced natural-language arguments. Corrected the circular DAG proof dependencies and the stale proof plan of the combined theorem. No existing definition or statement was changed, so no change record is needed.

## Proved and sorry left

Hole closed: `zariski_etale_pushed_resolution`, by conjunction introduction from the two components.

Holes added and left:

- `zariski_etale_pushed_resolution_finite_limits`, node `lem-weil-pbc-zariski-etale-pushed-resolution-finite-limits`.
- `zariski_etale_pushed_resolution_quasi_iso`, node `lem-weil-pbc-zariski-etale-pushed-resolution-quasi-iso`.

This is a decomposition, not a completed proof: one upper hole is replaced by two strictly smaller lower holes (net minus one). The combined theorem still depends on `sorryAx` through those helpers. Each remaining hole is exactly a named public theorem with `:= by sorry`; none occurs in data or a definition. All three modules compile locally. Explicit `#print axioms` for all three declarations shows only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.

## No longer needed

No existing import or module was pruned. From the new finite-limit helper removed `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`, `Mathlib.CategoryTheory.Sites.LocallyInjective`, and `Mathlib.CategoryTheory.Abelian.RightDerived`, after removing its irrelevant assumptions.

The old direct `proof_deps` of the combined node are now used through the component nodes: `lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites`, `lem-weil-pbc-site-extension-by-zero-exact`, `def-weil-pbc-sites-and-cohomology`, `def-sp-injective-resolutions`, `lem-weil-pbc-site-sheafification-iso-locally-bijective`, `lem-weil-pbc-sheafification-exact`, and `lem-weil-pbc-site-higher-direct-image-sheafified-presheaf`. They are not globally obsolete; their sourced arguments remain the plan for the unresolved components. No unit realization was removed.

## Where the brief, the DAG or earlier work was wrong

The first worker left the combined node's proof unchanged despite changing its Lean proof, and made each new helper depend on the combined theorem. That circular metadata did not describe a reduction. The corrected combined node depends on the two components; the components carry the original, noncircular finite-limit and homology arguments.

The finite-limit helper had copied every target hypothesis, including irrelevant cohomology data. Its original proof description was too abbreviated; the quasi-isomorphism description omitted the Ext-universe comparison and degree-zero augmentation identification. Both are now expanded. The first report incorrectly presented the decomposition as a proof without explaining its negative net hole count.

## New nodes

`lem-weil-pbc-zariski-etale-pushed-resolution-finite-limits` records finite-limit preservation for the arbitrary open-restriction lift. Its proof factors through the localized etale site over `i(top)`, then uses exact abelian inverse image and exact extension by zero. It does not assume that `i(top)` is terminal, or that this arbitrary lift is representably flat.

`lem-weil-pbc-zariski-etale-pushed-resolution-quasi-iso` records only the quasi-isomorphism conjunct with the original hypotheses and displayed canonical map. Its proof computes section cohomology, applies local vanishing and exact sheafification, and identifies the degree-zero kernel. No change record is required for either new declaration.

## Second reading by S1

1. Compared the item against the repository with `diff`, and mechanically checked the existing theorem signature byte-for-byte: unchanged. There are no changed existing definitions or other delivered existing Lean modules. Verdict: pass.
2. Compiled all three modules through `lcompile.py --all`, and compiled a scratch axiom probe for all three declarations. No errors or non-sorry warnings; only the two reported named theorem holes remain. No forbidden declarations, hollow definitions or witness choices occur. Axioms are the three permitted axioms plus `sorryAx` from the reported components. Verdict: valid decomposition, not an axiom-free target proof.
3. Read both component statements and arguments. Finite-limit preservation is independent of F and hvan, now removed from that helper. The quasi-isomorphism component is strictly one conjunct, retaining exactly the original canonical augmentation. Empty opens and the zero sheaf cause no exception: extension by zero is additive/exact, zero classes lift by zero, and degree-zero homology is handled separately from positive degrees. Searched with leanfinder, loogle, LeanSearch (unavailable: Internal Server Error) and `rg` on Mathlib and the library, and read ZariskiEtaleSheafLeftExact, ZariskiEtaleInclusionMorphismOfSites, SiteExtensionByZeroExact, SiteHigherDirectImageSheafifiedPresheaf, and InjectiveResolutionCohomologyPresheaf. The first requires flatness for set coefficients; the last fixes the Ext universe. No exact helper duplicate or immediate closing proof was found. Verdict: true strict components, still requiring substantial bridges.
4. Read the original node plan and `dag/units/sk-thm-p1.json` realized route. This item is below the unit level; the conjunction split keeps its original two arguments and bypasses no unit realization. Existing public imports support the target signature; newly added helper imports are private to proofs. Removed unnecessary imports of the new finite-limit module; no original module is pruned. Verdict: route preserved, decomposition honestly reported.
5. Compared node statements and `lean.statement` records against Lean. Updated combined `proof`, `proof_deps` and `proof_origin` to conjunction introduction, and component records to the original respective noncircular arguments, with actual search evidence and self-contained statements. New nodes have sources, blueprint provenance, creation records, module/declaration records and status split. Verdict: repaired metadata agrees with the Lean reduction and remaining mathematical plans.

Second reading changed: removed irrelevant finite-limit hypotheses/imports; expanded helper proof docstrings; repaired circular/stale DAG proof metadata, node statements and search records; corrected progress accounting and completed this review. The existing target signature and canonical augmentation remain unchanged.
