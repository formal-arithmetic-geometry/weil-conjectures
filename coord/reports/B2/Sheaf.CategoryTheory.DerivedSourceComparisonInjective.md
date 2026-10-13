## What changed

Replaced the original hole in `CategoryTheory.derivedSourceComparison_injective` with the worker's Ext dimension-shifting proof. The new module `Sheaf.CategoryTheory.DerivedSourceComparisonExtCompatibility` contains the constructed `CategoryTheory.sourceExtMap` and its compatibility theorem. During second reading, proved that compatibility theorem directly from Mathlib's Ext representative formulas and the library's included single comparison. Both modules now compile without holes. All existing signatures are unchanged.

The compatibility module uses a private Ext.Map import and marks the public map `@[no_expose]`; the item uses a private `import all` to unfold its body. This preserves the construction while satisfying the compiler's body-exposure rule. Relocation and exposure are recorded in `coord/changes/sourceExtMap.md` and `coord/changes/derivedSourceComparison_ext_compatibility.md`.

## Proved and sorry left

Closed the original hole `CategoryTheory.derivedSourceComparison_injective` and the worker's proposed split hole `CategoryTheory.derivedSourceComparison_ext_compatibility` (node `lem-sbc-derived-source-comparison-ext-compatibility`). The latter is a new proved intermediate theorem, not a new hole. Holes closed against the repository baseline: one. Holes added: zero. Neither delivered module contains `sorry`. The private helpers `sourceHom_bijective`, `sourceExtMap_comp`, and `sourceExtMap_bijective` are proved. The target's printed axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the unused ExtRightDerivedHom import from the compatibility module; it remains needed in the item. Ext.Map and the dedicated compatibility module are proof-only imports in the item. Removed `lem-weil-pbc-ext-via-injective-resolution` and `lemma-weil-pbc-leray-acyclicity` from the parent's proof dependencies: this route uses dimension shifting instead. Their modules were not imported by the repository version of the item. No realized unit node is bypassed. The compatibility node does not depend on its parent, avoiding a cycle.

## Where the brief, the DAG or earlier work was wrong

The earlier returned delivery put the compatibility result in the item and gave its node a parent dependency, creating a cycle. The relocation and dependency corrections repair this. Earlier Stacks citations for the compatibility result concerned sheaf cohomology and acyclicity rather than the Ext/derived-map formula; the corrected references name the actual Mathlib and library declarations. The worker left the compatibility result open, but it follows directly by applying the bounded-below inclusion to the given equality and postcomposing with common shift and single comparisons.

## New nodes

`lem-sbc-derived-source-comparison-ext-compatibility` states precisely the Ext equality induced by equality of displayed bounded-below derived images. Its statement is strictly an intermediate compatibility result, requires neither the Hom-bijection hypothesis nor acyclicity, and is now proved. Its node records the actual representative calculation and its dedicated Lean module. Change records are `coord/changes/sourceExtMap.md` and `coord/changes/derivedSourceComparison_ext_compatibility.md`.

## Second reading by B2

1. Compared both delivered modules with the repository. The dedicated module is new. The existing theorem `CategoryTheory.derivedSourceComparison_injective` has a byte-for-byte identical signature. The constructed map and compatibility statement retain the worker's signatures and body; no target or definition was weakened. The new module and body-exposure choice are documented in the change records.

2. Compiled both modules in import order through `lcompile.py --all`, without errors or warnings. No `sorry`, axiom, unsafe, opaque, implemented_by, extern, or hollow definition remains. The target and its Ext helpers print only the three permitted axioms. Injective presentations and the Ext/right-derived Hom isomorphism come from proved infrastructure; no arbitrary witness is chosen from an unproved existence theorem.

3. Checked the intermediate compatibility statement at degree zero, zero objects, and arbitrary a (including zero). It expresses functorial compatibility, not injectivity, so no bijection or acyclicity assumption is needed. Its natural-language proof and node match the completed Lean proof. Independent searches with `msearch.py` leanfinder, loogle, and grep, together with `rg` in both library roots, found the Ext representative formulas and a related surjectivity proof but no duplicate of this statement. Reused those formulas to close the hole.

4. Read downward from the target: compatibility converts equality of displayed images to equality of Ext images; dimension shifting proves the Ext map bijective; faithfulness of the inclusion recovers equality. The degree-zero Hom proof and the positive-degree vanishing/right-exact comparison are complete. The old dependencies omitted by this route are all listed above. The unit `sk-lem-failure-field` has empty realized statement/step lists; no realized node is removed or bypassed. Public imports support signatures or the constructed map's type; added proof imports are private.

5. Checked node statements against Lean signatures, the proof dependency unions against steps, and proof origins against the representative and dimension-shifting arguments. Updated the compatibility node and docstring to the actual shorter proof, which does not require the earlier extra shift-compatibility lemmas. The parent still records exactly the ExtRightDerivedHom and compatibility nodes used by its proof. No dependency cycle remains.

Changes made during second reading: proved `CategoryTheory.derivedSourceComparison_ext_compatibility`; corrected its proof description and citations in the module and node; rewrote the report to remove the superseded decomposition claim and document zero remaining holes.
