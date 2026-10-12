## What changed
Closed H.exists_mayerVietoris_extPresentation from two single-term comparison statements. Constructed the actual signed free-sheaf complex and proved short exactness from Mathlib. Proved the mapped biproduct additive equivalence, scalar compatibility and product comparison by Ext additivity and associativity. No existing signature or definition changed.

## Proved and sorry left
Closed the original hole in AlgebraicGeometry.Scheme.Modules.H.exists_mayerVietoris_extPresentation. This is a decomposition, not a sorry-free proof: two holes added, H.globalFreeExtComparison (lem-pc-global-free-ext-comparison) and H.openFreeExtComparison (lem-pc-open-free-ext-comparison). Each concerns one term, without a cover or complex. H.openFreeShortComplex_shortExact is proved. No data definition contains sorry, and no arbitrary existential witness is selected to define data: existential comparison witnesses are eliminated only within the proof of the existential target.

## No longer needed
Removed the duplicate private `openSquare_pullback` theorem from `MayerVietorisFreeComplex`; its proof is retained as a local fact inside `H.openFreeShortComplex_shortExact`. No existing imports removed. Removed redundant public Mathlib.Algebra.Category.Grp.Biproducts imports from both new comparison modules. The old proof dependency def-pc-flat-cohomology-comparison remains needed for definitions; it is retained through the new comparison dependencies. No old dependency module becomes unreachable. No extra row-exactness or connecting-square lemma is used here.

## Where the brief, the DAG or earlier work was wrong
The original dependency list did not state the derived open restriction/Ext comparison and its inverse-image naturality. These are now isolated as single-term statements. Checked empty opens, repeated opens, top opens and zero coefficients: the constructions and comparisons remain valid. The unit route is unchanged. The dry-run checker requires a second-reading section before handing to the second reader, contrary to the worker brief; the section is intentionally reserved for the second reader.

## New nodes
lem-pc-global-free-ext-comparison: global cohomology identified with Ext from the actual top-open free sheaf, with scalar and comparison compatibility.

lem-pc-open-free-ext-comparison: the same comparison for one arbitrary open; applied independently to U, V and their intersection.

lem-pc-free-mayer-vietoris-short-exact: actual signed free-sheaf short complex and its proved short exactness, using Mathlib MayerVietorisSquare.


## Earlier second reading (a previous round; superseded)

1. Compared the target module with the repository using diff. Both existing declaration signatures and their docstrings are unchanged; only new private helpers, proof imports and the target proof were added. Restored byte-for-byte whitespace before the target proof delimiter. No existing definition changes or change records are needed.

2. All four modules compile locally in import order without errors or warnings. Scratch copies with #print axioms confirm that the free sheaf, maps, complex and short-exactness theorem use only propext, Classical.choice and Quot.sound. The two named comparison holes and the target additionally use sorryAx, as reported. No forbidden axiom, unsafe, opaque, implemented_by or extern occurs. The sole direct holes are H.globalFreeExtComparison and H.openFreeExtComparison. All objects are actual constructions; comparison witnesses are eliminated inside an existential proof, never selected to define data.

3. Read both comparison statements and their docstring proofs against the definitions of HOver and H.baseChangeLinear. They concern one term and contain no cover or short complex, so neither restates the target. Restriction and extension by zero are exact for abelian sheaves (not arbitrary module pullback); this supplies the derived adjunction. Coefficient naturality and cartesian open identification supply the scalar and comparison equations. Empty opens yield zero Ext and cohomology; repeated opens give the diagonal/negative-diagonal complex; top opens recover global sections; zero coefficients give zero groups in all degrees. Fresh leanfinder, loogle and grep searches used extension-by-zero, freeYoneda and mapFunctor terminology. Mathlib Sites/SheafCohomology/Basic explicitly lists both the terminal and open Ext identifications as TODOs; upstream Clopen only covers a different pushforward comparison with a closedness hypothesis. No exact existing result was found or hole closed in a few minutes.

4. Checked the product equivalences, distributivity and Ext associativity calculations from the top down. The free complex's exactness already takes the short Mathlib MayerVietorisSquare route. Removed redundant public Grp.Biproducts imports from the two comparison modules, since their statements contain no biproduct. The remaining new imports supply signatures or instances, and the target's new plain imports supply proofs. The old comparison-definition dependency remains used transitively and no old module is pruned. Read dag/units/sk-thm-picard-rr.json: its realized fields are unchanged; this below-unit reduction preserves its route.

5. Checked module paths, declaration names and verbatim recorded statements of all four nodes, and matched the target proof steps/dependency union to the actual calls. Repaired both new comparison nodes to cite lem-pc-free-mayer-vietoris-short-exact in stmt_deps, proof_deps and proof-step uses: their signatures and arguments use the concrete free-sheaf construction from that module. Each remaining hole has its source and complete argument in its docstring and node. The three new nodes retain their required creation, source, search and blueprint records.

Second-reading repairs: two redundant imports removed, missing free-construction dependencies added to both comparison nodes, target proof-delimiter whitespace restored, and report pruning/accounting clarified. One original hole is closed and two holes are added: net minus one in this decomposition; the new short-exactness theorem is proved outright. Source checks included [Stacks Tag 01EB](https://stacks.math.columbia.edu/tag/01EB) and [Section 01F7](https://stacks.math.columbia.edu/tag/01F7).

## Second reading by W2

1. Compared every delivered module with the repository. Existing declarations and definitions retain
their original signatures; only proofs, proof imports, and newly delivered modules differ. Verdict:
pass.

2. Compiled all four modules locally. The original direct congruence proof compiles cleanly in the fresh delivery build. The only remaining `sorry`s are the two named comparison
theorems listed above; no forbidden declarations or hollow definitions occur. Fresh scratch
`#print axioms` probes show exactly propext, Classical.choice, Quot.sound for the constructions
and short exactness, with sorryAx additionally for the two holes and the target. Verdict: pass.

3. Checked the split-off statements against their docstrings, DAG nodes, and edge cases (empty,
repeated, top, and zero opens or coefficients). They are single-term Ext comparisons and are strictly
simpler than the Mayer--Vietoris target. Fresh leanfinder (derived sections / extension by zero),
loogle (Ext.mapExactFunctor), grep (extensionByZero / freeYoneda / cohomologyPresheaf), and local
upstream searches found no complete compatible single-term comparison. Verdict: pass.

4. Checked the proof route, imports, and pruning. The free short-complex theorem remains the unit
route; the target uses the two comparison nodes and the concrete free construction. No additional
imports were removable. Verdict: pass.

5. Checked node statements, proof dependencies, proof origins, and realized unit fields against the
Lean proof. The product comparison uses direct congruence and Ext associativity; the older errors.txt
refers to an earlier rewrite-based proof and is not a failure of the current proof. Verdict: pass.

Added this second-reading record. Tried explicit unfolding, rejected it as unnecessarily slow,
and retained the original correct proof. No Lean statement, definition, proof, or DAG route changed.
