## What changed
Added prefix and tail contribution intermediate theorems, each isolating one class of labelled junction deletions. The target proof splits the junction sum into these two classes and combines their contributions algebraically.

## Proved and sorry left
`AlgebraicGeometry.Scheme.cechFirstSortingJunctionDeletions` has its local hole closed by a decomposition, not an axiom-clean proof. Holes closed: 1; holes added: 2; net holes closed minus added: -1. Its proof still depends on the two new named holes below. The new intermediate declarations `cechFirstSortingJunctionPrefixContribution` and `cechFirstSortingJunctionTailContribution` remain `sorry`, with nodes `lem-pc-alternating-cech-first-sorting-junction-prefix-contribution` and `lem-pc-alternating-cech-first-sorting-junction-tail-contribution`.

## No longer needed
Removed the redundant plain import `Sheaf.CategoryTheory.SiteCechComplex` from the item and both new modules: it is already a public import of `AlternatingCechSortingOperators`. No old proof-dependency node is unused: sorting operators and the site Cech complex still occur in the expressions and filters. No module is pruned from the targets import closure.

## Where the brief, the DAG or earlier work was wrong
The original one-step proof plan was decomposed into prefix and tail contributions. The first delivery failed to update the item node to this route, and its new docstrings did not give complete takeover proofs; both are repaired below. The source explicitly omits verification of the homotopy formula: the labelled-deletion proofs are agent-written expansions of that formula, not proofs quoted from Stacks.

## New nodes
`lem-pc-alternating-cech-first-sorting-junction-prefix-contribution` and `lem-pc-alternating-cech-first-sorting-junction-tail-contribution` were added under `sec-picard-framework`.

## Earlier second reading (a previous round; superseded)
The target proof compiles and preserves the target signature. The two added statements are strict prefix and tail contributions of the junction sum and are used only to combine the two contributions.


## Second reading by M1

1. Compared the item module with the repository using `diff -u`. Its entire existing
   theorem signature and docstring are byte-for-byte unchanged; only its proof and
   plain imports change. The other two modules are new, with no existing interface
   to alter. No definitions, statement changes, or change records are introduced.
   Verdict: pass.
2. Compiled all three modules locally in import order through `lcompile.py`.
   The only textual `sorry`s are the two public named contribution theorems listed
   above, each exactly `:= by sorry`; there are no data definitions in this delivery.
   No forbidden axiom, unsafe, opaque, implemented_by, extern, or bypass occurs.
   Axiom probes of all three declarations show only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx` (from the two explicitly open statements).
   Verdict: valid conditional proof; not a completed axiom-clean target proof.
3. Read both new statements against the definitions. Prefix deletion is exactly
   r=a by injectivity of sigma, and its two signs cancel. The unique tail deletion
   is r=b+1 with b=tau.symm(sigma a)>=a; moving label b to a gives the next partial
   permutation, with the required negative sign. Checked every permutation and
   stage for label sets of sizes 2, 3, 4 and 5: 1,436 separate prefix/tail coefficient
   identities passed, comparing the resulting labelled tuples. This checks p=0,
   a=0, the last stage, b=a, and every move length in these sizes. The general
   argument is in each docstring; tests are supporting evidence, not Lean proofs.
   Repeated t-values preserve these identities, since comparisons use labels;
   an empty I admits no t. Each statement isolates one deletion class and is
   strictly a part of the original argument, not a restatement. Searched with
   leanfinder, loogle and grep using permutation-cycle and index-map-composition
   terms, and searched both local library roots. Existing sign and projection
   lemmas are ingredients, with no existing full contribution theorem. Verdict:
   true, needed decomposition; two holes remain, not closed in this reading.
4. Read the target proof from its sum partition through the two contributions to
   `Finset.sum_sub_distrib`. No shorter complete library result was found. Removed
   the redundant plain SiteCechComplex import from all three files; kept the
   sorting-operators public import because the signatures use its definitions.
   Both new contribution imports are plain, used only by the item proof. No old
   proof-dependency node is pruned. Read `dag/units/sk-thm-picard-pn.json`: its
   realized arrays are empty, and its Cech/Koszul route is unaffected by this
   below-unit decomposition. Verdict: pass; no unit step is bypassed.
5. Repaired the existing item node's `proof`, `proof_deps`, and `proof_origin` to
   record the actual partition and both contribution declarations. New nodes
   have full quantified statement contexts, exact Lean signatures, docstring
   proofs mirrored in the proof plans, definition dependencies, source and
   agent-origin attribution, creation/blueprint/chapter/unit records, and the
   independent searches. Verdict: nodes agree with the delivered Lean.

Changes in this reading: expanded the two new docstrings into complete
natural-language proofs, supplied self-contained contexts and honest source
attribution for their nodes, updated the item's node to the actual reduction,
removed redundant plain imports, and corrected the report's progress accounting.
No proof body or existing signature was rewritten.
