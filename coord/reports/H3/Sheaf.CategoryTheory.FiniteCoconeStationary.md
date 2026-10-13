## What changed

Completed `CategoryTheory.BigradedExactCouple.finiteCocone_stationary` with its existing
signature unchanged. It uses the proved finite cycle identity and the existing
`finiteBoundary_alphaKernel`, then reuses the alpha cocone iteration theorem and applies
the upper zero and lower isomorphism tail bounds. Added the new proof module
`Sheaf.CategoryTheory.FiniteCycleFormula`; its `finiteCycle_formula` is now proved
by induction using `pageCouple_image_prefix`, derived kernel identities and the
canonical projection recurrence. All added imports are proof-only imports. The returned-delivery repair adds
`import all Sheaf.CategoryTheory.FiniteCoconeLimitBoundaries` to reuse its private
`alphaIter_cocone` and removes the entire duplicate local theorem. The existing
stationarity signature and all other proofs remain unchanged; no other module is edited.

## Proved and sorry left

Closed the original item hole:
`CategoryTheory.BigradedExactCouple.finiteCocone_stationary`.
The second reading also closed the first worker's proposed split-off hole:
`CategoryTheory.BigradedExactCouple.finiteCycle_formula`
(node `lem-sp-finite-cycle-formula`). No new holes remain or are added by this delivery.
The existing dependency `CategoryTheory.BigradedExactCouple.finiteBoundary_alphaKernel`
(node `lem-sp-finite-boundary-alpha-kernel`) still has `sorry` in the repository;
this delivery does not prove it. Thus stationarity is proved relative to that open
statement, and its axiom closure still includes `sorryAx`; this is not a completed
target-closure proof. The item contains one original hole, and closes one of one.

## No longer needed

No original import or old proof dependency is removed: the original dependencies
`def-sp-exact-couple` and `def-sp-convergence` remain used. No module is claimed pruned. The duplicate local `alphaIter_cocone` proof is removed;
the existing theorem in `FiniteCoconeLimitBoundaries` is now used. No original import
is removed in this repair.
Removed the duplicate `FiniteCycleFormula` import and the unused private helper
`prescribed_inclusion_images` from the first worker's sandbox. The retained pullback-square helper is used in the completed induction. The incoming-iterate
recurrence now reuses the existing helper of FinitePageImageLift. The new cycle proof imports
`Mathlib.CategoryTheory.Subobject.Lattice` for `Subobject.pullback_top`.

## Where the brief, the DAG or earlier work was wrong

The maintainer returned the delivery because its private `alphaIter_cocone`
duplicated the existing theorem word for word in `FiniteCoconeLimitBoundaries`.
The repair imports and uses that existing theorem with `import all`, which makes
the private helper accessible within this proof without changing public visibility.
The import-direction check permits this dependency, and both sandbox modules
compile without errors or warnings. The stationarity node now records this reused
module dependency. The second-reading notes below describe the earlier delivery;
the cocone induction now lives only in the imported existing module.

The first worker's report called a one-for-one hole decomposition a proof. The second
reader completed the lower cycle identity, so the delivery now closes the item hole
without adding any lower holes. The initial new node had copied unrelated prior review
records, searches about stationarity instead of its own identity, an overly broad
stationarity proof, and literal Unicode escape sequences in its Lean statement.
These were repaired. The cycle formula is stated in Stacks Tag 011T and its shifted
form in Tag 0AMJ, not directly in the filtered-complex lemma Tag 012W. The literature
checkout is absent locally, so the second reader read the official online sources:
[011T](https://stacks.math.columbia.edu/tag/011T),
[0AMJ](https://stacks.math.columbia.edu/tag/0AMJ), and
[012W](https://stacks.math.columbia.edu/tag/012W).

## New nodes

`dag/nodes/sec-abelian-varieties/lem-sp-finite-cycle-formula.json` records the proved
finite-cycle identity in `Sheaf.CategoryTheory.FiniteCycleFormula`. The node has a
self-contained statement, the actual inductive proof and dependencies, actual recorded
Mathlib searches, H3 creation provenance and the verbatim Lean signature. No statement
or definition change record is needed. Its chapter and unit follow the parent item's
existing classification; that unit's `realized` statement and step lists are empty,
so no realized unit step is bypassed or removed.

## Earlier second reading (a previous round; superseded)

1. Compared the item module with the repository using `diff`. The existing public
   signature and visibility are byte-for-byte unchanged; no definitions are changed,
   no hypotheses are added, and no conclusions are weakened. The additional module
   is new. Restored the existing node's Lean signature from the repository verbatim.
2. Compiled both modules locally in import order through `lcompile.py`, with no errors
   or warnings. Neither delivered module contains `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, or `extern`; there are no new data definitions or existence choices
   in definitions. The image/inclusion witnesses are used only inside a theorem proof.
   Scratch-copy `#print axioms` checks are recorded below; delivery also runs the
   maintainer's all-declaration axiom probe.
3. Checked the proposed finite-cycle identity against Stacks 011T and 0AMJ, its exact
   bidegrees, the zero page (top), the first page (kernel of f followed by g), and the
   zero category. Proved the identity instead of leaving it split off. Searched the
   library and Mathlib with different exact-couple/image queries; no matching formula
   exists. The Loogle qualified identifier was unknown and LeanSearch was unavailable;
   these limitations are recorded, not treated as successful searches.
4. Read the stationarity proof from its conclusion downward. Its two bounds operate
   on total degrees p+q and p+q+1, and the explicit max/toNat bound covers negative
   bidegrees and zero natural thresholds. The cocone telescoping induction is valid
   at zero and at successors. The new cycle proof uses existing proved prefix and
   kernel identities. All imports are needed and proof imports are plain. No old
   proof dependency is removed and the unit's empty `realized` records are retained.
5. Rewrote the item node's proof steps to match the finite formulas, bound and cocone
   argument. Rewrote the new node to match the completed induction and its dependencies;
   fixed its source/provenance/search records and removed copied review assertions.

Changes by the second reader: proved `finiteCycle_formula`; removed a duplicate import
and unused helper; added the pullback-top proof import; expanded the cycle docstring;
repaired both nodes and made the report's hole accounting explicit.

Axiom-check result: `finiteCycle_formula` uses only `propext`, `Classical.choice`,
and `Quot.sound`; `finiteCocone_stationary` uses those three plus `sorryAx` from the
existing finite-boundary dependency. Both scratch-copy checks compiled cleanly.


## Second reading by H3

1. PASS: compared the delivered stationarity module against the repository with diff.
   Its existing signature and visibility are byte-for-byte unchanged; the only changes
   are proof imports and replacement of its sorry proof. FiniteCycleFormula is new.
   There are no data definitions or signature changes and no change records are needed.
2. PASS: compiled both modules in import order through lcompile.py without errors or
   warnings. Scanned all delivered Lean for forbidden declarations and sorry: none.
   Scratch copies with #print axioms confirm finiteCycle_formula uses only propext,
   Classical.choice and Quot.sound. finiteCocone_stationary additionally uses sorryAx
   through the already-open finiteBoundary_alphaKernel dependency. This closes the one
   original item hole and adds zero holes; it does not complete the target axiom closure.
3. PASS: there are no split-off statements left with sorry. Read the new cycle formula
   and its proof against Stacks Tags 011T and 0AMJ, including page zero, page one,
   arbitrary negative integer indices and the zero category. Its source and node match.
   Fresh grep, LeanFinder and qualified Loogle searches found no existing finite-cycle
   formula. Loogle finds map_pullback for an already-given pullback square; the local
   helper additionally constructs the factorization from equality of subobjects.
   Library search found incomingAlphaIter_succ duplicated from FinitePageImageLift;
   removed the duplicate and reused that existing private theorem with import all.
4. PASS: followed the stationarity conclusion back through the two finite formulas.
   The max of toNat bounds handles negative bounds and r=0; incoming sources are on
   diagonal p+q+1 and cocone kernels on diagonal p+q. The cocone iteration theorem
   is reused from FiniteCoconeLimitBoundaries. All imports support the signatures or
   proofs, and added imports are proof-only. No old proof dependency is removed,
   no module is pruned, and the unit's empty realized records are unchanged.
5. PASS: read both delivered node records against the Lean proofs. The stationarity
   node records the reused cocone helper's module; added the reused recurrence's node
   lem-sp-finite-page-image-lift to the new cycle node's first step and proof_deps.
   The new node has the required provenance, source, searches and verbatim signature.

Changes in this reading: removed the duplicate incomingAlphaIter_succ helper,
added a proof-only import all of FinitePageImageLift and qualified its use,
updated the cycle node's proof dependencies, and refreshed this review report.
