## What changed

Replaced the proof of `AlgebraicGeometry.Etale.finiteEtaleTrace_localization_of_localSums` in `Sheaf.AlgebraicGeometry.FiniteEtaleTraceLocalization` by a reduction to the existing section-descent uniqueness theorem and a transported section formula. The private helper `localSum_section_formula` is proved by naturality and evaluation of a finite sum. The new module `Sheaf.AlgebraicGeometry.FiniteEtaleTraceLocalizationSectionFormula` states the remaining transport step. Existing public signatures and definitions are unchanged.

Updated the item node's `proof`, `proof_deps`, and `proof_origin` to follow this route. The second reading retained the directly used local-sum predicate and inverse-image restriction dependency, corrected the description of section descent, removed redundant direct imports of `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` from both modules, and corrected the new node's prose to match its Lean statement (which requires étaleness, not finiteness).

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Etale.finiteEtaleTrace_localization_of_localSums`, node `lem-weil-pbc-finite-etale-trace-localization` (one of one original holes).

Hole added: `AlgebraicGeometry.Etale.finiteEtaleTrace_localization_section_formula`, node `lem-weil-pbc-finite-etale-trace-localization-section-formula`. Its entire proof is `by sorry` in its own module, with a source and natural-language proof in its docstring. There are no remaining holes in the item module.

This is a decomposition: one hole closed, one added, net zero holes. The upper theorem still depends on `sorryAx`, including open dependencies of section descent; it is not claimed to be axiom-free. The private helper is axiom-free apart from `propext`, `Classical.choice`, and `Quot.sound`. No definitions or arbitrary witness constructions were added.

## No longer needed

Removed direct imports: `Sheaf.Paper.FiniteEtaleEtaleLocalSplit` from the item module, and the redundant `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` imports from both modules. The latter is already publicly supplied by `FiniteEtaleTraceLocalSums`. No public import was removed.

Old direct proof dependencies no longer in the item node:

- `def-pc-fibre-product`
- `def-weil-closed-immersion`
- `def-weil-open-immersion`
- `def-weil-pbc-abelian-etale-sheaves`
- `def-weil-pbc-etale-site`
- `lem-weil-pbc-cartesian-square-pasting`
- `lem-weil-pbc-etale-base-change-finite-limits`
- `lem-weil-pbc-etale-composition-cancellation`
- `lem-weil-pbc-etale-covering-base-change`
- `lem-weil-pbc-finite-etale-etale-local-split`
- `lem-weil-pbc-finite-morphism-permanence`

These are removed from the item's direct route; several remain necessary transitively through section descent or the transport lemma. No claim is made that any of these modules disappears from the targets' full import closure. The local-sum predicate and inverse-image restriction remain direct dependencies because the written proof uses them.

## Where the brief, the DAG or earlier work was wrong

The earlier returned delivery omitted the item node and retained obsolete proof metadata. The repair report called the transport node existing, but it is new relative to the repository baseline. It also described the upper hole as proved without counting the new lower hole. The item metadata incorrectly said section descent chooses a split test object; its proof only uses the uniqueness clause of the characterized section. The new node's prose originally imposed finiteness absent from its Lean statement. These report and metadata faults are corrected here.

## Second reading by N3

1. Compared each delivered module against the repository. The item theorem signature is byte-for-byte identical, including all hypotheses, let-bindings, projection conditions and conclusion; its existing docstring is unchanged. The other module and its node are new. No target, definition, existing statement or public import changed; no change record is needed. Verdict: pass.

2. Compiled both modules in import order through `lcompile.py`, including after import cleanup: no errors or warnings. Searched the delivered sources for forbidden constructs and holes; the only `sorry` is the named transport theorem. Scratch `#print axioms` checks show only `propext`, `Classical.choice`, `Quot.sound` for the private helper, and those axioms plus `sorryAx` for the upper and open transport theorems. The upper proof uses section-descent uniqueness on two genuinely verified candidate formulas, then cancels the restriction isomorphism; it chooses no arbitrary witness data. Verdict: pass as decomposition, not a completed axiom-free proof.

3. Read the transport theorem and its complete docstring argument. It concerns a single trace and one supplied splitting, not existence of splitting covers or uniqueness by descent, so is strictly a part of the upper argument. Projection identities uniquely determine the pasting map and transport each section; naturality and preservation of sums give the formula. Checked identity localization, a single sheet, empty index, empty test object and disconnected bases: the formula reduces to naturality or the zero sum, without any nonemptiness or constant-degree assumption. No finiteness of f is needed for this conditional splitting formula. Independent leanfinder, loogle and grep searches used different queries; only general naturality/pullback and unrelated algebra traces appeared. Read the surrounding library and upstream étale sources: no independent theorem closes this formula, and later trace-family compatibility imports this item, so cannot supply a shorter acyclic route. Verdict: true and useful remaining split; not closed in this review.

4. Read from the upper target down to the two used lemmas. The private local formula already takes the direct naturality route. Retained the required public imports and removed redundant proof imports. Listed every old direct proof dependency absent from the replacement route above. Read `dag/units/sk-thm-p1.json`: neither this item nor the new transport lemma is a realized unit statement or step; the curve-calculation and trace-splitting route is preserved, with only this auxiliary argument decomposed. Verdict: pass; no unit-level pruning.

5. Compared the item and new node metadata against the Lean. The item now records section descent, the transport formula, the local-sum predicate and restriction isomorphism; its proof-dependency list is the union of its steps' uses. The new node has its source, complete proof plan, searches, status, creation and blueprint records, chapter/unit, and Lean declaration record. Corrected its prose statement to match the stronger conditional Lean formula without a finiteness hypothesis. Verdict: pass after the metadata repairs described above.

## New nodes

`lem-weil-pbc-finite-etale-trace-localization-section-formula`, in `dag/nodes/sec-proper-base-change/`, records the remaining algebraic transport step in the new module `Sheaf.AlgebraicGeometry.FiniteEtaleTraceLocalizationSectionFormula`. It has one named hole, a source and proof docstring, and independently repeated searches. No change records or forced adaptations.

The source characterization was checked against [Stacks, Tag 03SH](https://stacks.math.columbia.edu/tag/03SH); the transport argument is the explicit naturality and pullback-pasting step extracted from that route.
