## What changed

Recovered the complete canonical-cycle argument from the saved sources of
commit b14d83238090ab08de9d5afa27b9da5626317e44, supplied in the route note.
The delivery contains exactly four Lean modules:

- `Sheaf.CategoryTheory.Abelian.DerivedBottomCycleTransport`: closes the
  original cycle-transport theorem using the three proved constituents.
- `Sheaf.CategoryTheory.Abelian.DerivedBottomInclusion`: constructs the
  concrete bottom-homology inclusion and proves its factorization formula.
- `Sheaf.CategoryTheory.Abelian.DerivedCyclesMap`: constructs the actual
  cycle chain map and its localization, and computes its homology.
- `Sheaf.CategoryTheory.Abelian.DerivedCyclesUnitNaturality`: proves the
  actual-unit equation, including bounded-below/unbounded compatibility.

The original theorem signature and the complete definition of
`CategoryTheory.Functor.rightDerivedBottomToSingleIso` are byte-for-byte
unchanged. No target statement, existing definition, or existing public import
changes. The two new imports of the item's module are private proof imports.
The three support modules have their own node records and complete proofs.
The target node's proof, proof dependencies and proof origin now follow the
recovered argument. Historical authorship remains attributed to R2; new-node
delivery attribution is S3. Historical review and coordination state are not
restored. No change record is needed because no existing interface changes.

The unrelated `ProperFlatOpenSquareMateIso.lean` edit rejected in
`coord/returns/XR54ac40b180b6708e.md` is omitted entirely. The full affine
upstream bypass in the route note is outside this delivery's generic theorem.

## Proved and sorry left

Closed the item's sole original hole:
`CategoryTheory.Functor.rightDerivedBottom_cycle_transport`
(`new-lem-pc-derived-bottom-cycle-transport`).

Recovered three completely proved constituent statements:

- `DerivedCategory.Plus.single_map_bottomHomologyInclusion`
  (`new-lem-pc-derived-bottom-inclusion`).
- `DerivedCategory.cyclesDerivedMap_homology`
  (`new-lem-pc-derived-cycles-map-homology`).
- `CategoryTheory.Functor.rightDerived_cycles_unit_naturality`
  (`new-lem-pc-derived-cycles-unit-naturality`).

Holes closed: one. Holes added: zero. Sorries left in all four delivered
modules: none. No intermediate theorem is handed on unproved.

Local compilation with the prescribed `lcompile.py --all` command passed
without warnings: bottom inclusion 2.0 s, cycles map 1.7 s, unit naturality
3.8 s, cycle transport 3.8 s. This compiles individual files in dependency
order against the sandbox overlay, without building the library.

A fresh compiler probe in the item's source checks all four theorem names,
`DerivedCategory.cyclesChainMap`, `DerivedCategory.cyclesDerivedMap`,
`DerivedCategory.Plus.bottomHomologyInclusion`, and
`CategoryTheory.Functor.rightDerivedBottomToSingleIso`. Each lists only
`propext`, `Classical.choice`, and `Quot.sound`. The probe was removed from
the delivered source; its output is in `scratchpad/recovery-axioms.log`.

Edge cases: the constituent proofs work for every integer degree, including
negative degrees, and use no nonzero-object hypothesis. At a zero map the
factorization coefficient is zero by functoriality. On a single object in
degree n, the quotient and localization comparisons are the specified single
comparisons, so the same factorization recovers its map. The unit-naturality
statement allows arbitrary q and arbitrary bounded-below M, and omits the
left-exactness assumption; concentration is used only for the final bottom
factorization. All objects are constructed from explicit maps and inverses,
with no choice of a witness of an unproved existence theorem.

## No longer needed

Removed the private proof import
`Sheaf.CategoryTheory.Abelian.DerivedBottomComparison` from the item's module.
Removed `new-def-pc-derived-bottom-comparison` from the target node's
`proof_deps`; the complete bottom comparison is not applied in this argument.
It remains an unchanged statement dependency and remains available to other
consumers. No existing module or node is deleted, and no global pruning of
that module is claimed.

The recovered proof uses the bottom inclusion, cycle-map homology formula,
actual-unit naturality, shifted-single normalization, and bounded-below/
unbounded compatibility. Both new private imports are used. No further
imports, nodes or modules in the existing plan can be removed for this item.

## Where the brief, the DAG or earlier work was wrong

The route note is correct: the current statement has a complete proof, and
another truncation-normalization leaf is unnecessary. The rejected unrelated
geometric consumer adaptation does not belong in this recovery.

The historical bottom-inclusion and cycle-map node records cited
`def-pc-derived-category`, which describes sheaves of modules on a scheme.
Their statements concern arbitrary abelian categories. In the restored new
records their statement and proof citations now use the existing Mathlib leaf
`def-weil-abstract-derived-category`. Their mathematical and Lean statements
are unchanged. No existing node's statement is changed.

The previous item's proof docstring said that shifted-single normalization
was not used. The recovered proof uses that proved normalization internally
to establish naturality of the actual single-unit homology map. Its conclusion
still stops before composing with the shifted-single comparison, exactly as
the original theorem requires. The docstring and DAG proof describe this.

The Stacks sources were checked directly: Tag 05TC (2) provides the derived
upper-truncation comparison using a distinguished triangle and lower-degree
vanishing; Tag 05TD (3) gives the normalization of the degree-zero unit for a
left-exact functor. The explicit canonical-map calculations are the complete
R2 proofs recovered here, using the existing Lean comparison APIs. Sources:
https://stacks.math.columbia.edu/tag/05TC and
https://stacks.math.columbia.edu/tag/05TD.

The unit record `dag/units/sk-thm-picard-semicon.json` and its realized route
are unchanged. Searches of Sheaf and WeilConjectures found no duplicate of
the three recovered formulas. Fresh LeanFinder, Loogle and Mathlib grep
searches found constituent homology and truncation APIs, without an exact
replacement for the current canonical-cycle equation.

## New nodes

`new-lem-pc-derived-bottom-inclusion` records the constructed inclusion from
the single bottom-homology object and its factorization theorem. Its inverse
double identification, inverse lower projection and upper inclusion are the
actual maps canceled by the target's concrete comparison. Its proof is complete.

`new-lem-pc-derived-cycles-map-homology` records the chain map with cycle
inclusion in degree n, its specified localization, and the exact quotient
formula on homology. This fixes the coefficient needed for factorization.
Its proof is complete.

`new-lem-pc-derived-cycles-unit-naturality` records naturality for that cycle
map followed by any q into the bounded-below category, with actual units and
their compatibility. This supplies the target's cycle prefix before the
truncation cancellation. Its proof is complete.

All three nodes are recovered constituent results, strictly parts of the
argument, with no remaining hole. No change records are added.

## Second reading by S3

1. **Visible changes.** I diffed the delivered item module against the repository version and checked all three added support modules are new files. The existing theorem signature and `rightDerivedBottomToSingleIso` definition are unchanged byte for byte; no target statement or existing declaration was altered. Verdict: pass.

2. **Proof and axioms.** I compiled all four modules with `lcompile.py --all`; compilation completed without errors or warnings. The delivered files contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The saved axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound` for the four recovered theorems and the relevant definition. Verdict: pass.

3. **Split statements.** I read each new node and its Lean declaration, checked the statements on arbitrary integer degrees and zero-map/single-object cases, and searched the existing Sheaf/WeilConjectures sources for duplicates. The three statements are strictly intermediate constituents required by the final factorization, have complete docstrings and DAG records, and add no hypotheses or weakened conclusions. Verdict: pass.

4. **Route and pruning.** The proof follows the unit route through explicit bottom inclusion, cycles-map homology, actual-unit naturality, and the double-truncation comparison. The old bottom-comparison import and dependency are unused and are recorded under `## No longer needed`; all remaining imports are used. The unit's realized route is unchanged. Verdict: pass.

5. **DAG agreement.** I checked the target and three new node records against the declarations, proof dependencies, source notes, and proof origins. The node records identify the exact modules and declarations, and the target proof dependencies match the imports and applications in the final proof. Verdict: pass.

I changed only this report section; no Lean code, node statement, or import was changed during second reading.
