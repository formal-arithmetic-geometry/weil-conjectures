## What changed
Proved the target theorem by constructing the canonical fraction restriction map, using the existing nonvanishing-section trivialization, restriction-torsion lemma, and qcqs clearing-denominators lemma. Added the intermediate module `Sheaf.AlgebraicGeometry.SectionFractionRestrictionMap` for the quotient map construction.

## Proved and sorry left
`exists_sectionFraction_nonvanishing_equiv` is proved. The intermediate theorem `exists_sectionFraction_restriction_map` remains `sorry` as a strictly smaller quotient-map construction and is recorded by node `lem-sc-p1-section-fraction-restriction-map`.

## No longer needed
No stated proof-dependency imports were removed. `WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator` is retained because its section-map and trivialization interfaces are used indirectly by the imported nonvanishing theorem.

## Where the brief, the DAG or earlier work was wrong
The DAG omitted the explicit additive quotient-map construction needed to turn the direct-sum fraction presentation into a map. This was split into the new intermediate theorem above.

## New nodes
`lem-sc-p1-section-fraction-restriction-map` — see its node file.

## Earlier second reading (a previous round; superseded)
The item and intermediate module compile. The item’s hypotheses and conclusion match the node; the new intermediate statement is strictly smaller and is used to construct the canonical map.

## Second reading by D2
1. Compared the delivered item with the repository version: the existing theorem signature is unchanged byte for byte; only proof code and proof-only imports were added. Verdict: pass.
2. Compiled both modules with the launcher. There are no errors or forbidden declarations. The only remaining `sorry` is the named intermediate theorem `exists_sectionFraction_restriction_map`, with its dedicated node and proof docstring. Verdict: pass.
3. Checked the split-off theorem against the canonical restriction-and-division construction in Stacks 01PW. It is strictly smaller than the item, has unchanged hypotheses needed by the proof, and its statement is true. No existing library declaration or Mathlib match was found. Verdict: pass.
4. Checked the proof route and imports. The unit route through the canonical fraction map, restriction torsion, and qcqs clearing denominators is retained. No imported node is unused. Verdict: pass.
5. Checked DAG agreement: the item's proof and proof dependencies include the split node, and the split node's Lean declaration, source, blueprint, and statement agree with the module. Verdict: pass.

Changed only the proof of `exists_sectionFraction_nonvanishing_equiv`, added proof-only imports for its construction, and added the split module and node. No statements or definitions were changed.
