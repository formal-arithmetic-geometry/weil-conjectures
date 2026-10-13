## What changed
Added two proof interfaces for localization equivalences and additive chart section identifications, then combined them in the target theorem.

## Proved and sorry left
The target `exists_chart_completed_localizations` is reduced to the two strict intermediate interfaces. Sorries remain in `exists_chart_completed_localizations_alpha` and `exists_chart_completed_localizations_d`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The original theorem had no usable proved construction; its proof was decomposed into the two independent affine constructions required by the source argument.

## New nodes
`lem-sbc-punctured-completion-chart-completed-localizations-alpha` and `lem-sbc-punctured-completion-chart-completed-localizations-d`.

## Earlier second reading (a previous round; superseded)
The decomposition uses two strict intermediate interfaces: alpha supplies only localization equivalences and scalar compatibility; d supplies only additive section maps and their three formulas. The target combines them without changing its statement.

## Second reading by E1

1. Compared the delivered target module with the repository version. Its theorem
   signature is byte-for-byte unchanged; only proof imports and the proof body were
   added. The two auxiliary modules and node records are new split-off declarations.

2. Compiled all six sandbox modules with `lcompile.py --all`. Compilation succeeds.
   The target has no `sorry`; the two named auxiliary interface theorems retain their
   documented `sorry`s. No forbidden declarations or hollow definitions were added.

3. Checked the split statements against their Lean declarations and the edge case
   of an empty finite chart. The alpha node now states only the linear equivalence
   and scalar compatibility supplied by its theorem; the d node takes alpha as an
   input and states only the additive equivalence and its three formulas. Both are
   strict, true reductions of the target and have source and proof documentation.

4. Read the proof route and imports. The target combines exactly the alpha and d
   interfaces, while the unit's affine localization and pullback route remains in
   both node proofs. No import can be removed: SectionModules supplies every type
   and both auxiliary interfaces are used by the target proof.

5. Verified that the DAG `lean` records, theorem signatures, proof dependencies and
   proof origins agree after the statement corrections. No existing declaration or
   definition was changed.

Changed the two auxiliary docstrings to give complete construction arguments, and
corrected the two new node statements to match the actual staged interfaces. The
target hole is closed; the two auxiliary holes remain as the named split-off
theorems above. No modules were pruned.
