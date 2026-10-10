Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-derived-change-of-rings.json` (split item)
- `dag/nodes/sec-smooth-purity/lem-pur-total-left-derived-localization.json` (statement, Mathlib leaf: `CategoryTheory.Functor.totalLeftDerived`)
- `citations.json`

Attachments: none.

WANTED: none.

No statement error was found. The source item has no exact declaration in `WeilConjectures/`; the imported proof was expanded into the cone argument for clause (1), followed by the localization construction and K-flat resolution comparison for clause (2).

## Review by F1

I read the item source citation in Stacks `sites-cohomology.tex` (Tags 06YT and 06YY) and `derived.tex` (Tag 06XN), and inspected the local Mathlib declaration `CategoryTheory.Functor.totalLeftDerived`. Step 1 uses the definition of K-flatness and the existing tensor-cone two-out-of-three statement; their hypotheses are exactly an acyclic cone and K-flat source complexes. Step 2 uses the existing K-flat resolution theorem and the abstract total-left-derived construction, with the derived-category node supplying the ambient localization. Step 3 uses the same universal-property comparison and the K-flat resolution existence to obtain canonical model independence and compatibility. I checked that the new helper is a general localization theorem, not a restatement of the target, and recorded the Mathlib searches and citations.

## Not duplicates

`lem-pur-total-left-derived-localization` vs `lem-kun-derived-tensor-well-defined`: the former is an abstract localization construction for any derivable functor, while the latter is a scheme-level tensor-model independence statement.

## Second reading by F1

- Item statement: checked against Stacks sites-cohomology Tags 06YT and 06YY and derived.tex Tag 06XN; the ringed-site hypotheses, K-flat hypotheses, change-of-rings target, exact derived functor, and model-independence clauses agree, including the zero complex, a field, the empty site, and degree-zero complexes.
- Step 1: checked against the proof of Tag 06YT and the statements of `def-pc-kflat-complex`, `lem-pc-kflat-resolution`, and `lem-pc-kflat-tensor-cone-two-out-of-three`; replaced an invalid direct claim about $C^\bullet\otimes\mathcal O'$ by the K-flat-resolution comparison square.
- Step 2: checked against Tag 06XN; the localization construction and the exactness argument via shifts and mapping cones are now stated explicitly.
- Step 3: checked against Tag 06YY; replaced “same comparison” and “common refinement” shorthand by the counit and localization-universal-property comparison, including compatibility with a third resolution.
- New node `lem-pur-total-left-derived-localization`: checked against `CategoryTheory.Functor.totalLeftDerived` and its `IsLeftDerivedFunctor` instance in `Mathlib/CategoryTheory/Functor/Derived/LeftDerived.lean`; exact Mathlib leaf, with the recorded searches and declaration line.

Changes made: repaired Step 1's false K-flatness inference, added the required K-flat-resolution citation, made exactness and canonical comparison arguments explicit, and updated `citations.json` to match the repaired dependencies.
