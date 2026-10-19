# Worker report

## Files written

- `item.json`: split statement `lem-trf-universal-injective-check-stalks`.
- `lem-trf-localization-exact-for-modules.json`: Mathlib leaf, `LocalizedModule.map_exact`.
- `citations.json`: verbatim proof-step citations.

## Attachments

None.

## WANTED

None.

## Not duplicates

- `lem-trf-localization-exact-for-modules` vs `lem-sc-graded-localization-exact`: the new node covers arbitrary module sequences localized at an arbitrary multiplicative subset; the existing node is restricted to graded modules and also takes degree-zero parts.
- `lem-trf-localization-exact-for-modules` vs `lem-weil-pbc-localization-tensor-product`: the new node is exactness of arbitrary localized module sequences, whereas the existing node is a tensor-product localization comparison.

## What was checked

The item source and proof were read in `literature/stacks-project/algebra.tex`, Tag 05CL (`lemma-universally-injective-check-stalks`), including its displayed identities and both implications. I also read the current `main-20261015` blueprint ancestor `lem-trf-local-term-locality`, the chapter `sec-trace-formula`, and the unit `sk-i-curve-zero`. The item statement agrees with the source's implication (1) iff (4), retaining the exact prime and contracted-prime hypotheses.

Step 1 uses the statement of `lem-weil-pbc-localization-tensor-over-base` for the localization of the tensor map, and the module-localization definition for the fraction map. The remaining identification with tensoring over `R_p` is written explicitly by the two inverse fraction maps; the spectrum node supplies the meaning of the primes and contraction. Step 2 applies the new exact-localization leaf to the kernel sequence and uses the existing maximal-localization bijectivity leaf exactly on the zero map from the kernel. Step 3 applies the same exact-localization statement to the injective tensor sequence and tests an arbitrary `R_p`-module after restriction of scalars; the localization definition supplies `L_p=L` and the induced map formula. Every cited node was opened and its quoted sentence was copied verbatim into `citations.json`.

I checked hypotheses at each use: `M` and `M'` are A-modules, so their tensor products over R are A-modules; `q` is prime in A and `p=q∩R`, hence elements of `R\\p` map into `A\\q`; the kernel is an A-submodule; and a maximal ideal of A is among the primes covered by the hypothesis. The zero ring and zero modules make the implication vacuous or immediate, and identity and zero maps satisfy the criterion. The Mathlib leaf was searched with LeanFinder, Loogle, grep, and LeanSearch and matched `LocalizedModule.map_exact` in `Mathlib/Algebra/Module/LocalizedModule/Exact.lean` (lines 37 and 56).

## Review by Q79

I reread the imported item, the Stacks Tag 05CL source, the blueprint ancestor, all three item proof steps, and the full statements of every cited node. I verified that Step 1 takes only the localization-tensor comparison and the explicit fraction definitions from those nodes; Step 2 takes exactness after localization and the stated maximal-localization bijectivity criterion; Step 3 takes exactness after localization and the stated localization-map formula. The new Mathlib leaf was checked against the source declaration and is strictly smaller than the item. The item keeps the source's hypotheses and conclusion, and no proof fact is hidden behind an uncited tag. I corrected the imported metadata to this item's Q79 ownership, supplied the missing proof, and recorded the required Mathlib leaf and citations.

## Source error

None found.

## What could not be finished

Nothing.
- `lem-trf-localization-exact-for-modules` vs `lem-pc-elementwise-fp-module-equiv-descent`: the new leaf states exactness of arbitrary module localization; the existing node concerns descent of elementwise finite-presentation module equivalences.
- `lem-trf-localization-exact-for-modules` vs `lem-pc-tensor-tail-colimit-elementwise`: the new leaf states localization exactness; the existing node concerns elementwise tensor-tail colimit calculations.
- `lem-trf-localization-exact-for-modules` vs `lem-weil-pbc-base-change-diagram-elementwise`: the new leaf states exactness after localization; the existing node concerns an elementwise base-change diagram.
- `lem-trf-localization-exact-for-modules` vs `lem-weil-pbc-colimit-flat-relation-descent-elementwise`: the new leaf states exactness of localized module sequences; the existing node concerns flat relation descent through colimits.
- `lem-trf-localization-exact-for-modules` vs `lem-weil-pbc-commutative-algebras-colimits-exist`: the new leaf states module exactness; the existing node is existence of colimits of commutative algebras.
- `lem-trf-localization-exact-for-modules` vs `lem-weil-pbc-directed-colimit-base-change-elementwise`: the new leaf states exactness after localization; the existing node is an elementwise directed-colimit base-change comparison.
- `lem-trf-localization-exact-for-modules` vs `lem-weil-pbc-directed-tensor-cocones-colimit-n3`: the new leaf states exactness after localization; the existing node concerns tensor cocones and a directed colimit.
- `lem-trf-localization-exact-for-modules` vs `lem-weil-pbc-filtered-colimit-algebras-elementwise`: the new leaf states module localization exactness; the existing node concerns filtered colimits of algebras.
- `lem-trf-localization-exact-for-modules` vs `lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise`: the new leaf states exactness after localization; the existing node concerns tensor calculations for filtered algebra colimits.
- `lem-trf-localization-exact-for-modules` vs `lem-weil-pbc-filtered-colimit-algebras-underlying-module`: the new leaf states exactness after localization; the existing node identifies underlying modules of filtered algebra colimits.
- `lem-trf-localization-exact-for-modules` vs `lem-weil-pbc-filtered-colimit-localization-at-prime-data`: the new leaf states exactness of arbitrary localization; the existing node packages localization-at-prime data for a filtered colimit.
- `lem-trf-localization-exact-for-modules` vs `lem-weil-pbc-filtered-colimit-localization-at-prime`: the new leaf states exactness after localization; the existing node states a filtered-colimit localization-at-prime comparison.
