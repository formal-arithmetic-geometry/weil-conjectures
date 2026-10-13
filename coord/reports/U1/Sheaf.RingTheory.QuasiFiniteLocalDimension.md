## What changed

Proved `Algebra.ringKrullDim_le_of_isQuasiFiniteAtPrime` in
`Sheaf.RingTheory.QuasiFiniteLocalDimension`, preserving its signature and visibility.
The proof uses the already proved `Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime`,
Mathlib's saturation form of Zariski Main and local-ring bijectivity, then integral
incomparability and the strict-monotone height comparison. Updated the docstring and
node proof to match. Replaced the proof-only import
`Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` with `Mathlib.RingTheory.Ideal.Height`.
No public import, definition or statement changed. No forced adaptations.

The source argument is Stacks Tag 00QF, general case, with 00Q9 and 00GT.
The local copy of `literature/stacks-project/algebra.tex` is absent on this machine;
read the original at https://stacks.math.columbia.edu/tag/00QF and the Mathlib source.
The unit `sk-thm-p1` does not realize this helper as one of its fixed steps;
its route remains intact.

## Proved and sorry left

Closed 1 hole: `Algebra.ringKrullDim_le_of_isQuasiFiniteAtPrime`
(node `lem-weil-pbc-dimension-inequality-quasi-finite`).
No remaining `sorry` in the delivered module. Added 0 holes and 0 intermediate statements.
This is a proof, not a decomposition. The local single-file compile passed without warnings.
The delivery dry run checks the declarations' axioms and the preflight.

## No longer needed

Removed import `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` and proof dependency
`lem-weil-pbc-localization-prime-residue-field-iso`. This proof uses no residue fields
and no successive-localization correspondence: the canonical local ring homomorphism
is bijective directly by the saturation lemma. Thus that node and module are no longer
needed by this item's proof (other users may still need them).
All other original proof-dependency nodes remain used. Both public statement imports
and the proof import `Sheaf.RingTheory.ZariskisMainAway` remain necessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error found. The original localization/residue-field
bridge was unnecessary; Mathlib already provides the exact local-ring bijectivity needed.
The Mathlib height comparison also packages the prime-chain argument directly.

## Second reading by U1

1. PASS: compared the sole delivered module with the repository using `diff`.
   The existing theorem signature and visibility are byte for byte unchanged.
   Only its proof, explanatory proof docstring and one plain proof import changed;
   no definitions, public imports, statements or other modules changed.
2. PASS: independently compiled the file through `lcompile.py` without warnings.
   A scratch copy with `#print axioms Algebra.ringKrullDim_le_of_isQuasiFiniteAtPrime`
   reports exactly `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
   No sorry or forbidden declaration mechanism occurs in the delivered source.
   The integral closure is Mathlib's actual construction; the ring equivalence
   inverts a canonical homomorphism with proved bijectivity, so no arbitrary
   object is selected from an unproved existence statement.
3. PASS: no split-off statements, new declarations or new nodes. Checked the
   saturation witnesses, integral incomparability, and height comparison against
   their Mathlib source. The argument needs neither injectivity of the original
   algebra map nor Noetherian or finite-dimensional hypotheses. Zero rings admit
   no prime q, and infinite heights are handled by ENat and WithBot.
4. PASS: repeated a LeanFinder search using isolated fibre points and contracted
   heights, Mathlib grep, and searches of lean/Sheaf and lean/WeilConjectures;
   found no direct theorem giving a shorter proof with these hypotheses.
   Each remaining import is needed for the statement or proof. The removed
   localization/residue-field node is exactly the old proof dependency omitted
   by this proof, and is fully listed in No longer needed. Read
   dag/units/sk-thm-p1.json: this helper is not a fixed realized step, and the
   unit's route is preserved. Checked the source argument at
   [Stacks Tag 00QF](https://stacks.math.columbia.edu/tag/00QF).
5. PASS: node changes are confined to proof, proof_deps and proof_origin.
   The proof dependencies equal the union of the steps' uses; the recorded
   integral-closure, incomparability and local-dimension nodes match the Lean
   declarations used. Saturation and strict-monotone height comparison implement
   the recorded prime-chain argument. No new-node requirements apply.

Second reading changed only this report and added independent search records;
no Lean or node repairs were necessary. Independently confirmed 1 hole closed,
0 holes added, and 0 split-off statements.
