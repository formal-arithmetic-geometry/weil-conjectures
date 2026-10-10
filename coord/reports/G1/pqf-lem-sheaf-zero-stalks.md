Files written:

- `pqf-lem-sheaf-zero-stalks.json`: item split, 0 new nodes.
- `citations.json`: verbatim citations for all proof-step uses.

Attachments: none.

WANTED: none.

The imported statement is mathematically correct, but its `pqf-def-coherent` dependency was unused: the argument only needs a sheaf of modules and its stalks. I replaced the single vague proof paragraph with three complete steps. The first uses the vanishing stalk hypothesis and the germ representation from `def-weil-pbc-module-stalk`; the second uses that node's germ equality criterion to obtain a neighbourhood on which the section vanishes; the third applies the separatedness clause of the sheaf axiom from `def-weil-sheaf-of-modules-category`. No new lemma is required because each step is a direct definition-level argument.

## Review by G1

I read the item source `literature/blueprint/master/blueprint/sec-abelian-varieties/sk-prop-av-pqf-finite/pqf-lem-sheaf-zero-stalks.md` and checked its two proof sentences against the existing definition nodes. `def-weil-pbc-module-stalk` explicitly states both that stalk elements are germs and that equality of two germs is equivalent to equality after restriction to a neighbourhood, exactly what steps 1 and 2 use. `def-weil-sheaf-of-modules-category` identifies a module sheaf as an underlying sheaf of abelian groups, supplying the sheaf separatedness used in step 3. The hypotheses are uniform in an arbitrary open `U`, point `x ∈ U`, and section `s ∈ F(U)`; no coherence, quasi-compactness, or scheme finiteness hypothesis is used. I searched the whole DAG and blueprint for a zero-stalk sheaf lemma and found no duplicate. Mathlib searches recorded the unavailable LeanSearch service, LeanFinder's unrelated section-zero results, Loogle's broader `TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero`, and the source grep; the broader theorem requires a fixed coefficient category and was not attached to this ringed-module statement. I also tested the edge cases `U = ∅` (vacuous section) and `F = 0`; both satisfy the proof immediately.
## Second reading by G1

- Item statement: checked against the blueprint node and its hypotheses; added explicit citations for scheme, module-sheaf, and stalk notions, with no mathematical change.
- Step 1: checked against `def-weil-pbc-module-stalk`; the stalk hypothesis gives the zero germ of every section at every point.
- Step 2: checked against that node's verbatim germ equality criterion; applied to the section and the zero section on the same open.
- Step 3: checked against `def-weil-sheaf-of-modules-category`; its underlying abelian sheaf supplies the separatedness axiom, so a section locally zero is zero.
- New nodes: none; all three proof steps are definition-level and no duplicate or Mathlib leaf is needed.
- Metadata: filled the required blueprint ancestry (`from`) and empty `same_as` list; retained the recorded Mathlib searches, including the unavailable LeanSearch result.
- Edge cases: empty scheme/open and zero sheaf reduce to the stated argument; no source error found.
