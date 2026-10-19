# Stage-1 report: lem-kun-dimension-finite-type

Files written:
- `dag/nodes/sec-smooth-purity/lem-kun-dimension-finite-type.json` (statement, repaired split).
- `dag/nodes/sec-smooth-purity/lem-kun-finite-type-residue-trdeg.json` (unsplit statement node; no exact Mathlib leaf).
- `dag/nodes/sec-smooth-purity/lem-kun-finite-type-local-dimension.json` (unsplit statement node; no exact Mathlib leaf).
- `citations.json`.

Attachments: none.  WANTED: none.

The return required the unit route through `lem-kun-dimension-formula`. I restored that route explicitly: pointwise finiteness follows by combining the dimension formula with finite local-ring dimension and finite residue-field transcendence degree, then the global supremum is finite because finite-type schemes over fields are Noetherian with finitely many irreducible components. The prior residue-field Mathlib classification was too strong: the affine chart, quotient by a prime, localization, and residue-field identifications are substantive, so that node is now unsplit. I added a separate unsplit local-dimension node for the equally substantive Noetherian-stalk argument.

## Review by NC

I read the unit blueprint paragraph and the existing `lem-kun-dimension-formula` statement and proof. Step 1 cites the exact conclusions of both new nodes and the formula node; the formula's hypotheses (finite type over a field and a point) match the item. The new residue-field statement is sourced to Stacks Tag 00P0 but deliberately remains unsplit because applying the general finite-type algebra theorem requires the affine quotient and residue-field identifications. The local-dimension statement likewise remains unsplit because Mathlib's finite-Noetherian-local-ring instance still requires proving that the scheme stalk is Noetherian and local.

Step 2 uses only the definition of `kundim`; the generic-point/component and chain containment argument is written out as the elementary topology step from the blueprint. Step 3 uses the cited finite-type-over-Noetherian theorem and the cited Noetherian finite-components theorem, with the field's Noetherian hypothesis checked directly. Step 4 uses the definition and finite-components statement to take a finite maximum, including the empty case. I checked every citation quote against its node file and updated `citations.json` accordingly. Mathlib searches for both new nodes used LeanFinder, Loogle, and grep; they found only general algebra declarations, so neither is marked as a one-line Mathlib leaf.

## Not duplicates

`lem-kun-finite-type-residue-trdeg` vs `lem-kun-dimension-formula`: the existing formula equates local dimension with local-ring dimension plus transcendence degree, while this node asserts finiteness of the residue-field transcendence degree.

`lem-kun-finite-type-local-dimension` vs `lem-kun-dimension-formula`: the formula is an equality involving `kundim_x X`; this node asserts finiteness of the local-ring Krull dimension, a distinct input needed to use that equality.

`lem-kun-finite-type-local-dimension` vs `lem-weil-pbc-finite-type-domain-dimension-trdeg`: the existing node states the dimension/transcendence-degree relation for a finite-type integral domain and its fraction field, whereas this node asserts finite Krull dimension of a scheme stalk at an arbitrary point.

`lem-kun-finite-type-residue-trdeg` vs `lem-weil-pbc-finite-type-domain-dimension-trdeg`: the existing node concerns an integral-domain fraction field; this node concerns the residue field at an arbitrary scheme point and requires passing to an affine quotient and localization.

## Second reading by NC

- Item statement: checked against the blueprint node (order 1676); the field, finite-type scheme, and conclusion $\kundim X<\infty$ agree hypothesis by hypothesis, including the empty scheme.
- Item step 1: checked against the statements of `lem-kun-finite-type-local-dimension`, `lem-kun-finite-type-residue-trdeg`, and `lem-kun-dimension-formula`; each supplies exactly the asserted finite summand or equality. The empty case is explicitly covered.
- Item step 2: checked against `def-kun-dimension` and the topology argument in the blueprint; chains lie in an irreducible component and generic points realize component dimensions, so the pointwise supremum claim is the intended elementary reduction.
- Item step 3: checked against Stacks Lemma 01T6 and Topology Lemma 0052 as represented by the two cited nodes; the structure map to `Spec K` is finite type and a field is Noetherian, yielding Noetherianity and finitely many components.
- Item step 4: checked against `def-kun-dimension` and the finite-components node; the finite maximum argument handles the empty index set.
- `lem-kun-finite-type-local-dimension`: checked against Stacks Algebra Lemma 10.116.1, Tag 00P0 (`lemma-dimension-prime-polynomial-ring`) and the affine localization argument. The statement is self-contained and correctly includes arbitrary points, fields, and finite-type schemes; it remains an unsplit substantive statement.
- `lem-kun-finite-type-residue-trdeg`: checked against the same Tag 00P0 domain theorem after affine quotient and localization; the residue-field identifications are substantive, so this remains unsplit. The statement includes all points and the zero-dimensional/empty edge cases.
- Searches for both new nodes were checked in `searches.jsonl`: LeanFinder, Loogle, and source grep ran and found no exact scheme-level declaration; neither is a Mathlib leaf.

Changes made: corrected both new-node source places from the inaccurate section-style “Lemma 10.116.1” citation to the exact Stacks label `lemma-dimension-prime-polynomial-ring` (Tag 00P0), preserving the intended source and making B5 verifiable. No mathematical statements or proof steps required alteration.
