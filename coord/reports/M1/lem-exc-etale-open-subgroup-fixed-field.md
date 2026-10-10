files written:
- lem-exc-etale-open-subgroup-fixed-field.json — split statement; no new Lean code.
- lem-exc-etale-open-subgroup-fixed-field-galois.json — Mathlib leaf (three declarations, lines recorded).
- lem-exc-etale-open-subgroup-quotient-finite-discrete.json — Mathlib leaf (two declarations, file recorded).
- citations.json — verbatim citations for both proof steps.

attachments: none.

WANTED: none.

The imported item had the correct fixed-field statement but no proof split. I kept its route through the finite Galois correspondence in Stacks Tags 03QR and 0BML. The two new nodes are strictly smaller facts used by the proof, rather than restatements of the item.

## Review by M1

I read the item and its parent classification node in `dag/nodes/sec-curve-estimates/`, and checked the source claims against the Stacks Project web pages for Tag 03QR (Lemma 58.2.2) and Tag 0BML (Theorem 9.22.4). Step 1 cites the first new node, whose statement explicitly supplies finite-dimensionality, separability, and the equality of the fixing subgroup with H; these are exactly the fixed-field facts used. I verified that the hypotheses are met for K^sep/K because a separable closure is separable algebraic and normal, and that a point stabilizer is open by continuity. Step 2 cites the second new node, whose statement explicitly supplies both finiteness and the discrete quotient topology for G/H; compactness and continuous multiplication are the Krull-topology hypotheses on the absolute Galois group.

For the first new node I searched LeanFinder, Loogle, and Mathlib grep under its own id. LeanFinder returned `InfiniteGalois.isOpen_iff_finite`, `InfiniteGalois.fixingSubgroup_fixedField`, and `IntermediateField.isSeparable_tower_bot`; grep located the relevant declarations at `Mathlib/FieldTheory/Galois/Infinite.lean` lines 241 and 146 and `Mathlib/FieldTheory/Separable.lean` line 713. The combined Loogle pattern returned no hit, which is recorded as such. For the quotient node, LeanFinder returned `Subgroup.quotient_finite_of_isOpen` and `Subgroup.instDiscreteTopologyQuotientOfContinuousMul` in `Mathlib/Topology/Algebra/OpenSubgroup`; the Loogle and combined grep queries returned no hit and are recorded. I also searched the whole DAG and blueprint for duplicate fixed-field or Galois-correspondence nodes; none states this open-subgroup field result. Small cases checked were H=G (fixed field K and one-point quotient) and H={1} for a finite Galois extension (fixed field K^sep in the finite model and quotient of the expected finite size).

