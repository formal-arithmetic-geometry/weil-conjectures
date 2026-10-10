# Stage-1 report: thm-picard-serre-a

Files written:

- `dag/nodes/sec-picard-framework/thm-picard-serre-a.json` (statement, split)
- `dag/nodes/sec-picard-framework/lem-pc-generating-sections-pushforward.json` (statement, closed Lean declaration; Mathlib searches found no exact match)
- `citations.json`

Attachments:

- `AlgebraicGeometry.Scheme.Modules.GeneratingSections.ofPushforward` belongs to `lem-pc-generating-sections-pushforward` (new node, Lean source `WeilConjectures/AlgebraicGeometry/Modules/ClosedImmersion.lean:107-129`).

WANTED:

- None.

What was checked and corrected:

- The item declaration `AlgebraicGeometry.Scheme.Modules.exists_generatingSections_tensor_twist` in `WeilConjectures/AlgebraicGeometry/Cohomology/Serre.lean:443-502` is not attachable: its own proof is sorry-free but the audit records a transitive sorry dependency. I therefore split the item.
- The blueprint proof and unit route were checked against the theorem docstring and implementation. Step 1 uses the existing coherent closed-immersion node for coherence and the projection-formula isomorphism, plus the new closed-immersion generation node for the descent of generators. The new node's statement is exactly the conclusion supplied by `GeneratingSections.ofPushforward`.
- Step 2 uses only the projective-space twist definition: the transition rule makes the local sections `x_j^d` glue, and the standard charts cover projective space.
- Step 3 uses the existing finite twisting-module quotient node, the definition of invertibility to justify tensoring preserving surjectivity, and the existing twist-tensor isomorphism node. The edge case `r=0` is handled explicitly in the step text.
- I searched the whole DAG and blueprint for duplicates before adding the new node. Mathlib searches were run twice with LeanFinder, Loogle, and Mathlib grep; the general `GeneratingSections.ofEpi` results do not state descent along a closed immersion, so the node is not a Mathlib leaf.

## Review by C1

I read the item source, the unit record, the Lean theorem and its docstring, and the complete statements of every cited node. In particular, the existing coherence node does state the tensor/projection-formula isomorphism used by Step 1, while it does not state descent of global generation; that gap is why the new closed-immersion node was added. The new node is backed by the exact Lean declaration and its source comments. I checked the quotient node supplies a finite sum of negative twists and a surjection, the invertible-module node supplies invertibility, and the twist-tensor node supplies the identification with the nonnegative twist. The statement hypotheses and the `m\ge m_0` bound were checked against the item. No duplicate node or unsupported citation was found.

## Second reading by C1

- Item statement: checked against the imported blueprint/Hartshorne II.5.17 statement and the Lean theorem signature; the field, closed immersion, twist, coherence, and $m\ge m_0$ hypotheses and the stalkwise global-generation conclusion agree.
- Step 1: checked the closed-immersion coherence/projection-formula node and the pushforward-generation declaration; stalk and global-section identifications are elementary from the definition of closed pushforward, and the global-generation notion now cites its definition node.
- Step 2: checked the projective twist transition rule and standard-chart cover; the gluing calculation is explicit and handles $d=0$.
- Step 3: checked the finite twist quotient, invertibility definition, and twist-tensor isomorphism; preservation of surjectivity is justified stalkwise, and the $r=0$ case is explicit.
- New node `lem-pc-generating-sections-pushforward`: checked its closed-immersion hypotheses and conclusion against `GeneratingSections.ofPushforward` (Lean source lines 107--129), with the global-generation definition added as a dependency; Mathlib searches and small cases (empty scheme, field, zero module) give no counterexample.
- Small cases checked for the item: $X=\varnothing$, $X=\operatorname{Spec}k$, $n=0$, and $\mathcal F=0$; all are covered, including the empty quotient family.

Changes made: added `def-weil-pbc-generating-sections` to the item and new-node dependencies and citations, and expanded Step 3 with the local rank-one tensor-surjectivity argument. These repairs make every non-elementary notion and proof fact cited without adding a duplicate node.
