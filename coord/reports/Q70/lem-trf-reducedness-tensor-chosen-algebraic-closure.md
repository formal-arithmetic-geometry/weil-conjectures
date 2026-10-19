# Stage 1 report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-reducedness-tensor-chosen-algebraic-closure.json`: split item.
- `dag/nodes/sec-trace-formula/lem-trf-reducedness-tensor-alg-equiv.json`: new unsplit statement-only node; Mathlib ingredients found, no exact combined declaration.
- `citations.json`: verbatim proof-step citations.

## Attachments

`lem-pc-algebraic-closure-exists-unique` is the existing Mathlib leaf used for uniqueness of algebraic closures; no Lean project declaration attaches to the item itself.

## WANTED

None.

## What was checked and changed

The item source is Stacks Project `fields.tex`, Tag 09GV, with the tensor transport used in the affine criterion. I read the existing node `lem-pc-algebraic-closure-exists-unique`; its statement supplies a field isomorphism commuting with the two maps from the base field, exactly the hypothesis needed to package a $k$-algebra equivalence between the chosen and canonical closures. I also checked Mathlib's `IsAlgClosure.equiv` and `Algebra.TensorProduct.congr` source locations through the recorded searches. No declaration under `WeilConjectures/` states the item exactly or without `sorry`.

Step 1 cites `lem-pc-algebraic-closure-exists-unique` and uses its explicit sentence about an isomorphism of any two algebraic closures over $k$; the field-extension hypotheses in the item make both closures eligible. Step 2 cites the new node `lem-trf-reducedness-tensor-alg-equiv`, whose statement is precisely the tensor reducedness transport needed. The new node is strictly more general than the item (arbitrary $k$-algebra-equivalence of scalar fields), so it is not a restatement. The transport argument is via `Algebra.TensorProduct.congr` and `isReduced_of_injective` in both directions. The canonical tensor-factor order is handled by the standard tensor symmetry.

I checked edge cases: $A=0$, $A=k$, and $k$ algebraically closed all reduce to the same equivalence, and no finite-type, separability, or perfectness assumption is used. I searched the DAG and blueprint for duplicate closure/tensor/reducedness statements; the existing algebraic-closure uniqueness leaf is cited rather than duplicated. The item’s imported statement and hypotheses were retained unchanged.

## Review by Q70

I read the item node, the `sk-i-curve-zero` unit, the `sec-trace-formula` chapter, and the cited existing closure-uniqueness node. The item’s two proof steps match the source route: first identify the two closures over $k$, then transport reducedness through the induced tensor equivalence. Every cited node says exactly what its step takes from it, and `citations.json` quotes those statements verbatim. The new node has no proof steps because it is a statement-only unsplit lemma, and its Mathlib searches record all four commands run for the node. I verified that the statement introduces the field, algebra, scalar fields, and equivalence it needs, and that the proof does not assume finite generation or any unmentioned coefficient category. The item and new node carry the required blueprint ancestry and search logs.

## What could not be finished

The new transport lemma remains unsplit for the next stage; it is stated with the exact generality needed by the item and has no exact one-declaration Mathlib match.

## Not duplicates

lem-trf-reducedness-tensor-alg-equiv vs lem-pc-base-tensor-ordinary-degree-iso: the existing node is a module-level base-change isomorphism with an extra A-module and B-linear conclusion; it does not state reducedness invariance under a field algebra equivalence.
lem-trf-reducedness-tensor-alg-equiv vs def-weil-pbc-module-tensor-product: the existing node is only the tensor-product definition and universal property, with no reducedness or equivalence hypothesis.
lem-trf-reducedness-tensor-alg-equiv vs lem-pc-base-localization-dlinear-glue: the existing node compares scalar extensions of modules along a ring isomorphism and does not assert reducedness of tensor-product rings.
lem-trf-reducedness-tensor-alg-equiv vs lem-pc-first-localization-ordinary-square: the existing node is a derived/homological localization comparison and has no reduced-ring conclusion.
lem-trf-reducedness-tensor-alg-equiv vs lem-pc-flat-iterated-scalar-extension-homology-square: the existing node concerns homology under flat scalar extension, not ring reducedness under an algebra equivalence.
lem-trf-reducedness-tensor-alg-equiv vs lem-pc-scalar-coefficient-triangle-boundary: the existing node concerns connecting morphisms in scalar-extended triangles, not reduced tensor-product rings.
lem-trf-reducedness-tensor-alg-equiv vs lem-pc-scalar-extension-homology-square: the existing node is a homology square for modules and complexes and does not state reducedness.
lem-trf-reducedness-tensor-alg-equiv vs lem-pc-semilinear-scalar-extension-homology-square: the existing node transports semilinear homology data, not reducedness of tensor products.
lem-trf-reducedness-tensor-alg-equiv vs lem-pc-tensor-coefficient-shift-homology: the existing node is a shifted homology comparison and has no nilpotent/reducedness assertion.
lem-trf-reducedness-tensor-alg-equiv vs lem-weil-pbc-algebra-tensor-map-ring-hom: the existing node only constructs the tensor-product ring homomorphism f tensor id and does not assert that an isomorphism preserves reducedness.
lem-trf-reducedness-tensor-alg-equiv vs lem-weil-pbc-directed-subalgebra-tensor-colimit: the existing node identifies a filtered colimit presentation and does not compare reducedness through an algebra equivalence.
lem-trf-reducedness-tensor-alg-equiv vs lem-weil-pbc-presentation-base-change: the existing node gives polynomial presentations after base change and has no reducedness conclusion.
