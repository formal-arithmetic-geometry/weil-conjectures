# Worker report

## Files written
- dag/nodes/sec-proper-base-change/lem-weil-pbc-normal-algebra-separable-scalar-extension.json: item, split in three steps; statement unchanged.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-separable-field-geometrically-normal.json: statement-only input 0C30, unsplit; no Mathlib match.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-geometrically-normal-tensor-normal.json: statement-only input 06DF, unsplit; no Mathlib match.

## Attachments
None. No blueprint-tag declaration or normal scalar-extension theorem occurs in WeilConjectures of slopmaster2. Upstream master was treated solely as reference.

## WANTED
None.

## Faults corrected
The item had no proof. I exposed precisely the two algebra inputs used by Stacks 0C3M rather than replacing its conclusion by a new scalar-extension node. Geometric normality is defined inline in each new statement using all field extensions. No statement correction or dispute was needed. The inherited searches include invalid Loogle identifiers; I treated them as parser errors and made additional real searches. LeanSearch returned HTTP 500, recorded as unavailable. The normality of field extensions in FieldTheory.Normal is a different notion, and Mathlib's geometrically reduced tensor results assert reducedness only. Read Separable.lean:539-560 and GeometricallyReduced.lean:54-95; Algebra.IsSeparable forces algebraicity and does not cover the stated nonalgebraic hypothesis.

## Unfinished
Only the two deliberately unsplit input lemmas remain for later workers. No Lean was written or compiled.

## Not duplicates
lem-weil-pbc-geometrically-normal-tensor-normal vs lem-weil-pbc-normal-algebra-separable-scalar-extension: 06DF takes an arbitrary geometrically normal k-algebra A and any normal B, whereas the item takes a separable field K and normal B; the general tensor theorem does not provide geometric normality of that field, which is a separate proof step.

lem-weil-pbc-separable-field-geometrically-normal vs lem-weil-pbc-normal-algebra-separable-scalar-extension: 0C30 asserts normality of K tensor_k E for every field E/k, without a normal algebra B; the item asserts normality after tensoring K with arbitrary normal B. The geometric-normality input and the general tensor theorem jointly prove the item.

The 0C30 and 06DF tag searches find only the assigned item, where they are source references rather than statements of either input. The normalization field-change item and normality-perfect-closure-test consume the assigned item; they are not proofs to cite back. Searches of all DAG chapters and blueprint for geometric normality and tensor normality found no node with either input's statement. The new tensor theorem applies to arbitrary geometrically normal algebras, not just fields; the other input has no normal B and quantifies over arbitrary field base changes. Neither repeats a clause of the assigned item.

## Review by NB
I read varieties.tex 0C3M (lemma-base-change-normal-by-separable) and its preceding fibre-product lemma, then algebra.tex 0C30 (lemma-separable-field-extension-geometrically-normal) and the entire statement and proof of 06DF (lemma-geometrically-normal-tensor-normal). The source does not require finite type, Noetherian rings, or algebraic field extensions. Its geometric-normality definition follows the equivalent conditions of the preceding algebra lemma: the all-field-extension formulation used here agrees with that definition. The 06DF proof reduces to domains internally; that is not an extra hypothesis on its statement. Its displayed A tensor_K L is a typographical base-ring error (A is only a k-algebra); A tensor_k L is meant, as the preceding line and the geometric-normality hypothesis show. This typo is not used in our proof.

Step 1 uses precisely the new 0C30 statement: the given separable field K becomes geometrically normal over k. The existing separable-field-extension definition says every finitely generated intermediate field is separably generated, exactly the source hypothesis; I did not replace it with Mathlib's algebraic separability. Step 2 uses precisely the new 06DF statement with A=K and the original B. The hypothesis obtained in step 1 is its geometric-normality premise; normality of B is given. The output is K tensor_k B. Step 3 uses the module-tensor definition only for balanced maps, the universal property, and generation by pure tensors; the commutative algebra multiplication is specified explicitly in the item, not taken from that module definition. I corrected this attribution during self-review. I wrote the inverse tensor swap, balancing relation, products and unit, localization maps, and fraction-field transport of monic equations. The normal-ring definition then gives precisely the required prime-by-prime conclusion. citations.json quotes the actual statements for each use.

For B1-B10, both new nodes introduce their own k, algebras and fields, include all hypotheses, define geometric normality inline, cite normal-ring, tensor and field definitions, and have empty proof and proof_deps. Their tags and labels were checked in tags/tags. Each has blueprint ancestry through this item and its parent, and same_as is empty after whole-blueprint searches. Search records are genuine command results; second natural-language phrasings and a valid IsIntegrallyClosed, TensorProduct Loogle query supplemented the parser failures. No hit states either input. For C1-C8 and D1-D5, the only non-elementary steps are the two explicitly cited source inputs, which are independent general algebra theorems, not elementary facts or restated scalar-extension clauses. Their statements say exactly what is taken from them. Both are in the item's unit, and no descendant is cited, so there is no off-route use or cycle.

For E1-E7, I checked k=K, transcendental separable K=k(t), zero B, and disconnected B=k times k. In the identity case a field is normal; in the transcendental case the source's separability is the broad sense used by the node. The zero algebra gives no primes, hence a vacuous normality conclusion. No step claims the entire tensor product is a domain: even with B=k a finite separable K can split after further field extension. Likewise geometric normality of A does not imply A is a domain. The new input statements and step 3 preserve these cases. No extra finiteness assumption has entered the proof.

## Second reading by NB

- Item statement: checked against varieties.tex Tag 0C3M (`lemma-base-change-normal-by-separable`), including field, normal-algebra, separability, tensor-product, and prime-localization hypotheses; verdict: agrees.
- Step 1: checked against the statement of `lem-weil-pbc-separable-field-geometrically-normal` and algebra.tex Tag 0C30; verdict: cited node supplies exactly geometric normality for every field extension, with no added finiteness or algebraicity.
- Step 2: checked against the statement of `lem-weil-pbc-geometrically-normal-tensor-normal` and algebra.tex Tag 06DF; verdict: cited node applies with A = K and the given B and supplies precisely normality of the tensor product.
- Step 3: checked against the tensor-product and normal-ring definition nodes and the tensor-swap argument; verdict: elementary balanced-map, ring-isomorphism, localization, and monic-equation transport argument, including zero and disconnected cases.
- `lem-weil-pbc-separable-field-geometrically-normal`: checked B1 self-contained statement, B3 definition citations, B4 TeX, B5 Tag 0C30 source, B6 search records, and B7 no proof fields; verdict: passes. Tested identity, transcendental separable, and zero-prime edge cases.
- `lem-weil-pbc-geometrically-normal-tensor-normal`: checked B1 self-contained statement, B3 definition citations, B4 TeX, B5 Tag 06DF source, B6 search records, and B7 no proof fields; verdict: passes. Tested zero algebra, field, and disconnected normal algebra cases.
- Changes made: none to statements, steps, citations, or node records; appended this second-reading audit only.
