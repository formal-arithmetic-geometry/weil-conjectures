1. Files written:

- `dag/nodes/sec-curve-estimates/lem-exc-finite-galois-tensor-decomposition.json` (item, split)
- `dag/nodes/sec-curve-estimates/lem-exc-finite-galois-algebra-tensor-decomposition.json` (statement, unsplit; no Mathlib match)
- `dag/nodes/sec-curve-estimates/lem-exc-finite-galois-sheaf-sections-coproduct.json` (statement, unsplit; no Mathlib match)

2. Attachments: none.

3. WANTED: none.

4. The return's D2 was repaired by removing the tensor assertion from the algebra child and proving item part (1) in five steps: primitive element, simple-extension quotient, tensor universal property, normal/separable root enumeration, and distinct-linear-factor CRT. The algebra child now states only the affine fibre-product consequence conditional on the displayed tensor isomorphism. The return's C4 was repaired by making the sheaf child a statement for a sheaf on the small etale site of an arbitrary scheme S and a finite open-and-closed coproduct object X, with the empty-overlap and singleton-empty-section hypotheses explicit. The item applies it with S = Spec L and the coproduct supplied by the affine child.

## Not duplicates

lem-exc-finite-galois-algebra-tensor-decomposition vs lem-exc-finite-galois-tensor-decomposition: the child assumes the tensor isomorphism and concludes only the affine fibre-product coproduct with projection labels, while the item proves the tensor isomorphism and also the sheaf conclusion.
lem-exc-finite-galois-algebra-tensor-decomposition vs lem-exc-etale-field-gsets: the former is an explicit affine tensor/fibre-product statement for Spec E over Spec L; the latter classifies finite etale covers by Galois sets and does not state this tensor isomorphism or projection identification.
lem-exc-finite-galois-algebra-tensor-decomposition vs lem-exc-etale-open-subgroup-fixed-field: the former is the finite affine base-change decomposition; the latter is a fixed-field correspondence for open subgroups in a separable closure.
lem-exc-finite-galois-sheaf-sections-coproduct vs lem-exc-finite-galois-tensor-decomposition: the child is the general sheaf gluing lemma for any finite open-and-closed coproduct in a small etale site; the item specializes it to the Galois fibre product and adds projection formulas.
lem-exc-finite-galois-sheaf-sections-coproduct vs lem-exc-etale-field-gsets: the former concerns sections of an arbitrary sheaf on a coproduct object; the latter concerns classification of finite etale objects and Galois actions.
lem-exc-finite-galois-sheaf-sections-coproduct vs lem-exc-etale-open-subgroup-fixed-field: the former is a sheaf descent/gluing statement with disjoint components; the latter identifies intermediate fields from subgroup stabilizers.

## Review by C1

I read the imported item and the Stacks Tag 03SF discussion, then checked every cited node's statement. Step 1 uses the existing primitive-element and minimal-polynomial quotient statements with exactly their finite separable field hypotheses. Step 2 uses the tensor node's universal property to identify the tensor with the polynomial quotient. Step 3 uses the normal conjugate-root statement and the finite Galois fixed-field statement to identify all roots with the automorphism orbit and count them. Step 4 uses the existing distinct-linear-factor CRT statement. Step 5 uses only the repaired affine child, whose statement now takes the tensor isomorphism as an input and gives the two projection labels. Step 6 uses the repaired generalized sheaf child; the fibre-product components are open and closed, disjoint, finite, and their empty overlap has singleton sections. I checked the trivial and quadratic extensions and corrected the former self-citation and the mismatch between a sheaf on Spec E and the item's sheaf on Spec L.

5. Nothing remains unfinished.

## Second reading by C1

- Item statement: checked against Stacks Tag 03SF; finite Galois hypotheses, etale-site objects, tensor map, and both projection formulas agree.
- Step 1: checked Tags 030N and 09G1; added the explicit quotient-basis computation giving `deg(f) = [E:L]`.
- Step 2: checked the tensor universal property plus existing quotient-base-change and polynomial-tensor statements; repaired the uncited identification with `E[T]/(f)`.
- Step 3: checked normal conjugate-root and finite-Galois fixed-field statements; verified distinctness and root count using the degree equality from Step 1.
- Step 4: checked the distinct-linear-factor CRT node and evaluation map; verdict correct.
- Step 5: checked the affine child and its projection labels; verdict correct and strictly conditional on the tensor isomorphism.
- Step 6: checked the sheaf child, affine decomposition, and finite-separable-spectrum etale node; added the etale-site applicability citation.
- Algebra child node: checked its self-contained field, tensor-isomorphism hypothesis, fibre product, coproduct, and projection conclusion against Tag 03SF; valid strict consequence.
- Sheaf child node: checked arbitrary small etale site, finite coproduct, disjoint overlaps, singleton empty sections, and restriction bijection; added the scheme-coproduct definition dependency.
- Mathlib searches: verified semantic, Loogle, and source-grep searches are recorded, with unavailable services marked unavailable.

Changes made: cited existing tensor quotient and polynomial tensor lemmas, cited finite-separable spectra are etale, added the coproduct definition dependency, and expanded citations.json.
