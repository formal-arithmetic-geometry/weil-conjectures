1. Files written:

- `dag/nodes/sec-curve-estimates/lem-exc-finite-galois-algebra-tensor-decomposition.json` (item, split; no new nodes)
- `citations.json` (verbatim citation for the proof step)

2. Attachments: none.

3. WANTED: none.

4. The item is the affine consequence conditional on a supplied finite-Galois tensor isomorphism. I removed the erroneous self-citation and the attempted repetition of the sibling tensor-decomposition proof. The proof now applies the existing affine fibre-product spectrum statement and writes out the induced product-spectrum and projection calculation.

## Not duplicates

lem-exc-finite-galois-algebra-tensor-decomposition vs lem-exc-finite-galois-tensor-decomposition: this item assumes the tensor isomorphism and proves only the affine fibre-product coproduct with projection labels; the sibling additionally proves the tensor isomorphism and the sheaf-sections consequence.

5. What I could not finish: nothing.

## Review by E1

I read the item against the Stacks Tag 03SF discussion in `literature/stacks-project/pione.tex`. The sole proof step uses `lem-weil-pbc-fibre-product-affine-spectra`, whose statement gives exactly the identification of the fibre product with `Spec(E tensor_L E)` and identifies both projections with the two canonical tensor inclusions. I verified the hypotheses by instantiating its commutative base ring and algebras with L and E; the finite Galois assumptions are already present in the item and are used only to index the given isomorphism phi. Transporting that identification through phi gives `Spec(product_q E)`, whose standard affine spectrum calculation is the finite coproduct of `Spec E`; contravariance gives the identity and `Spec q` labels from the two displayed ring maps.

I checked the trivial case E=L (one coproduct component and both projections the identity) and a quadratic Galois extension (two components, with the second projection the conjugation map). The citation quote is copied verbatim from the cited node. The affine spectrum lemma is an off-unit generic scheme tool, recorded in `split_report.tool_uses` for maintainer review. No new node was created, so no new Mathlib search record was required.

## Second reading by E1

- Item statement: compared its supplied tensor-isomorphism hypothesis, affine fibre product, and projection labels with the sibling tensor-decomposition node and Stacks Schemes Tag 01I4 and Algebra Tag 00ED. Verdict: true under the stated hypothesis.
- Step 1: read the full statements of lem-weil-pbc-fibre-product-affine-spectra and lem-weil-pbc-spec-finite-product-fields. The first gives the tensor spectrum and inclusion maps; the second gives disjoint open component embeddings covering the spectrum. Gluing on that disjoint open cover gives the coproduct property. The composite of phi with coordinate q sends a tensor b to a q(b), so the restricted projections are id and Spec q. Verdict: valid after adding the finite-product citation and explicit map calculation.
- New nodes: none; the existing finite-product spectrum node supplies the needed fact. No duplicate was created.
- Small cases: E=L gives Q={1}, W=Spec L and both projections are identities. A quadratic Galois extension has two components and the conjugation map labels the second projection of one. Q is nonempty because it contains the identity; E being a field excludes the empty scheme.
- Existing-node search: searched DAG statements for finite-product spectra, finding lem-weil-pbc-spec-finite-product-fields; the affine fibre-product lemma was already cited. The read-only Lean source contains no declaration named for this node. No new Mathlib leaf was required.
- Changes: replaced stale five-step citations with the verbatim statements of the two current citations; added the finite-product node to uses, proof_deps and tool_uses; wrote the coordinate maps out; corrected the stale split summary.

## Source error

The inherited item source names Stacks Tag 03SF as if it states the tensor and disjoint-union calculation. In the available Stacks pione.tex, Tag 03SF is the section on Galois covers of connected schemes and does not state this calculation. The item is mathematically correct: its affine part follows from Schemes Tag 01I4 and Algebra Tag 00ED, and the tensor isomorphism is an explicit hypothesis. The source field is maintainer-owned, so this delivery leaves it unchanged and reports the mismatch here.
