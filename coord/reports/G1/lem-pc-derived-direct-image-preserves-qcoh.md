1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-derived-qcoh-truncation-filtration.json` — statement-only node; Mathlib searches found no match.
- `dag/nodes/sec-picard-framework/lem-pc-derived-direct-image-preserves-qcoh.json` — split item; Mathlib searches found no match.
- `citations.json` — verbatim step citations.

2. Attachments: none.

3. WANTED: `literature/stacks-project/perfect.tex`, Tag 08D5, for the item and the truncation-filtration node. The local repository contains only citation metadata; the proof was checked against the imported Tag 08D5 description and written out from the standard canonical-truncation argument.

4. No statement error was found. The imported item had no proof and no matching declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `Comparator`. I searched all DAG nodes and the imported blueprint for the item, for Tag 08D5, and for the truncation-spectral-sequence formulation. The existing `lem-pc-finite-support-hi` is not a duplicate: it concerns a single quasi-coherent sheaf and the individual sheaves $R^if_*\\mathcal F$, whereas this item concerns arbitrary derived complexes and all cohomology sheaves of $Rf_*E$. The new node is also distinct from it: it states the canonical truncation spectral sequence and the finite-filtration closure implication, not quasi-coherence of individual higher direct images.

## Not duplicates

`lem-pc-derived-qcoh-truncation-filtration` vs `lem-pc-finite-support-hi`: the new node is the derived canonical-truncation spectral sequence and its finite-filtration consequence; the existing node is the sheaf-level theorem that each $R^if_*\\mathcal F$ is quasi-coherent (plus a vanishing bound).

`lem-pc-derived-qcoh-truncation-filtration` vs `lem-pc-derived-direct-image-preserves-qcoh`: the new node is a general truncation spectral-sequence and finite-filtration mechanism, while the item applies it with the qcqs hypothesis and `lem-pc-finite-support-hi` to prove preservation of the full $D_{\\mathrm{QCoh}}$ subcategory.

`lem-pc-derived-qcoh-truncation-filtration` vs `lem-sc-qcoh-acyclic-derived-pushforward-cohomology`: the existing node assumes all positive higher direct images vanish and concludes $H^i(Rf_*E)\\cong f_*H^i(E)$ for unbounded complexes; the new node gives the general truncation spectral sequence and finite-filtration closure argument without that vanishing assumption.

`lem-pc-derived-qcoh-truncation-filtration` vs `lem-pc-derived-direct-image-uniform-truncation-bound`: the existing node gives a uniform high-degree vanishing bound and eventual truncation invariance for qcqs pushforward; the new node gives the spectral-sequence terms and finite filtration used to prove quasi-coherence of each output cohomology sheaf.

## Review by G1

I read the item statement and source metadata for Stacks Tag 08D5, the existing statement of `lem-pc-finite-support-hi`, and the definitions `def-pc-derived-category` and `def-pc-derived-direct-image`. I also checked `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the blueprint tag and relevant derived/direct-image declarations; no sorry-free declaration states this item exactly.

Step 1 uses the definition of $D_{\\mathrm{QCoh}}$ to obtain quasi-coherent $\mathcal H^q(E)$, the new truncation node for the $E_2^{p,q}=R^pf_*\\mathcal H^q(E)$ spectral sequence, and `lem-pc-finite-support-hi` for quasi-coherence of those $E_2$ terms. Each cited statement says exactly the fact used. Step 2 uses the new node's finite filtration and closure assertion, then the derived-category definition to identify the target subcategory. No step is marked elementary because each invokes a genuine derived or sheaf-theoretic theorem.

For hypotheses, I checked that the item assumes $f$ quasi-compact and quasi-separated, exactly the hypotheses of `lem-pc-finite-support-hi`, and that $E$ has quasi-coherent cohomology by membership in $D_{\\mathrm{QCoh}}$. The empty complex and the identity morphism give the expected zero and identity cases. The Mathlib searches were run for both the item and the new node using LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such. No Mathlib declaration states the needed scheme-derived result.

No corrections to the imported statement were needed.

6. What I could not finish: the cited Stacks source file is not present in this repository, so the report records it as WANTED; the proof follows the Tag 08D5 route and the standard truncation filtration supplied by the new node.

## Second reading by G1

- Item statement: checked against Stacks Tag 08D5 part (1) metadata and the imported blueprint; qcqs hypotheses and the conclusion about $D_{\\mathrm{QCoh}}$ agree, including the zero and identity cases.
- Step 1: checked against `def-pc-derived-category`, `lem-pc-finite-support-hi`, `lem-pc-derived-direct-image-uniform-truncation-bound`, and `thm-sp-truncation-e2`; the uniform bound now supplies the bounded-below truncation, and the existing spectral-sequence theorem supplies the finite range.
- Step 2: checked against the finite filtration clause of `thm-sp-truncation-e2`, the uniform truncation isomorphism, and the affine module description of quasi-coherent sheaves; the extension argument is local on affine opens.
- New node `lem-pc-derived-qcoh-truncation-filtration`: checked against existing `thm-sp-truncation-e2` and the uniform-bound node; removed because it duplicated their spectral-sequence/filtration content and did not itself justify finiteness for an unbounded complex.

Changes made: removed the redundant truncation node and its citations; rewrote both item steps to cite the existing bounded-below spectral sequence and uniform truncation bound; corrected `created.item` to this item; updated `citations.json` with verbatim statements. The source file remains WANTED as recorded above.

The existing `thm-sp-truncation-e2` is recorded as a tool from the proper-base-change unit: it is the generic bounded-below truncation spectral sequence needed after the qcqs uniform-bound reduction, and no Picard-duality node supplies that result.
