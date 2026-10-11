1. Files written:

   - `dag/nodes/sec-picard-framework/lem-sc-perfect-ext-bounded-qcoh-vanishing.json`, statement, split proof, and blueprint metadata.
   - `dag/nodes/sec-picard-framework/lem-sc-perfect-hypercohomology-gap.json`, statement-only unsplit node; Mathlib no match.
   - Existing `lem-pc-finite-support-hi` and `lem-pc-cohomology-sections-affine-base` supply the qcqs cohomology bound; no duplicate child node was created.

2. Attachments: none.

3. WANTED: none; Tag 09M4 was checked directly on the Stacks Project page and against the local node sources.

4. The imported item had no proof. I checked the exact Tag 09M4 statement and proof, including the dual perfect complex, its finite Tor-amplitude interval, the hypercohomology spectral sequence, the qcqs cohomological bound (Tag 01XJ/30.4.4), and the truncation argument. The first step uses the existing perfect RHom-tensor comparison and the generic site-level global-internal-Hom statement; the latter is declared as a tool because it is outside this unit. The second step is the new spectral-sequence gap statement. The third uses the new uniform cohomology-bound statement and the existing standard t-structure orthogonality. The last step is the interval substitution `a=-v-N`, `b=-u` and the final Hom identification. I tested the interval signs on the one-term case `K=O_X` (u=v=0): the result asks for vanishing of L in degrees `[-N,0]`, exactly the expected bound. Mathlib searches were run for both new nodes with LeanFinder, Loogle, and grep and recorded verbatim in their JSON.

## Review by H1

I read Stacks Tag 09M4 and verified that the item statement matches clause (1), including the order of the quantifiers and the interval of vanishing. I read the existing RHom comparison and global internal-Hom statements used in Step 1 and checked that they provide, respectively, perfectness of the dual and the H^0-to-Hom identification. The new hypercohomology node states precisely the spectral-sequence implication used in Step 2; the new qcqs bound states precisely the uniform N used in Step 3. The t-structure node supplies the separated-bound orthogonality invoked after truncation. Step 4 only performs the displayed integer substitution and applies the cited statements. I checked the small case `K=O_X` and `L=0`; both give the claimed vanishing. No duplicate blueprint node or existing DAG statement was found for either new lemma, and all cited nodes were opened to verify the quoted sentences in `citations.json`.

5. Nothing remains unfinished in the sandbox split; the required dry run is the next delivery-stage check.

## Not duplicates

lem-sc-perfect-hypercohomology-gap vs lem-sc-perfect-ext-bounded-qcoh-vanishing: the new node is the spectral-sequence implication for an arbitrary perfect tensor factor and a single cohomological degree; the item is the global Hom-vanishing conclusion with existence of an interval.

lem-sc-perfect-hypercohomology-gap vs lem-pc-finite-support-hi: the new node concerns derived tensor hypercohomology and Tor amplitude, while the existing node concerns higher direct images of quasi-coherent sheaves.

lem-sc-perfect-hypercohomology-gap vs lem-pc-cohomology-sections-affine-base: the new node is a spectral-sequence vanishing statement, while the existing node identifies sheaf cohomology with sections of higher direct images over an affine base.
lem-sc-perfect-qcoh-global-sections-truncation vs lem-sc-perfect-ext-bounded-qcoh-vanishing: the auxiliary node is the independent truncation/cohomological-dimension implication for an arbitrary quasi-coherent complex, while the item adds the perfect tensor-Hom and Tor-amplitude argument and concludes a Hom vanishing interval.

## Second reading by H1

- Step 1 checked against Stacks Tag 09M4 and the statements of `lem-pc-perfect-rhom-tensor-comparison` and `lem-pur-rhom-global-sections`; verdict: the dual/tensor and global-Hom identifications are exactly the cited conclusions.
- Step 2 checked against the Tag 09M4 spectral sequence and `lem-sc-perfect-hypercohomology-gap`; verdict: the interval `[j-v,j-u]` and the union over `j=-N,...,0` give `[-v-N,-u]` with the correct signs.
- Step 3 checked against Tag 09M4, Tag 01XJ, the generic Leray edge-map node, affine quasi-coherent acyclicity, and the new truncation statement; verdict: the morphism to `Spec(Z)` is only qcqs, and the repaired route no longer assumes it is separated.
- Step 4 checked against the final sentence of Tag 09M4 and Steps 1--3; verdict: the integer substitution is elementary and the conclusion follows from the preceding identifications.
- `lem-sc-perfect-hypercohomology-gap` checked against the displayed Tag 09M4 spectral sequence; verdict: self-contained statement, correct Tor-amplitude interval, no proof fields.
- `lem-sc-perfect-qcoh-global-sections-truncation` checked against the Tag 09M4 truncation paragraph using the qcqs cohomology bound and standard truncations; verdict: self-contained statement-only auxiliary fact, with all notions definition-linked.
- Small cases checked: `K=O_X` gives the expected interval `[-N,0]`; `L=0` and the affine/field cases give zero Hom; `N=0` has the stated vacuous negative range behavior.

Changes: repaired the item's incorrect `created.item` metadata; replaced the invalid separated affine-base citation by the generic Leray route; added the missing truncation auxiliary statement; removed stale Step 4 citations; and made `citations.json` quote the exact cited statements.
