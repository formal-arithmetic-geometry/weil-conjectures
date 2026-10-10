# Stage-1 report: lem-sc-finite-twisted-inverse-bounded-below

Files written:

- `dag/nodes/sec-picard-framework/lem-sc-finite-twisted-inverse-bounded-below.json` — statement, split proof, blueprint metadata, and split report.
- `dag/nodes/sec-picard-framework/lem-sc-finite-rfstar-finite-cohomological-dimension.json` — statement-only Stacks input; Mathlib search found no match.
- `dag/nodes/sec-picard-framework/lem-pc-derived-tstructure-orthogonality.json` — statement Mathlib leaf; exact match `CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE`.
- `citations.json` — verbatim statement quotes for every cited step.

Attachments: none.

WANTED: none.

The source packet for Tag 0AX2 was read in `/home/ubuntu/c1-stacks-review/duality.tex`, lines 509–533. The repository does not carry the Stacks TeX checkout itself. The source proves the stronger qcqs version; the item specializes it to finite morphisms of Noetherian schemes. The imported item had no proof and no Lean declaration with the blueprint tag; searches of both `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-conjectures-slopmaster2/WeilConjectures` found no matching declaration.

## Review by G1

I checked the item statement against Tag 0AX2: finite Noetherian schemes satisfy the source's quasi-compact and quasi-separated hypotheses, and the right adjoint is the `f^!` in the item. Step 1 uses only the new finite-cohomological-dimension statement, which says exactly that `Rf_*` raises a uniform upper cohomological bound by at most `N`; the finite-to-qcqs reduction is elementary from the finite-morphism and Noetherian definitions. Step 2 uses that same amplitude statement for the truncation `A = tau_{<= c-N} f^!K`, and uses the Mathlib leaf whose statement is precisely vanishing of morphisms from `D^{<= n}` to `D^{>= m}` for `n < m`; the adjunction is the defining right-adjoint property of `f^!`. Step 3 is elementary truncation bookkeeping: the canonical truncation map induces the identity on cohomology in degrees at most `c-N`, so its vanishing forces those cohomology sheaves to vanish. I checked the small cases `f = id` (take `N = 0`, so the assertion is tautological) and `K` concentrated in one degree (the bound shifts by at most `N`).

For the new Stacks node I searched the whole DAG and blueprint for finite cohomological-dimension or `Rf_*` boundedness statements; none states this result. Its Mathlib searches were run with LeanFinder, Loogle, and Mathlib grep and found no derived-scheme amplitude theorem. For the orthogonality node I searched the whole DAG and blueprint; no duplicate statement was present. LeanFinder located `CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE`, and I read the declaration at `Mathlib/CategoryTheory/Triangulated/TStructure/Basic.lean:250-252`; the other required searches were recorded as unavailable/no direct hit. The new node is therefore marked as an exact Mathlib leaf.

No source or statement error was found, and no existing node was changed.

## Second reading by G1

- Item statement: checked against Stacks Tag 0AX2, `lemma-twisted-inverse-image-bounded-below`; finite Noetherian hypotheses imply the source's quasi-compact and quasi-separated hypotheses, and the right-adjoint and `D^+_{QCoh}` meanings match. Verdict: correct; tested on the identity finite morphism and a one-degree complex.
- Step 1: checked against Tag 0AX2's first paragraph and Tag 08D5/`lemma-quasi-coherence-direct-image`; the existing uniform truncation-bound node supplies the result after an explicit shift. Verdict: repaired and correct.
- Step 2: checked against the displayed Hom computation in Tag 0AX2 and the standard t-structure definition; truncation bounds, adjunction, and strict inequality for orthogonality are in force. Verdict: repaired to cite the existing bound node and state the adjunction use.
- Step 3: checked against the final sentence of Tag 0AX2 and the canonical truncation triangle; the induced cohomology identity gives the lower bound. Verdict: elementary and correct.
- `lem-pc-derived-tstructure-orthogonality`: checked against Mathlib `CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE` and its standard t-structure dependency. Verdict: exact Mathlib leaf; small cases `n=0,m=1` and zero source are consistent.

Changes: removed `lem-sc-finite-rfstar-finite-cohomological-dimension` because it duplicated the existing `lem-pc-derived-direct-image-uniform-truncation-bound` up to shifting; rewrote Steps 1 and 2 and their citations accordingly; corrected `proof_deps` and citations. The source and target statements were otherwise unchanged.

## Not duplicates

lem-sc-finite-rfstar-finite-cohomological-dimension vs lem-pc-noetherian-derived-direct-image-right-adjoint: the existing node uses Tag 08DW only for quasi-coherence preservation and right-adjoint existence on Noetherian schemes; it does not state the uniform finite cohomological-amplitude bound $Rf_*D^{\\le r}\\subseteq D^{\\le r+N}$ needed here, and its hypotheses/conclusion are different.
