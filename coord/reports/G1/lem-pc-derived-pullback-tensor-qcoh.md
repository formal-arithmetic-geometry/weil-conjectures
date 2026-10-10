# Stage 1 report

1. Files written:

   - `dag/nodes/sec-picard-framework/lem-pc-derived-pullback-tensor-qcoh.json` — item, statement, split proof, no new nodes, Mathlib searches recorded.
   - `citations.json` — verbatim statement excerpts for every cited node in each step.

2. Attachments: none.

3. WANTED: `literature/stacks-project/perfect.tex`, Lemma 36.3.8 (Tag 08DW), part (1), for derived pullback preserving quasi-coherence; and Lemma 36.3.9 (Tag 08DX), part (1), for derived tensor preserving quasi-coherence. The local literature checkout contains only the citation index, not the Stacks TeX sources.

4. No source statement or Lean declaration was changed. The imported item had no proof; I supplied two steps matching its two clauses. Existing DAG searches found the K-flat resolution, termwise pullback, affine pullback-section, and quasi-coherent tensor-product statements, so no duplicate clause node was created.

## Review by G1

I read the item and its parent `lem-pc-projection-formula`; the parent explicitly takes the conclusion that `E tensor^L Lf^*K` remains in `D_QCoh`. I checked the statements of all four cited nodes. Step 1 uses the K-flat-resolution existence, the termwise computation of derived pullback for a flat complex, and the affine pullback-section isomorphism; these establish quasi-coherence locally on affine opens. Step 2 uses K-flat resolutions and the existing theorem that tensor products of quasi-coherent modules are quasi-coherent with affine section formulas. The hypotheses are schemes and quasi-coherent objects as required by the item. I tested the identity morphism and affine schemes as small cases: both clauses reduce to ordinary pullback/tensor of modules. The Mathlib searches found only generic sheaf pullback/quasi-coherence declarations and no exact derived `D_QCoh` theorem; LeanSearch was unavailable and is recorded as such. Citations are copied verbatim into `citations.json`.

5. What I could not finish: the Stacks source packet is absent locally, so the exact source proof could not be read; this is reported under WANTED and the proof is marked agent-origin.

## Second reading by G1

- Item statement: checked against Stacks 08DW(1) and 08DX(1), including the morphism-of-schemes and $D_{\\mathrm{QCoh}}$ hypotheses; verdict: correct.
- Step 1: checked against 08DW proof and 06Z0 (the affine derived equivalence); verdict: repaired. The former K-flat argument used a resolution with properties not stated by its cited nodes.
- Step 2: checked against 08DX proof and 06Z0, with the underived affine tensor section formula 01I8/01CE represented by the existing tensor node; verdict: repaired.
- New nodes: none; existing affine equivalence and affine tensor nodes were reused, and no duplicate or Mathlib leaf was created.
- Small cases: identity morphism, affine schemes, the zero complex, and the empty scheme reduce respectively to identity pullback, derived tensor over a ring, zero, and the unique zero object.

Changes made: replaced the unsupported global K-flat/termwise pullback route with the local-affine reduction used in the Stacks proofs; removed citations whose statements did not supply the claimed boundedness or quasi-coherence; updated citations.json to contain only verbatim statements actually used; recorded the source-page check despite the absent local TeX packet.
