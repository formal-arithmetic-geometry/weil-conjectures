# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dvr-induced-primitive-normalization.json`: existing statement node, now split in eight steps; no exact Mathlib match. The statement and its statement dependencies are retained.
- `citations.json`: one verbatim statement quotation for every node cited by each step.
- `searches.jsonl`: actual Q03 searches recorded by msearch.py. The item's inherited searches were retained as history; the five Q03 records were appended to its Mathlib searches.
- `report.md`: this report.

No new nodes and no new Mathlib leaves. No Lean files were written and no compiler, Lake or build tool was run. All writes are in this sandbox.

## Attachments

None. Searched the whole project library for the item tag, primitive normalization and induced/highest-weight terminology. The incidental hits in ArtinSchreier, Procyclic and ring-theory files do not state this group-scheme assertion. No declaration under WeilConjectures gives all clauses of the item.

## WANTED

None for the sources of this split. The local Milne PDF and Stacks TeX sources used below are present. The existing relative Borel-geometry node records its own missing Conrad PDF; this split uses that node's statement as an existing black box, and does not claim Milne proves relative Borel geometry.

## Audit and corrections

The imported item was a statement-only supporting prerequisite. Its assertion is correct with the indicated positive-exponent convention; no statement dispute or change was needed. Milne Proposition 22.22 is over a field and does not by itself prove the DVR assertion. The proof_origin is therefore agent, with Milne supplying the field eigenline and Stacks supplying flat exactness. I did not substitute a characteristic-zero argument or assert arbitrary residue-field base change for invariants.

The essential additional argument is written in the item's steps: use two explicit linear kernels to obtain a generic eigenvector; choose its primitive integral coordinates; prove saturation of W in A[H] by cancelling the uniformizer in the right-equivariance target; use the dense reduced special-fibre cell to prove that its evaluation is a unit. Without the saturation calculation, a primitive element of W need not have been shown to remain nonzero as a function on H_kappa.

Read the current latest blueprint unit and the direct-image proof file. Proof (3) now uses compactification, whereas this item's long inherited provenance records an older alteration prerequisite. This split only discharges that existing node-level prerequisite and changes no chapter or unit route. The ancestor command returns None, agreeing with the live blueprint.from.node; its explicit place and via list were retained. Whole-blueprint searches for primitive, Borel and semi-invariant found no node stating the integral normalization. No unit realized fields are appropriate for this supporting item.

## Not duplicates

No new nodes are proposed. Reused `lem-sfb-induced-module-primitive-line` for the geometric field assertion and `lem-sfb-dvr-rho-section-modules` for integral finiteness and the actual rational coaction. In particular there is no new node restating one of the item's conclusions.

## Review by Q03

I read Milne, Algebraic Groups, Definition 22.21, Proposition 22.22 and its proof on printed pp.468--469 (PDF pages 480--481), including the inverse in the right-character convention and the final torus-weight calculation. I also read Stacks algebra.tex lemma-flat (00HD) and lemma-flat-localization (00HT), morphisms.tex lemma-flat-characterize (01U5), and varieties.tex lemma-smooth-geometrically-normal (056T). No new node requires a separate source review. I opened the statement of every existing node cited by the proof and checked the following uses.

Step 1 takes nonzero finite freeness and the rational left coaction from the exact integral rho-module node. PID Noetherianity is in lem-weil-pbc-pid-noetherian-normal. Smooth-unipotent-solvable excludes normal unipotent radicals in the semisimple fibres, making them reductive. The local Borel-geometry node assumes a nonzero Noetherian local base and a split Borel pair; these hypotheses hold here, and its statement gives the smooth radical, semidirect decomposition, arbitrary base-change compatibility and geometric positive-root comparison. Smoothness implies flatness by sbc-lem-smooth-criterion, the affine criterion converts this to flatness of R and D, and flat-module-torsionfree-domain gives precisely the cancellation needed later.

Step 2 uses localization-flat for K/A, module-over-field-flat for E/K, and flat-tensor-exact for the kernel of the written right-equivariance difference map. The cited affine fibre-product spectra node gives exactly the tensor coordinate rings and projection maps; the multiplication and action maps base change by their coordinate maps. Nonvanishing after extension follows from the nonempty finite basis, without a residue-field cohomology theorem.

Step 3 applies induced-module-primitive-line over E, which is algebraically closed, to the nonzero module E_B(-m rho). Its statement supplies both the U-fixed line and its full group-scheme torus weight. The minus sign is necessary: w0(-m rho)=m rho. The positive-root reversal proves w0 rho=-rho in the integer character lattice, so this remains valid in characteristic 2. The B=T semidirect V decomposition from Step 1 turns the two identities into the B eigenvector identity over every scalar algebra.

Step 4 applies the same flat-tensor-exact statement to the separate, explicitly written left-eigenvector difference map. Its nonzero kernel after E-extension implies a nonzero K-kernel. This requires only flat field extension, not exactness of reduction modulo the maximal ideal.

Step 5 uses a finite basis and the discrete valuation description in def-sc-discrete-valuation-ring. Multiplication by the inverse minimum coordinate valuation makes a primitive vector. Since W tensor D is a finite direct sum of the torsion-free D, the eigenvector equation descends from its localization. Replacing b by its inverse gives precisely the requested negative exponent for left multiplication. This is an elementary coordinate and localization argument from previous steps, not an unnamed representation-theoretic input.

Step 6 uses flat-tensor-exact on the injection given by multiplication by the uniformizer on R, with D flat. This proves cancellation in R tensor D and therefore W intersect pi R = pi W. The primitive vector consequently has nonzero reduction as an actual regular function, not merely as an abstract class of W/pi W.

Step 7 uses smooth-geometrically-reduced for the closed fibre, and reduced-dense-image-schematic with quasi-compact, quasi-separated cell map (both schemes are affine). The scheme-theoretic-image definition then identifies the zero kernel with injectivity of restriction of regular functions. These cited statements say exactly what is needed. The cell identity is written out and forces the evaluation to have nonzero residue. Step 8 divides by this unit and checks both normalization and the universal left-equivariance identity.

Small cases: for SL2 with B upper triangular, write g=(a b; c d), rho(diag(t,t^-1))=t, and n0=(0 -1; 1 0). The function c^m lies in W_m, has value 1 at n0, and its left B character is t^-m, confirming both signs. The same calculation works in residue characteristic 2 and over mixed-characteristic DVRs. For the trivial group, W_m=A and f_m=1. Scaling a primitive w by pi would indeed destroy its closed-fibre evaluation, explaining why primitive choice is required.

Against delivery-errors B--E: there is no new unsplit node or hidden proof in a statement; all objects and signs remain those of the item. Every non-elementary step cites the exact existing statements it uses, and citations.json copies their words. There is no cycle through the double-flag parent: it is not cited. No clause is moved wholesale to a new node. The two kernel calculations, primitive scaling, saturation and cell evaluation carry the integral proof explicitly. Each step is below 2000 characters, so no long step conceals another source lemma. Mathlib results from both semantic phrasings, Loogle and grep were read; discrete-group induction and Lie algebra weight chains do not give this group-scheme assertion. All cross-unit proof citations are existing Mathlib leaves or closed nodes, so no new tool-use approval is requested.

## Unfinished work

None in this stage-1 item. Existing dependency nodes retain their own independent status. Required delivery checks and push follow this self-review.
