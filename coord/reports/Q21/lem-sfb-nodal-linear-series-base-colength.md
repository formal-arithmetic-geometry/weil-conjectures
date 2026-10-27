# Stage-1 report: lem-sfb-nodal-linear-series-base-colength

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-linear-series-base-colength.json: statement, split into six steps; not a Mathlib leaf.
- citations.json: verbatim statement quotations for every proof-step citation.
- report.md: this report. searches.jsonl records the actual msearch invocations; write_split.py is sandbox-only scratch work.

No new nodes; zero Mathlib leaves. No Lean files written or compilers invoked.

## Attachments

None. Searches for the exact blueprint tag and for base-colength, evaluation image, base ideal, nodal and ordinary-double-point concepts in lean/WeilConjectures found no declaration stating the item. AmpleProjPreimage.lean concerns inverse images of Proj basic opens, not this theorem. The searches also checked lean/Sheaf as additional reference material; these cannot establish an attachment under this brief.

## Literature wanted

WANTED: literature/franciosi-tenni-clifford-singular-curves-2014.pdf, Proposition 2.17(ii), printed p.233, and Theorem 3.9 proof, printed p.247, for lem-sfb-nodal-linear-series-base-colength. The local PDF is absent. I read the author-hosted primary PDF at https://pagine.dm.unipi.it/franciosi/lavori/clifford.pdf online (PDF pages 9 and 23). The proof is consequently marked agent, with the explicit evaluation construction and local arguments in the node. No literature was downloaded into the repository.

## What needed correction

The item had no proof. Its statement is unchanged, including every boundary, finiteness and section-space clause. No statement dispute was found. The imported blueprint provenance named det-thm-sf-ctf-stability-direct-images but had from.node=null. The created.item chain is broken at an intermediate record: blueprint_refs.py ancestor returned None. I retained the inherited place and via list, and filled from.node with that existing blueprint node. I read its current latest blueprint proof: clause (3) is the direct-image/compactification route served by this descendant. Searches of the whole blueprint for nodal, linear series, base locus and 0E38 found no alternate statement of this item; same_as remains empty.

## Not duplicates

No nodes created. During preparation I considered a local two-branch intersection prerequisite. Searching the DAG found lem-trf-stacks-nodal-closed-subcurve, whose statement already supplies the required reduced boundary. I reused it and discarded the proposed new node. Its 0E38 source was read in curves.tex, including the local branch argument. The exploratory local-ring Mathlib searches remain honestly logged, but no node or false Mathlib claim was made from them.

## Review by Q21

I read the worker brief, stages/1-dag.md, the three SETUP levels, GOAL.md, the chapter and unit records, and delivery-errors B through E. There is no repair-note file for this item. The current statement is a supporting lemma below the stable-curve branch of direct-image constructibility; it does not replace a unit step. Off-unit tools are individually declared in split_report.tool_uses.

For the item I read the primary Franciosi–Tenni discussion at the places above. I checked the Stacks sources actually needed for the proof: modules.tex 01BY (lemma-coherent-abelian); coherent.tex 01XZ (lemma-coherent-Noetherian); curves.tex 0E38 (lemma-closed-subscheme-nodal-curve); varieties.tex 06LH (lemma-algebraic-scheme-dim-0), 0AYY (lemma-degree-effective-Cartier-divisor, dimension argument), 08AA (lemma-euler-characteristic-additive) and 0AYT (lemma-chi-tensor-finite). There are no new nodes whose sources require separate review.

Step 1 uses lem-kun-projective-implies-proper exactly for properness; lem-trf-proper-field-invertible-coherent exactly for Noetherianity and coherence of O_X and L; lem-weil-pbc-coherent-modules-kernel-cokernel-sum for finite sums, cokernels and kernels; def-sc-invertible-module for local rank one. I opened all four statements. The evaluation image is obtained as a kernel into its cokernel, not assumed coherent without a cited closure result. Its local generators and change of frame are written out.

Step 2 uses lem-pc-nowhere-dense-dim-zero only after checking finite type, dimension one, and absence of every component generic point from the zero scheme. At a reduced generic stalk a nonzero coefficient is a unit. Then lem-pc-zero-dimensional-closed-subscheme-finite gives the finite-dimensional section algebra, exactly as its statement says. In particular I did not take that stronger finiteness conclusion merely from the topological finite-set lemma.

Step 3 uses lem-trf-stacks-nodal-closed-subcurve for the scheme-theoretic intersection, not just the existence of two branches in the normalization. The reduced component unions satisfy its pure-dimension and finite-type assumptions; the stated split completions and algebraically closed field give its residue-field hypotheses. I explained why the scheme-theoretic complementary closure is the reduced complementary union. Its output is a disjoint union of spectra of finite separable extensions, all equal to k here. The definitions of reduced schemes and fibre products supply their precise meanings. This proves the block-boundary assertion, including its scheme structure and length.

Step 4 writes the reduced-ring reason that generic vanishing on a component union is actual vanishing there. It then checks residues of each supported summand at a joining node. The ideal-sheaf definition identifies vanishing on the reduced finite node scheme with membership in its ideal. I checked the exact statements of the coherence closure lemma, pqf-lem-coherent-ft-locnoeth, lem-pc-euler-additive and lem-pc-chi-zero-dim-support: they give coherence and Euler/dimension equality for the displayed exact sequence. The zero-dimensional support condition holds for every term. Thus no unjustified claim that arbitrary global sections preserve epimorphisms is needed.

Step 5 is elementary: each global section supplies its own evaluation preimage, and the subsheaf inclusion is injective on sections. The equality is inside the specified section space, not just an abstract vector-space isomorphism. It uses no external theorem and has no node citations.

Step 6 uses the effective-Cartier-ideal definition to give the actual local multiplication isomorphism a↦ta, using that t is a nonzerodivisor. This proves invertibility and identifies the tensor product with the product ideal without an unproved flat-tensor assertion. Its zero scheme is contained in the union of the two finite supports, so the finite-subscheme node applies. I opened the Euler-additivity and zero-support tensor-invariance statements again: the latter applies with the invertible module I_T and F=O_X/B, and yields exactly the needed left-term dimension. The displayed coherent exact sequence then proves length additivity. Finally the equality of subsheaves of omega_X follows from the same explicit multiplication and Step 5. The construction needs no claim that the enlarged base scheme is Cartier.

Small cases checked: X=P^1 and V generated by a nowhere vanishing section (B=O, empty Z, b=0); a section with a zero of order d on a smooth curve (local quotient k[t]/t^d); two smooth components joined at a node with supported summands (each summand has zero residue at that node); an irreducible self-node (no inter-block edge); a one-block partition (empty boundary); T empty; and local Cartier multiplication at a node, where a nonzerodivisor t can vanish on both branches. The formula length(R/tB)=length(R/tR)+length(R/B) follows through the displayed sequence, including non-Cartier B. None of these needs two-connectedness, characteristic zero, or Cartierness of the enlarged scheme. Those hypotheses were not inserted.

I checked B1–B10: no new nodes, no undeclared definitions, statement unchanged, actual Mathlib queries recorded, blueprint provenance repaired, and no project attachment. I checked C1–C8 by opening each cited statement and retaining the exact part it supplies; the tools do not depend back on this item. I checked D1–D5: the six steps carry the argument and do not move a clause into a replacement node. I checked E1–E7 through the hypotheses and small cases above. Every step is shorter than 2000 characters; the longest is the explicit Cartier calculation. There is no hidden comparison or omitted local lemma in a long step.

## Remaining work

No mathematical part is left unfinished. New prerequisites: none. Delivery remains subject to the required server dry run and push.
