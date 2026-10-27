# Worker report — Q30

Item: lem-sfb-bialgebra-distribution-tangent-calculus. Stage 1 only, 2026-10-24.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-bialgebra-distribution-tangent-calculus.json: statement, split; no whole-item Mathlib match. Twelve explicit steps, using three existing nodes; no new nodes and no new Mathlib leaves.
- citations.json: one verbatim statement quotation for each of the five step/node citation pairs.
- report.md: this report. searches.jsonl is the actual search-command log; write_split.py is a sandbox-only drafting helper, not a project file.

## Attachments

None. Searched the project library for the exact blueprint id and the notions bialgebra, convolution, augmentation, tangent and invariant derivation. Bialgebra.exists_derivation_counitAlgHom_comp and Bialgebra.exists_derivation_of_cotangent in WeilConjectures/RingTheory/HopfAlgebra/Cartier.lean:466,501 are related partial statements: their conclusions only assert a derivation with prescribed counit values. They do not state its invariance, uniqueness, the finite-order convolution filtration or the bracket formula. They therefore do not attach the item. I read lines 436–510, including their exact hypotheses, conclusions and proofs; the split does not take extra facts from their proofs as an uncited black box.

## WANTED

None. Milne's Algebraic Groups is present and was read at printed pp.195–196 (PDF pp.207–208), Propositions 10.28–10.29 and their proofs, and printed p.208 (PDF p.220), section 10(l). No SGA source is used. No Stacks theorem is needed beyond the existing tensor-product definition; its recorded source is Tags 00CW/00CX in algebra.tex.

## Corrections and scope

The imported statement is mathematically correct. I kept every hypothesis and every conclusion, adding only the citation of the existing tensor-product definition at its first use. In particular C is not assumed finite-dimensional, finite type, smooth, connected or Hopf; there is no characteristic restriction. Milne states his application for coordinate Hopf algebras, but all the displayed derivation and distribution calculations use precisely the bialgebra axioms stated here. No antipode enters the proof. There was no earlier item copy, split or report in the sandbox, and no repair note in the repository.

The proof route remains the existing supporting chain for the rational distribution/enveloping comparison. I read the chapter record, the unit record and the latest main-20261024 blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md, its proof and its direct-images proof (3). The pre-existing long ancestry records the supporting alteration/representation input below that step. No unit realization fields are changed: this item is not the unit's key statement. blueprint_refs.py ancestor prints null, so I preserved its from.node and via instead of inventing a blueprint ancestor. Whole-blueprint searches for convolution, derivation, bialgebra, left-invariant, distribution and cotangent yield no equal statement. The cotangent search does find the algebraic-group Lie/tangent definition, which has stronger characteristic-zero/algebraic-closure hypotheses and does not state this bialgebra result.

## Searches and reuse

All new searches were made with the prescribed msearch.py Q30/item command and are copied exactly from searches.jsonl into mathlib_searches, alongside the item's inherited searches. I read the returned signatures and the relevant local sources. The first semantic phrasing returned manifold LeftInvariantDerivation: it assumes a nontrivially normed field, model with corners and smooth-function algebra. The second phrasing returned LinearMap.convMul/convRing/convOne and Bialgebra.mul_compr₂_counit: these give full-dual convolution or counit multiplicativity, not the order filtration and tangent comparison. LeanSearch and a Loogle follow-up returned Derivation.instLieAlgebra, which only supplies the commutator structure on all derivations. Coalgebra, Derivation gave no Loogle hits. The Bialgebra grep for augmentation/distribution/invariance/derivations gave no hits. No service in these new searches was unavailable.

The full-dual convolution result already exists as lem-sfb-convolution-linear-map-algebra, a Mathlib leaf; I opened its whole statement and match and read Coalgebra/Convolution.lean:55–68,174–193,212. I reuse it directly, instead of creating another leaf. The Lie-algebra definition already explicitly states the End(V) commutator example and the assertion for commutator-closed subspaces; I opened that whole node. No generic derivation-commutator child is necessary: the two Leibniz expansions are written in step 10. The augmentation splitting, cotangent functional extension and invariance computations likewise are the proof steps themselves, not new nodes that merely restate clauses of the item.

## Not duplicates

No new nodes. Existing lem-sfb-convolution-linear-map-algebra is cited for precisely the full-dual convolution algebra clause. Existing lem-ag-lie-identity-cotangent-dual concerns the local ring of an arbitrary group scheme and its tangent Lie algebra, not the present explicit augmented-bialgebra functional calculation. def-wf-lie-algebra-derivation assumes characteristic zero and an algebraically closed field. Neither can be used as this item's assertion in arbitrary characteristic. The whole DAG search also found the Hopf monomial pairing and characteristic-zero enveloping comparison nodes; those need the present calculus and are not cited back, avoiding a cycle.

## Review by Q30

I checked delivery-errors B–E against the actual node files and sources. There are no new unsplit statements to check for hidden proofs or duplicate tags. The item introduces all objects itself and the added tensor-definition edge now accounts for its tensor notation. Its statement has no changed mathematical content. Its twelve steps are each under 600 characters, so none hides a lemma in a step longer than 2000 characters.

Steps 1 and 2 use def-weil-pbc-module-tensor-product only for bilinearity, tensor maps and generation by simple tensors, which its statement expressly supplies. The projections c ↦ epsilon(c)1 and p(c) give the four tensor slots directly. For x in I the scalar slot vanishes by applying the two counits; the other slots each have an I factor. This proves the needed ideal containment rather than assuming an unquoted coideal theorem. Step 3 expands a product of r+s+1 such sums. If the first tensor slot has at most r I factors, the second has at least s+1; otherwise the first has r+1. This proves the order bound without assuming finite generation of I. Coefficients in an ideal-power generator can be absorbed into its first I factor, since r+s+1 is at least one.

Step 4's cited convolution node states associative unital convolution on Hom_R(C,B), its unit and scalar map without finiteness or cocommutativity. Taking R=B=k meets every hypothesis: the stipulated linear coalgebra maps satisfy precisely those counit/coassociativity identities. The remaining subspace, nestedness and subalgebra checks are written in that step, with multiplication closure from step 3. No ideal-power/tensor exactness theorem is being assumed.

Steps 5 and 6 prove both directions of L=(I/I^2)^*: the equation v(1)=2v(1) is solved by subtraction, not division by 2, so characteristic 2 is included. Conversely the p(a)p(b) term vanishes modulo I^2. These are direct calculations with the given Leibniz identity and the scalar splitting, with no external tangent-space comparison invoked.

Step 7 uses the tensor-definition node to choose finite-sum notation; the source's map (id tensor v)Delta is a derivation by the displayed multiplication expansion and counit contractions. Step 8 uses coassociativity for its invariance and the opposite counit for epsilon D_v=v. Step 9 checks epsilon D is a tangent functional and derives the other inverse by applying id tensor epsilon to Delta D=(id tensor D)Delta. I checked which counit contraction is used at each occurrence; neither inversion in a group nor a finite-dimensional duality is needed.

Step 10 expands DE and ED on ab, cancels the two middle terms, and composes the invariance identities in the specified order. Step 11 cites def-wf-lie-algebra for the exact sentence giving End(V) and its commutator-closed subspaces as Lie algebras; it is not using a definition as a substitute for an unstated theorem. Transport through the already proved linear bijection gives the bracket on L. Step 12 evaluates epsilon D_vD_w on c and gets sum v(c_1)w(c_2), which is v*w, not w*v. This confirms the sign and factor order in the item's final formula. citations.json contains verbatim statement text for every cited pair; no proof text is substituted for a statement quote.

I tested the statement on C=k (I=L=0, F_n=k epsilon); the additive bialgebra k[t] with Delta(t)=t tensor 1+1 tensor t; the multiplicative monoid bialgebra k[t] with Delta(t)=t tensor t and epsilon(t)=1 (D_v=t d/dt, so the absence of an antipode is harmless); k[t,t^{-1}]; and alpha_p, C=k[t]/(t^p) with primitive t in characteristic p. In alpha_p the first tangent derivation is d/dt and remains well-defined because p=0; no factorial inverse or characteristic-zero step occurs. For a sign check, in the coordinate bialgebra of the matrix monoid Delta(x_ij)=sum_l x_il tensor x_lj, a matrix tangent A gives D_A(x_ij)=sum_l x_il A_lj. Consequently epsilon(D_A D_B)(x_ij)=(AB)_ij and the bracket is AB−BA, exactly the final formula. These tests cover zero tangent dimension, non-Hopf bialgebras, positive characteristic and a noncommutative convolution example.

## Unfinished

None in the requested stage-1 split. No Lean file was written, no compiler/Lake/build tool was run, no sub-agent was started, and no repository or launcher file was changed. Delivery validation is performed only by the required server dry run.
