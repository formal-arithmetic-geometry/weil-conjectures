# Stage-1 delivery: lem-sfb-finitely-generated-residue-perfect-core

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finitely-generated-residue-perfect-core.json: statement, split; no Mathlib match for the whole item.
- citations.json: verbatim statement quotations for all eight step/node citations.
- searches.jsonl: actual search-command log; item queries and supporting Laurent/Frobenius queries.
- report.md: this report.

No new nodes and no new Mathlib leaves. All necessary supporting statements already exist.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag, perfect-core wording, Frobenius intersections and infinitely divisible elements found no declaration of this item. The existing intersection_subfields_differentials_powers theorem has a different statement (one Frobenius image and composita in a finite extension), so is not an attachment.

## WANTED

None. The ILO PDF and Stacks sources are available locally.

## Findings and changes

The item statement is retained verbatim, including algebraic extensions and empty generator lists. The initial node had no proof. I read ILO Expose IV 3.2.1, Lemma 3.2.2 and Proposition 3.2.3(i)-(iv), printed pp.55-56 (PDF pp.61-62). The proposition supplies finite-extension stability and the Laurent calculation. Its rational-function consequence is expanded explicitly. Stacks 030F, fields.tex label lemma-transcendence-degree, supplies a finite transcendence basis; 09GH, label lemma-algebraic-finitely-generated, gives finiteness after adjoining finitely many algebraic elements. The source's one-variable Laurent computation is realized by the existing coefficientwise Frobenius leaf followed by support divisibility, rather than by citing a definition as a theorem.

The latest blueprint sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), now routes through proper and open direct-image preservation and does not state this historical Epp supporting result. I retained the item's existing null blueprint ancestor and creation-chain provenance, and recorded the historical relationship in split_report. No chapter or unit route is changed and no unit realization fields are owned by this auxiliary item.

## Not duplicates

No nodes created. Searches of the whole DAG for the ILO source place, perfect core, Laurent series and transcendence bases found lem-per-finite-extension-perfect-core, lem-per-epp-perfect-core-complete-local, lem-per-separable-closure-perfect-core and the relevant proper-base-change Mathlib leaves. I reused the finite-extension theorem rather than restating it. The complete-local theorem requires a complete Noetherian local domain and a residue hypothesis; the separable-closure theorem concerns an algebraic separable closure. Neither is the present finitely generated field statement. Whole-blueprint searches using tools/blueprint_refs.py for perfect core, transcendence, Laurent and perfect field found no equivalent blueprint statement.

## Review by NC

I checked B-E of delivery-errors.md against the item, all cited statements, ILO IV pp.55-56, Stacks 030F/09GH, and the latest blueprint proof. There are no statement-only new nodes to review, no new objects hidden in a theorem, and no new duplicate or clause of the item moved to another node. The finite-extension result is an existing independently split node with its own strictly more general hypotheses, not a new substitute for the item.

Step 1 cites the finite-transcendence-basis statement for an algebraic extension over a rational subfield and the algebraic-generators statement for finite dimension. I read both statements. Finite generation of l over k is in the item; l=F(a_1,...,a_m) follows because k is contained in F and the a_j already generate l. Thus the latter statement's hypotheses hold with base F, even if the generators are empty. Both are existing Mathlib leaves. I also read the pinned declarations exists_finset_isTranscendenceBasis and IntermediateField.finiteDimensional_adjoin.

Step 2 cites the Laurent-series definition only for bounded-below coefficients and the coefficientwise power-series Frobenius statement for the actual power identity. I read both statements and MvPowerSeries.map_frobenius_expand in the pinned source. The shift t^N makes a power series, its p-th power is covered by the cited theorem, and multiplication by t^(-pN) restores the original exponents. Induction includes n=0. This is a few-line specialization, not an unrecorded analytic convergence theorem.

Step 3 uses the identity established in Step 2. For each n a root forces the support into p^n Z. Every fixed nonzero integer fails divisibility once p^n exceeds its absolute value. Coefficient zero supplies roots in H. This proves the two inclusions of the core equality in a few lines; zero is harmless. It does not assume H perfect. There is no non-elementary external input in this step.

Step 4 cites the Laurent-field statement for the field structure of every L_i and the transcendence-basis definition for injectivity of the polynomial presentation of F. I read both statements and HahnSeries.instField. The injection into L_r is checked by recursively comparing coefficients of a finite polynomial, and its extension to fractions sends a/b to the quotient of their images; injectivity ensures denominators stay nonzero. Roots remain roots under an injective field map. Inducting the equality of Step 3 r times gives the same constant k; k_perf=k uses precisely the item's surjective Frobenius hypothesis. When r=0 no series are introduced. No finite extension or algebraic constant was mistakenly identified with the base at this stage.

Step 5 cites lem-per-finite-extension-perfect-core. Its statement explicitly assumes only finite dimension and characteristic p, and concludes algebraicity over the lower perfect core, without separability. Step 1 verifies finite dimension and both fields have characteristic p. Step 4 identifies F_perf with the specified k. The quoted sentence is exactly the algebraicity assertion this step uses. This off-unit statement is declared as a generic tool use in split_report.tool_uses, with its purpose explained; its source is ILO IV Lemma 3.2.2 and Proposition 3.2.3(ii). I read its complete statement and proof to check that it does not depend on this item.

Step 6 cites the separable-algebraic definition for the monic irreducible minimal polynomial and the coprimality criterion. I read that statement. Algebraicity is already proved. Vanishing derivative forces only exponents divisible by p, and the hypothesis on k supplies coefficient roots, contradicting irreducibility through P=Q^p. Nonzero derivative has smaller degree, hence is coprime to irreducible P. This is an explicit short polynomial argument; perfectness is not used as an uncited theorem.

I tested the statement and steps on l=k, a finite extension of a finite field, k(t), k(t_1,t_2), an inseparable finite tail over a rational function field, x=0, p=2, n=0 and an empty basis. The finite-tail theorem requires no separability and therefore covers that edge case. The infinite perfect closure of F_p(t) illustrates why finite generation is essential; it is not a counterexample to the item. I found no statement dispute. Every proof step is under 1000 characters; none approaches the 2000-character long-step threshold. The only non-elementary steps apply the exact cited statements; all elementary steps show their calculations explicitly. All citations.json quotes are copied verbatim from those statements.

The Mathlib searches are the actual msearch.py queries in searches.jsonl. Relative perfectClosure is the maximal purely inseparable algebraic subextension (I read its definition and membership equivalence in FieldTheory/PurelyInseparable/PerfectClosure.lean), not the intersection of Frobenius images. Supporting hits map_frobenius_expand, Laurent-series field instances and finite-transcendence-basis statements are already represented in the DAG and were reused. No new node was needed for a generalization already present in Mathlib. No SGA route, Lean writing, compiler, Lake or build tool was used.

## Unfinished work

None in the one-level split. Required dry run and direct delivery follow this review.
