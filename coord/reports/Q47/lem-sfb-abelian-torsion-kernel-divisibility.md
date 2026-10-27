# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-abelian-torsion-kernel-divisibility.json`: split the item into seven steps, retaining its statement, statement dependencies, source, provenance and ancestry. No new nodes; no new Mathlib leaves.
- `citations.json`: fifteen step/node records, each quoting the complete statement of the cited node verbatim.
- `searches.jsonl`: the unmodified search-command log. Five fresh searches supplement the item's five inherited searches, which have been retained.

## Attachments

None. Searched `lean/WeilConjectures/` by the blueprint tag, torsion factorization and divisibility language, and inspected the abelian-variety isogeny and torsion sources. Their proved declarations establish multiplication isogenies and étaleness, not the requested algebraic factorization. Abstract quotient-group declarations are not attachments.

## Literature wanted

WANTED: none. Every source needed is already available in the read repository.

## Defects found and changes

The item was an unsplit, correct statement. Its pointwise hypothesis needs an explicit bridge to the scheme-theoretic kernel. Its citation of Milne 8.12 must not be used as if the stated example for separable isogenies alone proved the claim for an arbitrary homomorphism. I supplied that argument using existing finite-étale classification and fpqc descent nodes. This also avoids importing any assertion that a bijective morphism is automatically an isomorphism. The source statement and its hypotheses have not changed, and there is no statement dispute.

The inherited `blueprint.from.node` is null: `tools/blueprint_refs.py ancestor` also returns None. Its detailed `from.place` and `via` are unchanged. The item is not the unit's key theorem, so no unit realization record is changed. The inherited unit names the old six-functors unit while the chapter field names six-functors-basics; both are preserved as required. `coord/dag-sync.md`, requested by the older standing brief, is absent; the current direct-delivery instructions and live read repository supply the workflow.

## Proof and searches

Read Milne, *Abelian Varieties*, Chapter I, Remarks 8.11(f) and 8.12 (printed p.39), Lemma 10.16 (p.49), and Proposition 14.4(b) (p.62). The proof keeps the quotient-by-torsion route: rather than assert the quotient's universal property, it realizes it by Stacks 023Q. `proof_origin.by` is agent because this explicit scheme-theoretic expansion is written here, not copied from a single source proof.

The existing closed nodes `lem-sc-isogeny-facts`, `lem-sc-mult-n-etale-kernel`, `lem-sc-finite-etale-algebra-criterion`, and `lem-sc-av-commutative` give the substantive abelian-variety inputs. The existing Mathlib leaf `lem-galois-fpqc-covering-base-change` gives stability of coverings. The off-unit node `lem-weil-pbc-fpqc-representable-descent` is declared as a generic tool in `split_report.tool_uses`; it supplies precisely the scheme-morphism equalizer property, not object descent or a special quotient theorem.

Read every hit returned by the fresh searches. LeanFinder's first phrasing returned abstract quotient groups and cyclic-group maps; its second returned affine algebra quotient lifts and unramified algebra uniqueness. LeanSearch returned torsion subgroups, abstract divisibility, ZMod.lift and ModuleCat.hom_nsmul. None supplies a morphism of abelian varieties. Loogle returned zero hits, and the logged Mathlib AlgebraicGeometry grep for isogeny/IsIsogeny/AbelianVariety returned zero hits. All five queries are recorded exactly from searches.jsonl with their actual outcomes; no service was unavailable. Whole-DAG and whole-blueprint searches for isogeny, quotients, fpqc, torsion kernel, separable isogeny and divisible by found the reused nodes but no equivalent statement. No new node is needed.

## Unfinished work

None in the requested one-level split. Existing cited nodes retain their own downstream work; this delivery neither changes them nor claims their Lean proofs where no closed audit exists.

## Review by Q47

I read the whole of delivery-errors B–E (both copies) and checked the seven actual steps against the cited statements, not their proof sketches. I read Stacks groupoids.tex at 0BFG, 0BFH and 03RP, morphisms.tex at 02GL, descent.tex at 023Q, and topologies.tex at 022D. Milne's quotient universal property explains the route and the use of divisibility in 10.16 and 14.4(b). There are no new-node sources to audit.

Step 1 uses lem-sc-av-commutative for commutativity of both A and B, lem-sc-isogeny-facts for finiteness, flatness and surjectivity of q, and lem-sc-mult-n-etale-kernel for finite étaleness of K. Each node's statement gives exactly that fact. The field is algebraically closed, n is positive, and n invertible is precisely the prime-to-characteristic hypothesis. Only the forward étaleness implication is used, including in dimension zero.

Step 2 uses the definition of finite morphism, which explicitly includes affineness, and the definition of fpqc covering. For an affine target open V, the single affine q^{-1}(V) covers it by the already proved surjectivity. Flatness is already supplied by step 1. This is a direct verification of the definition, so its elementary flag does not hide a base-change theorem.

Step 3 uses def-sc-group-scheme to identify the finite kernel with Spec of a finite-dimensional algebra, the full equivalence in lem-sc-finite-etale-algebra-criterion to express it as a product of finite separable extensions, and def-weil-algebraic-closure for splitting minimal polynomials. The argument that every extension factor equals k is written out. Finite products of fields have disjoint spectra, so equality on these components is equality of scheme morphisms. Thus the use of k-points is justified by finite étaleness, not by a general assertion that schemes are determined by their rational points.

Step 4 uses the group operations and kernel from def-sc-group-scheme and the multiplication homomorphism from def-sc-mult-n. The kernel-pair identification is given in both directions by (a,t) -> (a,a+t) and (a,b) -> (a,b-a), with the inverse calculation and kernel membership written out. This is a short direct calculation from the group laws, not a new lemma. The two pullbacks of f agree using the scheme-level vanishing established in step 3. No finite-kernel quotient theorem is used without a node.

Step 5 uses exactly the existence and uniqueness clause of lem-weil-pbc-fpqc-representable-descent. Step 2 gives its fpqc hypothesis and step 4 its overlap equality. Applying its uniqueness with target Spec k verifies that the descended scheme morphism is over k. The cited statement allows every scheme as target; this is not borrowed from a definition of the fpqc topology.

Step 6 uses lem-galois-fpqc-covering-base-change for each of q x id and id x q, and the uniqueness clause of lem-weil-pbc-fpqc-representable-descent for cancellation of each cover in succession. The equality after q x q is written as an identity of group-scheme morphisms using the actual equation g q = f: g(q(a+b)) = f(a+b) = f(a)+f(b). In particular no surjectivity of q on arbitrary T-points is assumed. The identity element is checked separately, and the operations and definition of homomorphism are those of def-sc-group-scheme.

Step 7 uses the full scheme-morphism uniqueness already obtained, and def-sc-mult-n to identify composition with [n] with the n-fold pointwise sum on every test scheme. This proves both the uniqueness and the Hom-group formulation rather than omitting the final clause.

For B, there are no new statement-only nodes to type-check or duplicate; all notions introduced in the unchanged item retain their actual definition dependencies. For C, all fifteen cited step/node pairs have verbatim quotation records; every non-elementary input is cited, all cited nodes are unmerged, and none depends transitively on this item. The generic descent tool is explicitly declared instead of silently changing the unit route. For D, the argument stays in the item's seven steps; no clause is merely moved into a new node, and the kernel-pair formula is an elementary calculation. For E, checked n=1 (q=id and g=f), A or B the zero-dimensional abelian variety, and f=0 (unique g=0). Checked why algebraic closedness and invertibility are used at step 3: finite étale kernels split into k-points; without étaleness one cannot infer scheme vanishing from rational-point vanishing. No polarization, dimension, separability of f, or finiteness of f is added. Each step is under 1000 characters, so none triggers the long-step review threshold.

## Not duplicates

No new nodes. Reused the existing finite-étale classification, multiplication isogeny/étaleness and fpqc descent statements instead of introducing special cases.

## Repair of the returned delivery

The return was a promotion failure, not a mathematical rejection: L approved the reader's split but the queue's live DAG still held the unsplit item. The sandbox retained the reviewed seven-step split and its search log. Its previous durable receipt names head `d2d1610d46c`; the required initial dry run rebuilt the retained delivery on the current DAG and passed at `2f95cb88096` before these repair edits. This delivery is rebuilt by deliver.py on its freshly fetched base, rather than re-pushing that old head.

Compared the retained item with the current read repository: the live item has empty proof/proof_deps and status unsplit. The statement, statement dependencies, source, title, creation record and blueprint ancestry agree exactly. There is no released repair note for this item. I retained the existing proof, literature citations, full report and every logged search. No new statement or search question arose, so no search was repeated.

I re-read all current statement dependencies and every proof dependency. All fifteen retained citations.json quotations are still verbatim substrings of their respective current statements, so none of the mathematical premises quoted in the returned split has changed. In particular finite étale classification still gives a product of finite separable extensions, the isogeny node still explicitly gives finiteness/flatness/surjectivity, the base-change node still concerns fpqc coverings, and representable descent still supplies both existence and uniqueness for arbitrary target schemes. The hypotheses in steps 1–7 remain satisfied as described in Review by Q47.

I also re-read Milne I, Remarks 8.11(f), 8.12 and Lemma 10.16, and Stacks 023Q, 022D, 02GL, 0BFG, 0BFH and 03RP from the local sources. The use of 0BFH remains only its forward direction for invertible n; the zero abelian variety is covered as well. I repeated the project-source attachment search, including the abelian-variety isogeny and torsion modules: the exact factorization statement is still absent. All existing Mathlib search results are retained and read; none constructs the required algebraic homomorphism.

For this repair I clarified step 6 to name the two morphisms compared at each application of descent uniqueness: first cancel h_2 from L h_1 h_2 = R h_1 h_2, then cancel h_1. I also wrote preservation of the identity as equality of scheme morphisms. This makes explicit why no surjectivity on arbitrary test-scheme points is needed. The proof route and cited nodes are unchanged. All steps remain under 2000 characters. Rechecked n=1, f=0 and the zero-dimensional abelian variety; the original finite-étale bridge and uniqueness argument apply in each case. No new nodes or Mathlib leaves are introduced by this repair.

## Continued promotion repair against the current DAG

The retained previous repair receipt names delivery head `8fb92059efd`. On this continuation, the required initial dry run exited successfully with `OK (not pushed)` at `8006f4fa451`. It rebuilt the retained sandbox on the freshly fetched DAG; I waited for that invocation to exit before making these edits. The current read repository still has the unsplit item with empty proof and proof_deps. Its statement, statement dependencies, source and ancestry remain identical to the retained split. There is no released repair note.

I re-read the current statements of all thirteen distinct statement/proof dependencies and checked all fifteen citation records again: every quote remains verbatim and every step takes exactly the fact quoted. None requires a changed mathematical premise. The current project source has no declaration bearing this item's tag; the abelian-variety Isogeny and Torsion declarations concern multiplication, finite flatness, étaleness and torsion cardinality, not this factorization. I retained and read the existing search log rather than repeat unchanged search questions.

I re-read the local Milne text at Remarks 8.11(f), 8.12, Lemma 10.16 and Proposition 14.4(b), and the Stacks statements at 0BFG, 0BFH, 03RP, 02GL, 022D and 023Q. The nonzero hypothesis in the biconditional of 0BFH is irrelevant to the forward implication supplied by the cited node: the zero abelian variety has identity multiplication and trivial kernel. Étaleness, algebraic closedness and positivity are used exactly as in the signed seven-step review above. The n=1, zero-variety and f=0 cases still satisfy all steps.

This is not an unchanged re-push: besides recording the new comparison, I expanded step 4 to specify the actual scheme morphisms from projections, addition, inversion and the fibre-product universal property. This replaces the terse functor-of-points explanation without introducing a Yoneda or representability input. The inverse formula lands in the kernel because q(b-a)=0 on the kernel pair; the composites are the group-law identities already written there. This remains an elementary argument from the two cited definitions. Steps 1–3 and 5–7 retain their reviewed argument and every quotation remains valid. No new nodes, statement changes, new Mathlib leaves, or searches are needed. Every step is shorter than 2000 characters. The final dry run and push below are made from these updated sandbox files, so deliver.py rebases this repair instead of reusing the old returned commit.


## Promotion repair on 2026-10-23

The first required dry run of the retained delivery exited with `OK (not pushed)` at `5a0b742d807`. This is a fresh deliver.py rebuild on origin/sheaf-dag, not reuse of a returned delivery head; the previous retained receipt/report and their proof edits remain above as history. Compared the current live node with the retained returned version: the live node is still unsplit with empty proof/proof_deps. Statement, statement dependencies, title, source, creation record, chapter, unit and blueprint ancestry are identical. Only the split fields and five logged supplementary searches differ. No released repair note is present. Delivery uses the tool's freshly fetched current base again after these edits.

I re-read all thirteen distinct current statement/proof dependencies and checked every one of the fifteen citation records against those statements. All are still verbatim; no mathematical premise needs replacement. The present representable-descent node is itself marked Mathlib, and its statement explicitly supplies descent existence and uniqueness for every target scheme, as steps 5 and 6 require. The retained tool-use declaration is harmless and does not assert a new route. The old report's references to closed inputs describe their Lean audit rather than their imported/split status; this delivery only needs the statements and does not certify their downstream proofs.

This repair also updates the proof itself, rather than merely rebasing and re-pushing. In step 6 the two product covers are now explicitly identified as base changes along the first and second projections, with their pullback coordinates written out. This checks the exact hypothesis of lem-galois-fpqc-covering-base-change. The same step now verifies preservation of inversion as an equality after q, then cancels q by the uniqueness clause of lem-weil-pbc-fpqc-representable-descent. This uses only the already cited group-scheme operations and descent statement. Preservation of multiplication and identity, and the two successive cancellation applications, are retained. No new lemma or node is hidden in either added calculation.

For the signed Review by Q47 above, I again checked delivery-errors B--E in full, the chapter/unit route and the human's three blueprint levels. I re-read Milne I, Remarks 8.11(f), 8.12, Lemma 10.16 and Proposition 14.4(b), and local Stacks 0BFG, 0BFH, 03RP, 02GL, 022B, 022D and 023Q. Steps 1--3 still establish the finite-etale kernel and its scheme-level vanishing, step 4 establishes the actual overlap identity, step 5 descends a k-morphism, the repaired step 6 descends all group operations, and step 7 proves the Hom-group formulation and uniqueness. In particular the nonzero condition in the reverse direction of Stacks 0BFH is not used: only the invertible-n implication is cited, and zero-dimensional abelian varieties have identity multiplication. Rechecked n=1, f=0 and A or B the zero abelian variety. No hypothesis on f being an isogeny was introduced.

Repeated the project-source attachment search by exact blueprint id and torsion/factorization/divisibility language, and read the multiplication and torsion declarations in the abelian-variety Isogeny and Torsion modules. They do not state this algebraic factorization. Read and preserved searches.jsonl and all recorded results; the statement and search questions have not changed, so no Mathlib searches were repeated or invented. No new nodes, new Mathlib leaves or changed statements. All steps are under 2000 characters. The final dry run and push follow these updated files.
