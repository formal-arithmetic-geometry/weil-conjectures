# Stage-1 delivery: lem-sp-p1-splitting-scalar

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-p1-splitting-scalar.json`: item, statement; six-step split, no statement change. Mathlib searches find no match for its geometric derived-morphism assertions.
- `citations.json`: eleven verbatim statement quotations, one for every step/node citation.
- `report.md`: this report. `searches.jsonl` contains the required search-command records. `write_split.py` is sandbox-only authoring scratch work.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter record was edited: the item is a subordinate lemma of the coefficient-comparison unit, not its key statement.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id and for projective-line splitting/scalar and trace/coefficient combinations; inspected the Kummer class and boundary-comparison source. The existing geometric Kummer-class naturality concerns scheme pullback, and the coefficient boundary realization is not both of the present splitting and trace equations. There is no exact attachment found. No Lean file was written or compiled.

## Wanted literature

None. The blueprint and Stacks files needed for this argument are present.

## Corrections and scope

The imported statement needs no correction. Its proof was empty. The important distinction is between extending the actual derived Kummer morphism and tensoring a short exact sequence of abelian sheaves. The latter would need extra care for nonflat coefficients, so the proof uses the former, exactly as the statement defines the scalar-extended Kummer component. Similarly, the coefficient map is identified by its counit-transpose normalization, not by invertibility of an arbitrary map between split objects.

All eight original statement dependencies and the inherited provenance/search records are retained. The proof dependency list is exactly the union of the step citations. Generic tools in other units are declared in `split_report.tool_uses`, rather than setting the maintainer-owned `tool_uses` field. The chapter and the unit's route are retained: this proves the projective-line building block of the Charts paragraph of the coefficient-comparison argument.

## Not duplicates

No new node was created. Whole-DAG statement/title searches covered Kummer coefficient classes, scalar composition, ringed-topos derived composition, twist pullback, and adjunction mates. `tools/blueprint_refs.py search` was run for Kummer, scalar extension, normalized projective-line splitting, and coefficient compatibility; its ancestor command identifies `det-sp-reduction-exceptional`. The existing `lem-pur-kummer-coefficient-base-change` is about finite free modules on smooth curves over an algebraically closed field and cohomology groups. It does not give this lemma for an arbitrary nonflat ring map over a relative base. It is not used as a surrogate for the present claim. The broad ringed-topos composition lemma already in the DAG supplies the genuinely generic fact, so no new scalar-associativity or Chern-naturality node is needed.

## Review by Q69

I read `sk-lem-sp-reduction-exceptional.proof.md` in the main-20261015 snapshot, especially Charts, alongside the current unit and chapter records. I also read the scalar-extension proof in `sk-def-sp-scalar-extension-functor.proof.md`, the finite projective-line trace proof, and the trace definition. Charts says that the Kummer classes come from one common Z/ell^n class and that integration is projection in the splitting. Those are precisely the two constructions expanded here. This is marked agent-written because the blueprint itself is agent-written and the detailed mate calculation is supplied here.

For the technical foundations I read Stacks `sites-cohomology.tex`: `lemma-bounded-flat-K-flat` (Tag 06YQ), `lemma-pullback-K-flat` (Tag 0G7E), `lemma-derived-base-change` (Tag 06YY), `lemma-derived-pullback-composition` (Tag 0D6D), `lemma-pullback-tensor-product` (Tag 07A4), `lemma-adjoint` (Tag 07A6), and `remark-base-change` (Tag 07A7). The composition proof explicitly applies the second pullback to an already K-flat complex with flat terms; it requires no flat coefficient map. In `etale-cohomology.tex` I checked `lemma-kummer-sequence` (Tag 03PL): invertibility of N on the scheme is the hypothesis, as here. I did not use any SGA source.

Step 1 uses the actual statement of `lem-asd-finite-etale-twist-line` for local rank one and flatness, `lem-pc-kflat-closure` for the degree-zero flat models, and `lem-pur-derived-change-of-rings` for the exact scalar functor computed by these models. I checked the balanced isomorphism and its inverse on a tensor generator. Finite biproduct inclusions and projections are preserved because the functor is additive; this is not a claim that ordinary tensoring by B preserves every exact sequence. It is enough that the two particular source lines are flat over A.

Step 2 uses the definition of h in the statement of `lem-asd-ordinary-finite-p1-adjunction`: extend the fixed Kummer first Chern class, then take the inverse-image/direct-image adjunct. Thus the upstairs c_R is literally the scalar image of c_Lambda. I opened `lem-sfb-ringed-derived-monoidal-comparisons`: it states a canonical comparison for arbitrary ringed topoi computed by ordinary pullback composition on K-flat complexes, with no flatness or boundedness restriction. Identity topoi with structural ring maps Lambda -> A -> B meet these hypotheses. Naturality at c_Lambda is the written equation in Step 2; its source component multiplies units and its target component is the prescribed balanced map. I have not inferred arbitrary coefficient compatibility from base-change compatibility in the projective-line theorem.

Step 3 uses only the proper counit-transpose normalization explicitly stated in `lem-sp-et-proet-coefficient-compatibility`, and the full displayed mate-transpose statement of `lem-pur-adjunction-mate-transpose`. Their maps have the same direction: lambda goes from q_B^* T_S to T_P q_A^*, and beta goes from T_S Rq_A* to Rq_B* T_P. I checked the formula by taking its B-transpose, using naturality of lambda and the A-triangle identity; this calculation is written in the step. No site-comparison isomorphism is used. The coefficient-compatibility node's normalization defines the proper map before its bounded-constructible isomorphism assertion. Our inputs are in fact the shifted locally free constructible line; the proof only needs the defining mate.

Step 4 uses `lem-asd-etale-finite-twist-pullback` for the roots-induced map u_R and `lem-asd-ordinary-finite-p1-adjunction` for the two precise splitting components. Its equality involving u_R is checked as a map of sheaves on a root tensor generator before shifting. The canonical tensor comparisons are those supplied by the already-opened generic ringed-topos lemma. Applying Step 3 to u_A and c_A yields both required component equations, with the same source and target identifications as in the question.

Steps 5 and 6 are elementary consequences of the preceding formulas: Step 5 checks the two inclusions and invokes the coproduct universal property. For Step 6 I read the statement of `def-amb-p1-trace`, which defines exactly pr_2 composed with the inverse splitting. Composing the splitting equation with t_B and cancelling T_S(s_A) proves the trace equation in the specified direction. This does not assume beforehand that beta preserves a trace normalization.

I checked all hypotheses: ell differs from the positive characteristic, so N is invertible on S and P; finite type over a field makes the standing S Noetherian as required by the supplied splitting theorem. Both coefficient rings are killed by the chosen N, and the map is unital, so their Lambda structures compose. The small sites are taken in the project's fixed universe. The generic ringed-topos and scalar lemmas are unbounded statements, so no bounded-below hypothesis is lost by a nonflat extension. The argument also applies for A=Z/ell^2 -> B=F_ell (genuinely nonflat), the identity coefficient map, and an empty base. For N=1, both rings are zero rings and all the displayed arrows are the unique arrows in the zero module categories; the same formulas remain valid. No nontrivial-ring hypothesis was introduced.

Against delivery-errors B--E: there are no new statements to risk elementary-node inflation, duplicate nodes, or restating a clause as a child node. I read every cited node's statement, not just its proof, and cut the citation quotations verbatim. There is no uncited vanishing, projection formula, cohomology base-change, or preservation-of-constructibility theorem in the proof. The common Kummer class is part of the supplied construction, not a newly postulated compatibility. Every step is under 2000 characters. A read-only traversal of the current DAG found no path from any proposed proof dependency back to the item. All search entries added by this worker are the actual command's records; the hits were unrelated algebraic Kummer extensions, cotangent cohomology, ordinary pullback naturality and basis formulas. No Mathlib leaf was claimed.

## Unfinished work

None at stage 1. No new unsplit node is introduced. Validation and delivery results are recorded below after the required server checks.

## Server validation

The required `deliver.py Q69 lem-sp-p1-splitting-scalar --no-push` completed with exit 0 and `OK (not pushed)` at commit `6e35c15d154`; server preflight passed, including the DAG and split review checks. The final push is performed by the same delivery tool with server preflight enabled.
