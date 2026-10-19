# Stage-1 delivery: lem-per-marked-finite-diagram-approximation

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-marked-finite-diagram-approximation.json`: statement, split into eleven proof steps; no Mathlib match for the marked approximation assertion.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-gabber-graded-model-approximation.json`: new statement-only unsplit lemma, ILO III Definition 4.2 and Theorem 5.1; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-associated-graded-local-dimension.json`: new statement-only unsplit lemma, local algebra input of ILO III Corollary 5.4(i); no Mathlib match.
- `citations.json`: 27 verbatim statement excerpts, one for every step/node citation.
- `report.md`: this report. The earlier sandbox's proof, sources, old-statement.txt and searches.jsonl were retained. Only the construction justification in Step 2 and its citations were supplemented on resumption.

## Attachments

None. Searching the read-only slopmaster2 project by the exact blueprint tag, marked-diagram terminology, graded approximation and associated-graded dimension found no project declaration proving this item or either new lemma. General finite-presentation descent exists there, but does not assert marked approximation or normal-crossings preservation. The master checkout is reference material, not evidence of completion.

## WANTED

None. The ILO volume and Stacks sources used here are already available. The dimension input is recorded from ILO's explicit use of Matsumura 15.9, not represented as a proof of that theorem.

## Statement error — STATEMENT-DISPUTED

The imported item assumed that Z times X was supported on D but concluded that the approximated D was supported on Z times the approximation. The two containments are reversed. For an explicit counterexample take A=k a field, X=affine one-space over k, Z empty and D the origin. Then A is an excellent henselian local domain equal to its completion, and the original support hypothesis holds, but every model is X itself and the entire X is its closed fibre. The nonempty marked origin cannot become supported on the empty set on any neighborhood of that entire fibre.

ILO III Theorem 6.1(iii) and Proposition 6.2, final paragraph, instead use equality: the inverse image of Z is the support of the reduced normal-crossings boundary. I retained the earlier sandbox's explicit equality in both hypothesis and conclusion, faithfully correcting the imported statement to that intent. I also retained its clarification that the dominant union has the reduced closed subscheme structure. No target or chapter statement is changed. The parent should be checked at independent review for use of the intended equality rather than the erroneous one-sided formulation.

There is a typographical error in the source's last paragraph of III 6.2: the first occurrence of the expected codimension is printed card(J) for D_K; its next occurrence correctly says card(K). The split consistently uses the cardinality of the subset indexing the intersection.

## Unfinished work

No unfinished work in this one-level split. The two new lemmas remain unsplit deliberately and carry no proof or proof dependencies. Their future proofs are separate DAG items.

## Not duplicates

lem-per-gabber-graded-model-approximation vs lem-per-marked-finite-diagram-approximation: the former only compares thickened graded algebras of a single arbitrary finite-type scheme and a fixed model; it says nothing about regularity, boundary intersections, support equality, neighborhoods or dominant components. Steps 4–11 derive those conclusions, so this is a strictly smaller algebraic input rather than a clause relabelled.

lem-per-gabber-graded-model-approximation vs lem-per-uniformization-complete-local-descent: the latter reduces uniformization from completion and invokes this item's marked diagram conclusion; it does not state the graded comparison used to prove it.

lem-per-gabber-graded-model-approximation vs def-nagata-finite-presentation-descent: the latter constructs an object at a finite stage of an inverse limit; it supplies no comparison with close A-valued sections and no thickened graded algebra isomorphism.

lem-per-associated-graded-local-dimension vs lem-trf-smooth-local-tangent-cone-extension: the latter treats a smooth local map of essentially finite-type Q-algebras and describes a polynomial tangent cone extension; the new lemma treats arbitrary Noetherian local rings and arbitrary proper ideals with isomorphic associated graded rings, and concludes only equality of dimensions.

lem-per-associated-graded-local-dimension vs def-pur-normal-bundle: the latter defines a normal cone and describes the conormal bundle of a regular immersion; it gives no dimension-reconstruction theorem for arbitrary ideals in Noetherian local rings.

The whole-DAG searches by approximation, graded rings, normal cone, the proposed ids and the ILO places found no equivalent result. Whole-blueprint searches `graded` and `approximation`, together with the ancestor query, confirmed that neither new lemma is already an imported blueprint node. Both inherit the exact ancestor lem-per-artin-gabber-affine-curve and the full created-item chain. The sources are precise ILO results rather than invented Stacks tags.

## Review by N3

I read the standing brief, stages/1-dag.md, the three blueprint levels in SETUP, GOAL, coord/dag-sync, the worker role, the chapter and unit records, and delivery-errors B–E in full. This is the generic approximation input below the ancestor's finiteness/duality branch, not a replacement of the Fourier/perverse unit route. I read ILO III section 2 (printed pp.35–36), Definition 4.2 (p.39), Theorem 5.1 and its proof (pp.41–42), Corollary 5.4 and its proof (pp.42–43), and Proposition 6.2's last paragraphs (pp.44–45) in the available volume's extracted text. For the new graded-model lemma, Theorem 5.1 supplies every quantifier, including all later stages and all sufficiently close sections, and uniqueness over the fixed thickening. N=n+1 and a=N-c are written explicitly. For the new local-dimension lemma, Corollary 5.4(i)'s proof uses the dimension at the zero section of the normal cone; its local formulation allows any ideal in the maximal ideal, not just a primary ideal.

I opened and read the statement of every node cited by each step. Step 1 takes Noetherianity of completion from lem-weil-pbc-adic-completion-noetherian, Noetherianity of finite-type schemes from lem-weil-pbc-finite-type-over-noetherian, finite algebra presentations from lem-weil-pbc-finite-type-noetherian-finite-presentation, and finiteness/regularity of the marking list from the boundary definition. The completion and each finite-type A-subalgebra are Noetherian. Finite affine covers and quasi-compact overlaps then make these morphisms finitely presented; this explicitly supplies the hypotheses needed in Step 2.

Step 2 uses the actual Nagata constructed model and its property theorem, not a definition as an existence theorem. On resumption I added the two missing explicit inputs: lemma-nagata-relative-gluing-datum-descends identifies the raw charts and overlaps after base change, and lemma-nagata-relative-gluing-axioms-eventually supplies inverse and cocycle identities for gluing. The final property lemma supplies finite presentation and the comparison isomorphism. The morphism-descent and eventual-equality statements apply because the spectra are qcqs with affine transitions and all models are finitely presented. The closed-immersion-stage lemma is applied to finitely presented arrows between such models; these are finitely presented over the Noetherian stage base. Intersections are defined as fibre products, so their identifications do not assume exactness of a nonflat base change.

Step 3 uses exactly the constructible-containment conclusion of lem-weil-pbc-limit-contained-in-constructible (Stacks 05F4, whose statement I read in limits.tex). Its inverse system is qcqs with affine transitions. The equality locus of two closed supports is constructible in the Noetherian stage. Containment of the entire limit image in that locus therefore gives eventual equality, and arbitrary base change preserves equality of the pulled-back supports. No commutation of scheme-theoretic union with nonflat pullback is asserted.

Step 4 uses the new graded-model statement for each ambient scheme and each intersection, with finitely many thresholds and a at least 2. The quotient by the base degree-minus-one element is computed explicitly, rather than assuming that a truncated thickening already determines dimension. Step 5 uses the new local-dimension statement after taking stalks, where the ideals are proper because the point is on the closed fibre. Step 6 uses the boundary definition's regular intersection and dimension clauses and the exact regular-local cotangent criterion. The calculation I squared contained in the maximal ideal squared explains cotangent invariance and does not identify a base fibre ring with a local ring incorrectly.

Step 7 takes excellence of affine finite-type algebras from lem-exc-finite-type-localization-excellent and openness of the regular locus from the J-2 clause of def-exc-excellent-ring. It removes finitely many closed bad loci, all disjoint from the entire closed fibre. Step 8 takes regularity of the closed immersions and locally constant codimension from lem-per-regular-lci-geometric-calculus, and applies its displayed dimension formula only with the identity smooth factor and identical residue fields. Thus the locally constant integer is the local dimension difference needed here. This avoids an unjustified openness assertion about codimension.

Step 9 uses the regular-quotient kernel-parameters statement (Stacks 00NR, read in algebra.tex), the parameter regular-sequence and quotient-dimension statement (00NQ), the cotangent criterion and the exact Nakayama local-generators statement. All rings and quotients are regular local, and the relevant ideals are proper at the point. The full intersection's codimension makes the marking classes independent; extending their cotangent basis proves the simultaneous parameter assertion within the step. Step 10 uses prime parameter elements and the domain assertion from the cited UFD lemma, explicitly proves the product/intersection equality and radicality, and invokes the parameter criterion (Stacks 0BI9/0BIA, read in etale.tex) for the boundary. rem-pc-regular-normal is used for precisely its finite disjoint integral-component conclusion, including the possibility that one original marking splits into several components. No claim that approximation preserves global irreducibility is made. Step 11 uses that same disjoint-component conclusion to select dominant global components and explains why the restricted reduced scheme structure agrees. It uses no properness or surjectivity assumption.

I checked fields (m=0), empty schemes, empty closed fibres, empty boundaries and empty intersections. With a field the graded comparison reduces to the unchanged model. For dimension reconstruction, I=0 recovers R in degree zero; a maximal ideal gives the usual tangent cone; a nonprimary ideal such as (x) in k[[x,y]] is allowed and its associated graded retains dimension two. The hypotheses do not demand a flat scheme over A. A vertical regular component is handled separately by the final open-and-closed selection; it is never declared dominant. All eleven steps have fewer than 2000 characters (the longest is Step 2), and none hides a separate comparison lemma behind “transport” or “standard.” The two new nodes are statement-only, their TeX is written once, and all proof uses appear in proof_deps.

I read and retained the logged Mathlib search results rather than repeating unchanged questions. Searches cover LeanSearch, LeanFinder, Loogle and source grep, with distinct semantic phrasings for both new inputs. Dimension results for ring equivalences do not compare associated graded rings to their original rings; regular-sequence dimension formulae require extra hypotheses absent here. Henselian lifting of formally smooth algebras, ordinary affine-transition-limit morphism factorization, and Artinian-scheme definitions do not state the Gabber graded comparison or the marked conclusion. No service failure is treated as a negative search. The exact queries and dates remain in the nodes and searches.jsonl.

The generic tools from other units are declared in split_report.tool_uses with their purposes, rather than written into the maintainer-owned tool_uses field. No SGA source is used. I verified every citations.json quote against the current cited statement, including the two added gluing inputs. The support correction is explicit above; all other inherited proof, citations, source provenance and searches have been preserved.
