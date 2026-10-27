# Stage-1 report: lem-trf-polynomial-square-bar-naturality

## Files written

- dag/nodes/sec-trace-formula/lem-trf-polynomial-square-bar-naturality.json: item, statement, split; unchanged statement and statement dependencies. Seven proof steps. Mathlib searches find ingredients, not the complete assertion.
- citations.json: one verbatim statement extract for every node used by every step.
- report.md: this report. Searches made by msearch.py are preserved in searches.jsonl.

No new nodes; no Mathlib leaves. No Lean written or compiled. The shared repository and launcher were read only; packaging and push use the authorized delivery command.

## Attachments

None. I searched all lean/WeilConjectures for the exact blueprint tag/id and polynomial/bar/standard-resolution notions. There is no project declaration giving the full assertion. Unrelated group bar resolutions and finite naive cotangent presentations do not state it. The general DAG comparison's Sheaf Lean record is not an attachment of this item.

## WANTED

None: all mathematical sources used are present locally.

## Corrections and dependencies

The item had no proof. Its statement is retained verbatim, including non-surjective polynomial presentations, arbitrary square maps, infinite variables, and no resolution assumption on uQ. The inherited blueprint ancestor is local-term-locality; its current main-20261015 text is the contracting-correspondence argument. I retain the recorded intermediate cotangent-resolution/lci-adjunction/semistable-modification ancestry and do not claim that ancestor separately states this algebraic tool. The unit and chapter route are unchanged.

I added proof dependencies on the existing polynomial-augmentation-boundary, Kähler-differentials definition, polynomial-presentation-homology and simplicial-derived-colimit-computation nodes. None is a new node. The last is the precise general theorem supplying cross-category semilinear naturality, which is stronger than merely naturality in F or maps within one fixed presentation category. The steps do not extract any construction from another node's proof.

## Unfinished

No gap in this one-level natural-language split. Its existing dependencies remain separate DAG tasks; this is not a claim that their Lean proofs are finished.

## Mathlib searches read

The exact current searches are those appended from searches.jsonl, with the actual tool/query and returned digest; earlier inherited searches are preserved. I tried two semantic phrasings. Both LeanFinder runs mainly returned Dold-Kan projection or normalization naturality. LeanSearch returned ProjectiveResolution.isoLeftDerivedObj_hom_naturality and its homotopy-category variant. I read Mathlib/CategoryTheory/Abelian/LeftDerived.lean:98-138, especially the declaration at line 123: it compares a single additive functor applied to projective resolutions in a fixed abelian category, not the two polynomial presentation categories and bar comparison here. Loogle returned KaehlerDifferential.map and map_D; I read Mathlib/RingTheory/Kaehler/Basic.lean:645-680, definitions at 658 and formula at 668. These give the differential-map ingredient, not the item. The initial grep found Ideal/CotangentBaseChange.lean:17; I read its opening and tensorCotangentHom construction: it concerns an ideal's conormal base change (and flatness for an equivalence), not simplicial resolutions. The broad follow-up grep was truncated to unrelated map declarations, so I refined it to CategoryTheory/Abelian and RingTheory/Kaehler using msearch again; those returned the exact lines just read. No unavailable service was recorded as an absence.

## Not duplicates

No new nodes were created, so no new/existing pairs require justification. Whole-DAG keyword and tag searches and blueprint_refs searches for bar comparison, polynomial resolution, 08QL and 08Q9 were made before deciding to reuse the general comparison. The latter is not a duplicate of this specialized item: it supplies its genuinely general categorical input. The related polynomial-resolution-universal-evaluation node concerns signed presentation-site comparisons and small full subcategories, and is not needed as an additional dependency.

## Review by Q148

I read Stacks cotangent.tex Tag 08QL (section-functoriality), including the final sentence omitting the comparison verification, and its resolution remark 08QI. I also read sites-cohomology.tex Tag 08PD (remark-morphism-fibred-categories) and the whole statement and proof of 08Q9 (lemma-compute-by-cosimplicial-resolution). The explicit ring-square and differential maps follow 08QL; the omitted compatibility is supplied by the already split general comparison, with every parameter checked below. There are no new nodes whose source needs a separate review. I read the statement of every cited node, not merely its title or proof, and checked the verbatim extracts in citations.json against those statements.

Step 1 constructs t_n by finite polynomial substitution. This is an elementary construction, including infinitely many variables because each polynomial uses finitely many. Step 2 uses polynomial-augmentation-boundary only for the standard simplicial structure, with exactly the evaluation faces and unit degeneracies its statement displays. It proves their compatibility on coefficients and variables; the equations for evaluation and double brackets prove every nested face and degeneracy. The induction for strict composition has explicit base beta and step L(gf)=L(g)L(f). No standard-resolution contractibility is silently used here.

Step 3 constructs the presentation functor by balanced tensors. The original commutative ring square proves balance of the augmentation. The displayed mutually inverse substitution maps prove polynomial base change directly, so no uncited base-change theorem or flatness assertion is used. All data remain in U, while the presentation categories are small in V. For E empty the inverse reduces to A tensor_A A' = A'; for infinite E the same generator check applies.

Step 4 cites the actual quotient-by-additivity/Leibniz/constants presentation in the Kähler-differentials node. I checked it contains these relations, so the proof checks maps on those relations rather than citing that definition for an unstated theorem. Tensor balance uses augmentation compatibility, and the two naturality paths are written on dx tensor b. Step 5 uses the same presentation for K(h), first constructing the balanced simplicial A'-algebra map k. Its augmentation uses exactly epsilon' h=beta epsilon; its face equation gives the alternating differential equation. Identity and composition are checked on differential generators using the already proved strict laws for t.

Step 6 cites polynomial-presentation-homology for smallness, representable contractibility (requiring only the given trivial Kan augmentations), and its canonical first-vertex bar comparisons. It then cites simplicial-derived-colimit-computation, whose statement explicitly allows u:D->D', rho:B->B', a semilinear coefficient transformation and a simplicial k:uQ->Q', and explicitly states the exact comparison identity used. These are precisely the u, theta and k of Steps 3-5, and F'(k)theta equals K(h) on every differential generator. I checked that the source and target coefficient rings B and B' lie in V and restriction is along beta. No inference uses the proof of either dependency. The first-vertex convention agrees on both nodes, so no concealed sign change occurs.

Step 7 cites polynomial-augmentation-boundary for the standard endpoints' trivial Kan property and polynomial terms, and the general comparison statement for its explicit absence of a contractibility requirement on uQ. Thus the standard case is a valid specialization even for nonflat base change. As a small nonflat test, take A=Z, B=Z/2, A'=Z/2, B'=Z/2: the tensor balance and generator formulas still make sense and no preservation of exactness is asserted. Zero target rings and identity squares likewise give the prescribed zero differential modules or identity maps; no generator, nonzero-ring, surjectivity of vertical maps or injectivity assumption was inserted.

Against delivery-errors B-E: no new statement-only-node formatting, source, missing-definition, or duplicate issue arises; the statement remains TeX without re-escaping. Every non-elementary input is one of the cited statements above. The proof has actual substitutions and relation checks, not clauses relabelled as new lemmas; the generic naturality theorem is an existing broader input, not a new restatement. The comparison identity is a derived-category equality, with all target scalars restricted. There is no node depending back on this item in the proof dependencies' closure (to be mechanically checked on the server). Every step is shorter than 2000 characters; none hides an additional independent theorem. I corrected the tempting but unjustified route through a_Q after treating uQ as a resolution: the final proof never does that. No mathematical statement correction or disputed source claim was needed.
