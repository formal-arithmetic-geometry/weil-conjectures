# Worker report: lem-trf-cotangent-resolution-coherence

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-cotangent-resolution-coherence.json`: repair the existing split, keeping the statement and the derived-colimit route; replace Steps 2–3 by the direct simplicial abelian-group lemmas below; status split.
- `dag/nodes/sec-trace-formula/lem-trf-simplicial-abelian-set-homotopy-quasi-iso.json`: new statement-only node, Stacks 08P2; not a Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-simplicial-abelian-surjective-quasi-iso-boundary-lifting.json`: new statement-only node, Stacks 08P1; not a Mathlib match.

`citations.json` contains a verbatim statement quotation for each step/node pair. There are two new nodes and zero new Mathlib leaves. No Lean was written and no compiler was run.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item's blueprint tag and id found nothing; concept searches for cotangent, standard resolution, simplicial abelian groups and trivial Kan fibrations found no project declaration asserting the item or either new input. The upstream master checkout is reference material, not a finished proof.

## WANTED

None: all sources for the retained argument and both new nodes are in `literature/stacks-project/`.

## Faults and repair

This is the dedicated repair in `coord/returns/Q13.md`, headed with 2486cbd099d046114307fe42015d3aa9c9f5e383 and returned again on 2026-10-18 at 06:52 CST. Its explicit fault is continued use of the dropped simplicial/model machinery. The shared base still has that rejected proof with status unsplit. There was no previous node or report in this Q13 sandbox, only dispatcher briefs.

The repaired proof has no use or proof dependency on `lem-cbc-simplicial-module-model`, `lem-cbc-realization-weak-equivalence`, or `lem-coef-kan-quillen-right-proper`. It also no longer needs the normalized-versus-alternating comparison. Standard-resolution contractibility comes from the already existing adjunction lemma. The elementary constant-complex calculation and direct Stacks 08P2 prove the standard augmentation is a resolution. Stacks 08P1 turns any polynomial resolution's additive quasi-isomorphism into exactly the boundary lifting that the remaining proof needs. These are classical simplicial abelian-group statements; no model structure, geometric realization, Kan–Quillen theorem or transferred module model structure occurs in their statements or our applications.

The item's statement is unchanged. The definition of polynomial resolution is precisely the termwise-surjective/quasi-isomorphism criterion of Stacks 08QI. Neither an additive contraction obtained from a set section nor algebra homotopy inverses between arbitrary resolutions are claimed. The remaining Steps 1 and 4–9 retain the current base's route and formulas. The two earlier NV auxiliary nodes already exist on the base and are reused without edits. Maintainer-owned `tool_uses` and historical review fields remain unchanged as required by the field contract; their obsolete entries do not occur in `proof_deps` or the step `uses`. The current worker's `split_report.tool_uses` declares only the retained boundary-defined Stacks 08NS tool. Maintenance may remove the old unused tool metadata when landing.

The historical ancestry through the lci-cotangent-presentation input is preserved. I read the trace-formula chapter and current `sk-i-curve-zero` unit; this auxiliary algebraic input does not assert that it realizes the current unit's zero-stalk theorem, and no unit record was changed. No SGA source is used.

## Not duplicates

lem-trf-simplicial-abelian-set-homotopy-quasi-iso vs lem-trf-cotangent-resolution-coherence: the item's metadata mentions 08P2 but its statement is about polynomial ring resolutions and cotangent comparisons; the new node is the generic underlying-set homotopy criterion for a morphism of simplicial abelian groups, with no rings, polynomial resolution or cotangent complex.

lem-trf-simplicial-abelian-surjective-quasi-iso-boundary-lifting vs lem-trf-cotangent-resolution-coherence: 08P1 occurs in the item's old source/proof metadata; the new statement is a generic boundary-lifting theorem for termwise surjective abelian-group morphisms and contains no cotangent-resolution comparison.

lem-trf-simplicial-abelian-set-homotopy-quasi-iso vs lem-cbc-simplicial-module-model: the latter is a transferred model-structure theorem with normalized-complex and Quillen consequences. It does not state the implication from a possibly nonadditive homotopy inverse to an additive homology isomorphism. That implication previously needed additional weak-equivalence and realization results; the new node states Stacks 08P2 directly.

lem-trf-simplicial-abelian-surjective-quasi-iso-boundary-lifting vs lem-cbc-simplicial-module-model: the existing model theorem describes fibrations and weak equivalences, and does not state the boundary lifting supplied by 08P1. Deriving the latter by that route would reintroduce the explicitly rejected Kan–Quillen machinery. The new node isolates the smaller direct classical theorem, rather than copying that model structure.

Whole-DAG tag searches for 08P1, 08P2 and their source labels found only the item. A parsed search of all node statements for simplicial abelian groups, quasi-isomorphisms and homotopy equivalences found no direct match. Blueprint searches for `simplicial abelian` and `homotopy equivalence` found no node stating either new result. The broad cotangent search returned only unrelated Lie-algebra and zero-stalk nodes; `polynomial resolution` returned none. `blueprint_refs.py ancestor` confirmed `lem-trf-local-term-locality`, with the item's existing via chain used for both new nodes.

lem-trf-simplicial-abelian-surjective-quasi-iso-boundary-lifting vs def-weil-pbc-trivial-kan-fibration: Definition 08NL defines the boundary lifting property but asserts nothing about quasi-isomorphisms of abelian groups. The new node proves that property from termwise surjectivity and an alternating-complex quasi-isomorphism, as in Stacks 08P1. Its source mentions 08NL only to fix the conclusion's convention.

## Review by Q13

I read cotangent.tex Definitions 08PM and 08PN, the generator-fibre proof of Lemma 08PS, both proofs of Lemma 08PT, Remark 08QI and the Functoriality section 08QL. I also read simplicial.tex Lemmas 08NC, 08ND, 08P1 and 08P2, including the proofs of the two latter results, and sites-cohomology.tex 08Q9, 08PG, 08PH and 08PD. In particular, 08P2 permits only set-theoretic simplicial homotopies; it does not require their additivity. This is why it repairs the first rejected step. The new 08P1 node keeps BOTH termwise surjectivity and the associated-complex quasi-isomorphism, and states the boundary condition including n=0, exactly as the source does. Both statements explicitly define their alternating complexes and their reindexing into nonpositive cochains.

For Step 1 I opened the existing adjunction node: its statement supplies the simplicial object, naturality, and underlying-set homotopy equivalence. The free/forgetful algebra adjunction and surjectivity of evaluation on each generator verify its hypotheses. Step 2 uses precisely the homology conclusion of the new 08P2 node; the calculation of the constant complex is written out and requires no lemma. Step 3 checks the two hypotheses of the new 08P1 node, factoring the augmentation through the constant complex so that there is no mismatch between a map to B[0] and a map to const(B). Its second citation is the boundary definition itself, not a model-category characterization.

In Step 4 the size-convention statement allows U in V; all U-small algebra structures and maps form a V-set, so the category used in the derived-colimit theorem is genuinely small in its working universe. The source uses a cardinal bound; the larger-universe implementation retains its purpose. For Step 5 I read the full statement of the boundary-defined trivial Kan homotopy lemma. A boundary of algebra maps prescribes independent compatible boundaries on the generators; Step 3 fills each, and the polynomial universal property extends them uniquely. This proves the needed boundary lifting before invoking that lemma. It uses no assertion about model fibrations. Empty variable sets give the unique map, and an infinite variable set uses choice of a filler per generator, without any finite-generation hypothesis.

For Step 6 I opened the derived-colimit node: its statement supplies canonical a_Q, their naturality for resolution morphisms, and the smallness/representable-contractibility hypotheses used here. Steps 4–5 check exactly those hypotheses. The universal derivation statement supplies the displayed differential-module functor, and the derived-category statement licenses the inverse of a quasi-isomorphism. The comparison c_Q is explicitly the quotient of the two canonical a maps; no comparison chain map between arbitrary resolutions is smuggled in.

For Steps 7–8 the only cited differential fact is its universal derivation, whose statement gives both the existence of the maps and the relations their formula must respect. I checked coefficient maps and generator images in the evaluation faces and unit degeneracies. Identity and composition follow from equality on coefficients and variables. Tensor extension T tensor_A A' remains polynomial by the mutually inverse coefficient-and-variable maps. No flatness of A to A' or B to B', and no claim that the tensor resolution remains a resolution, is used.

Step 9 takes the reindexing equation from the actual statement of the derived-colimit node, including its semilinear/restriction-of-scalars clause and the absence of a contractibility assumption on uQ. Substitution of a_std inverse times a_Q gives the written naturality equation; cancellation proves the identity and composition assertions. Thus the retained step does not rely on the proof of a cited node for an extra naturality claim.

I checked both new inputs on identity and zero simplicial groups, and the second on constant groups: a constant quasi-isomorphism is an isomorphism, so boundary lifting holds also in dimension zero. Surjectivity alone would fail for a map whose kernel has positive homology, which explains why it is not dropped. The first result does not claim the set homotopies become additive chain homotopies. For the item, the zero ring, an empty polynomial variable set, infinitely many variables, identity squares and nonflat ring squares are all covered by the stated argument. Neither new node repeats a clause of the cotangent item; each is a separate non-elementary simplicial theorem, left statement-only. No source error or statement dispute was found. All nine proof steps are shorter than 1100 characters, and there is no hidden long-step lemma. The return's dropped-machinery point is repaired rather than renamed.

Mathlib searches for both new nodes were run through the required msearch.py wrapper and their actual records retained in searches.jsonl. All four services returned successfully. I read every returned type and the relevant source: the quasi-isomorphism instances require chain homotopy equivalences; the simplicial homotopy type concerns maps in its chosen category; and the fibration hits require the model properties that need proving here. The Dold–Kan surjectivity hits concern simplex-category maps, not surjectivity of simplicial abelian-group maps. Neither node is a one-line specialization of those hits. The item's prior Mathlib records are retained, not presented as new Q13 searches.

## Unfinished work

None at this split level. The two new statement-only inputs join the ordinary stage-1 queue; the pre-existing standard-adjunction and derived-colimit nodes remain owned by their own items.
