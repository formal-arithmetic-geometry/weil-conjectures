## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-supported-source-system-cup-calculus.json`: statement, split into four elementary assembly steps; Mathlib verdict: no exact match or one-line specialization.
- `citations.json`: verbatim statement excerpts for every step/node citation, including flat-source closure and pullback coherence.
- `report.md`: this report. No new nodes and no Mathlib leaves. The local `write_split.py` is only a sandbox editing helper; `searches.jsonl` is the search command's actual log.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact item id and for supported cup/source-system language; the exact tag is absent. Read the nearby constructions in `WeilConjectures/EtaleCohomology/Purity/Smooth/SupportedCup.lean:185–260` and declaration inventory in `WeilConjectures/SixFunctors/Etale/Derived/Supports.lean`. These are specialized scheme-support cup definitions, not a theorem for arbitrary ringed sites, arbitrary coherent flat source systems, all integer degrees and weights, and the prescribed exact-pullback comparison. The pro-etale finite/adic cup lemmas concern their own coefficient and support settings, not this statement.

## WANTED

None. The relevant Stacks source and current blueprint are available locally.

## Audit and changes

The live item was unsplit with no proof; there was no earlier sandbox item or report and no repair note. Copied it and kept its statement, statement dependencies, blueprint fields and earlier Mathlib searches. Added the proof, proof-dependency union, agent proof origin, split report, and actual searches from this attempt. No definition or target was changed.

Read `GOAL.md`, the worker brief, stage-1 rules, delivery-errors B–E whole (including the duplicated historical copy), the three-level rule in SETUP, the chapter and unit records, and the current blueprint frame-independence proof. This item is not the unit statement, so no unit realization was edited. The blueprint's even-degree permutation and endpoint pullback argument are served by the same source-system route; no SGA source is used.

Searched the whole DAG by `0FPL`, `0FPM`, source-system and shifted-tensor language, and ran blueprint searches for `cup product`, `shifted tensor` and `source system`, plus the ancestor command. The existing shifted-tensor morphism calculus states precisely the non-elementary identities required. Its additive-constraint node states naturality of the prescribed shift constraints and closure of flat degree-zero sources. Therefore no new lemma is necessary: coefficient/source substitution and inverse equations are elementary steps, rather than additional nodes restating this item's clauses.

The six fresh searches recorded in the item are exactly the queries in this sandbox's `searches.jsonl`: LeanFinder with two conceptually different phrasings, Loogle, LeanSearch and two grep queries. Read the hits. Ordinary monoidal sheaves (`Sites/Monoidal.lean:168–188`), ordinary graded tensor modules (`LinearAlgebra/TensorProduct/Graded/External.lean:70–125`), and complex-level shift comparisons (`Algebra/Homology/BifunctorShift.lean`, especially lines 95, 119, 156 and 199) do not specialize in one line to this ringed-site derived Hom product and its prescribed pullback comparison. The second semantic search also returns abstract CommShiftTwo commutators and the derived localization shift, which do not give the asserted product. All fresh services answered successfully; the earlier unavailable search is preserved as unavailable.

## Not duplicates

No new nodes were created. The existing `lem-pur-shifted-tensor-morphism-calculus` is cited, not restated as a new node. Its operation has arbitrary tensor targets without coherent coefficient multiplication or source labels. The present item performs the explicit source/target substitutions. `lem-per-noetherian-supported-product-calculus` is about supported cohomology of Noetherian schemes with finite coefficients, rather than arbitrary ringed sites and source systems, and was not used as an unjustified generalization.

## Review by NU

I read Stacks `sites-cohomology.tex:8421–8491`, Tags 0FPL (`lemma-cup-product-associative`) and 0FPM (`lemma-cup-product-commutative`), and checked their tag/label mapping. They state relative-cup diagrams, not this shifted-Hom calculus; 0FPM omits its proof. Accordingly this proof is explicitly agent-written, using the already stated and reviewed shifted-Hom identities, rather than claiming Stacks directly proves the stronger statement. I also read the current `lem-pur-frame-independence.proof.md`, especially Permutations and Elementary shears. There are no new nodes needing separate source review.

For Step 1 I opened `lem-pur-derived-tensor-additive-constraints` and verified its statement gives natural derived t, flat degree-zero tensor sources, and the representative normalization used in the item. The naturality formula follows by expanding B and using the tensor bifunctor's composition law, so it hides no new comparison lemma. I opened `lem-pur-shifted-tensor-morphism-calculus` and checked its statement gives separate additivity of B. I opened `def-weil-abstract-derived-category` and checked its statement explicitly says the derived category is additive, so fixed pre/postcomposition preserves sums. These are precisely the three Step 1 citations. The source sheaves are flat by hypothesis, and their derived tensors are again flat degree-zero objects by the cited closure statement.

For Step 2 the cited shifted-calculus statement gives the ternary B equality, after the source and target associators. Expanding both star composites gives the two displayed M/H expressions. M_L=M_R and H_L=H_R are exactly the item's two associativity hypotheses, and taking inverses is legitimate because every mu is an isomorphism. The iterated source hypotheses are supplied by Step 1. No idempotence of the label operation and no unit label is used.

For Step 3 the same cited statement gives exactly sigma B = (-1)^(ab) B-swapped sigma. I checked the direction of the source relation: mu_(d,c) sigma = mu_(c,d) implies sigma mu_(c,d)^(-1) = mu_(d,c)^(-1). The target relation is h_(s,r) sigma = h_(r,s). Thus the two sides really are the defined products with the sign displayed, after precisely the allowed label/weight identifications. No sign from the weights is introduced because those coefficient sheaves are in degree zero.

For Step 4 I verified the cited shifted-calculus statement gives pullback of B on all derived morphisms, preservation of flat sources, and coherence with the prescribed tensor, shift, associator and symmetry comparisons. Exactness of module pullback is a hypothesis of the item, so termwise U is the stated derived functor. The two replacement equations are just the assumed b/tau equations, with inverses and compositions. Expanding U-sharp and substituting them gives the displayed expression; Step 1 naturality, with the four maps explicitly specified, converts it to the required primed product. This proves equality on derived morphisms and does not infer equality merely from pure-tensor cohomology representatives. Both ringed sites have the smallness and commutative-ring hypotheses required by the cited calculus, since the second is assumed to be another such site.

I tested a=b=0 (ordinary unsigned product), a=b=1 (minus on interchange), a=-1,b=1 (the same odd sign), arbitrary negative weights (no positivity enters), zero maps (bilinearity), characteristic two (the sign becomes the identity), repeated labels including c wedge c (no idempotence assumption needed), and the identity pullback b=tau=identity (the comparison formula specializes correctly). A zero source and the empty label set yield zero or vacuous assertions. All four steps are under 2000 characters; none hides an independent non-elementary claim. I checked delivery-errors B1–B10, C1–C8, D1–D5 and E1–E7 against these files: no new-node schema or duplicate problem arises, every non-elementary input is a cited statement, the only computations beyond it are the displayed substitutions, the source route and hypotheses agree, and the statement is unchanged. No source dispute was found.

## Unfinished work

None in the one-level stage-1 split. The existing dependency nodes retain their own proof obligations. No Lean was written or compiled, and no repository or launcher file was edited.
