# Q70: lem-sfb-space-affine-coherator-formula

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-affine-coherator-formula.json`: statement, split; four proof steps, no new nodes, no new Mathlib leaves. The statement and its statement dependencies are unchanged.
- `citations.json`: a verbatim statement quotation for every step/node citation.
- `searches.jsonl` and `search-0.txt` through `search-4.txt`: actual logged search queries and their returned hits, in addition to the imported item's retained search records.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id and for coherator/Coherator. `AlgebraicGeometry.exists_dqCoheratorAdjunction` and related detection lemmas in `DQCoheratorAdjunction.lean` concern Zariski scheme module categories and do not state the small-etale affine formula. They are not attachments to this item.

## WANTED

None.

## Corrections and route

The imported item had no proof. Its statement agrees with Stacks 08H0, after the affine equivalence and the identification of the right adjoint in 0CR4. No statement dispute or hypothesis change is necessary. In particular, the claim concerns every unbounded input complex; knowing only that derived global sections is the inverse on quasi-coherent complexes would not suffice. Step 2 supplies the ambient adjunction before step 3 uses that equivalence.

Read spaces-perfect.tex, lemma-affine-coherator (08H0), lemma-better-coherator (0CR4), and lemma-boundedness-better-coherator (0CSS), affine proof paragraph. Also read the ordinary mapping-property proof in schemes.tex, lemma-compare-constructions (01I7), the module tensor adjunction in sites-modules.tex, lemma-adjoint-pullback-pushforward-modules (03D7), and derived.tex, lemma-derived-adjoint-functors (09T5). The explicit section calculation is the ordinary adjunction underlying the cited affine coherator construction, rather than a new route replacing a unit step.

The item's inherited chapter is sec-six-functors-basics and its inherited unit is sk-thm-sf-ctf-stability. Read both records and the latest blueprint unit. Its distant effectivity/Quot prerequisite is recorded in the inherited blueprint.from.place. `tools/blueprint_refs.py ancestor lem-sfb-space-affine-coherator-formula` returns None; I retained the inherited null ancestor and the complete via chain, rather than inventing a blueprint id. Whole-blueprint searches for `affine coherator`, `derived adjunction`, and `coherator`, and whole-DAG searches for 08H0, 0CR4, ordinary affine adjunctions and exact derived adjunctions, found the cited existing tools and no equivalent blueprint node. No unit realization field is changed: this is not its key statement node.

## Mathlib searches

Ran two LeanFinder phrasings, Loogle `SheafOfModules.IsQuasicoherent`, a grep for coherator/etale derived sections, and LeanSearch for the affine formula, all through the required Q70 msearch.py command. All five services returned successfully. Read their hits: ordinary quasi-coherent sheaf data, global sections of schemes or sheaves, ordinary right-adjoint instances, Zariski tilde, and general derived localization functors. None states this formula or specializes to it in one line. Kept every imported search and appended only the five actual new queries and outputs. No new node needed searches.

## Not duplicates

No new nodes. Reused the existing affine-etale module realization, small ringed model, K-injective resolution theorem, exact-left/K-injective derived adjunction theorem, coherator adjunction, and uniqueness of right adjoints.

## Review by Q70

I checked the proof against the Stacks sources just listed and opened the statement of every cited DAG node. For step 1, lem-sfb-affine-etale-derived-module-realization explicitly gives the associated module's affine-chart value B tensor_A M and its global sections M. The small ringed model explicitly retains restriction as an equivalence of module categories. These are exactly what is needed to construct, and uniquely extend, the displayed chart maps. Balancedness uses A-linearity of h and the structural A-action on F; compatibility sends b tensor m to b restricted times h(m) restricted along either route. Evaluation at T and multiplication by b prove that the maps are mutually inverse. This short tensor calculation remains in the item's proof, rather than becoming an unnecessary node.

For step 2, the realization node states exactness in the ambient module-sheaf category, not merely exactness inside QCoh. The resolution theorem applies to a small site with a commutative structure sheaf, precisely the model fixed in the statement. Restriction equivalence preserves acyclic complexes and their homotopy Hom groups, so resolution existence transfers. The cited lem-sp-canonical-right-derived-adjunction-shift states the unbounded adjunction for an exact additive left adjoint and the K-injective right derived functor; its stronger shift conclusion is not needed. Sections is additive and its output carries the actual A-action. Thus all of that theorem's hypotheses hold, and its right derived functor is the one stipulated in the item. This citation supplies an ambient derived adjunction, not a bounded-below calculation or a spectral sequence.

For step 3, the realization node states an unbounded equivalence with inverse derived global sections, so it supplies a quasi-inverse b and the counit abP isomorphic to P. Applying the fully faithful a gives the first Hom bijection; step 2 gives the middle one; the counit gives the last. Naturality in both variables follows from those specified maps. This proves that H=a RΓ is right adjoint to the inclusion without imposing quasi-coherence on E. For step 4, the coherator node gives exactly the same inclusion as left adjoint to DQ, and det-sp-unique-right-adjoint gives a natural isomorphism compatible with counits. Applying the inclusion gives the claimed derived-object isomorphism, not just separate cohomology isomorphisms.

I tested the statement on E=0, E=a(M)[n], and A=0 (empty affine scheme); it gives respectively zero, the identity through the equivalence, and the zero category. Unbounded complexes cause no convergence issue because step 2 uses K-injectives. Arbitrary non-quasi-coherent E is covered by the ordinary and derived adjunctions. No step uses a node's internal proof, an uncited flatness/acyclicity theorem, or a finiteness assumption. All steps are below 2000 characters. No new statement duplicates a clause of the item. Citations are verbatim and proof_deps is exactly the union of uses. Generic off-unit resolution, derived-adjunction and uniqueness tools are declared in split_report.tool_uses; they do not replace any geometric unit route.

## Unfinished work

None in this one-level split. The existing prerequisites remain separate DAG items where not already finished.
