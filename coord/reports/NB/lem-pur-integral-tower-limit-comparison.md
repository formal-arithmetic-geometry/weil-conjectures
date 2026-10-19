# lem-pur-integral-tower-limit-comparison — NB

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-integral-tower-limit-comparison.json`: statement, split into six proof steps; no exact Mathlib match for the full normalized-system/completed-operation statement.
- `citations.json`: one verbatim statement quotation for each of the 14 step citations.
- `searches.jsonl`: actual Mathlib search outputs logged by the prescribed command; inherited searches in the item were retained, with this run's searches appended.
- `report.md`: this report and signed review.

New nodes: 0. Mathlib leaves: 0. No Lean or unit record was written, and no compiler or build command was run.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact id and the blueprint tag found no declaration. Concept searches found the finite étale monoidal comparison and normalized-tower interfaces, not the entire strict pro-étale comparison with coherent reduction, prescribed completed-operation substitution, and resolution independence. I read the module introductions of `SixFunctors/Etale/Derived/UpperStarMonoidal.lean` and `IntegralCoefficients.lean`: the first explicitly rests on sorried derived-tensor interfaces, and the latter uses small étale coefficients and only existence assertions for comparisons. Neither is an attachment for this item. The upstream master was not used as evidence of a finished proof.

## WANTED

None. The sources needed for this split are present locally.

## Corrections and scope

The imported item had a statement and searches but no proof. Its statement was retained exactly, including strict inverse maps, semilinear quotient transitions, normalization, unbounded flat-term K-flat representatives, coherent reduction, and naturality. There is no statement dispute. I added the explicit argument and the union of its actual citations as `proof_deps`, retaining the existing statement dependencies and historical blueprint ancestry.

The current main-20261015 file `sec-six-functors-basics/sk-def-purity-conv/def-weil-frobenius-coefficient-twists.md` is a definition with no proof file. The nearest historical ancestor reported by `tools/blueprint_refs.py ancestor` is `def-weil-frobenius-coefficient-twists` through `lem-pur-derived-pullback-tensor-iso`. This item serves that parent's integral comparison, formerly step 4, as the existing `blueprint.from.place` records. It does not invent a new step of the unit or alter its route. The item's chapter and unit records were read and retained. It is not the unit's key node, so no unit realization record is delivered.

The generic foundational tools `lem-weil-pbc-ringed-strict-tower-homotopy-limit`, `lem-coef-normalized-dvr-effectivity`, and `lem-coef-semilinear-derived-sections` belong to other units. Their `split_report.tool_uses` entries state why this unit needs their precise black-box interfaces. This delivery does not set maintainer-owned `tool_uses`.

## Not duplicates

No new nodes were created. I searched the whole DAG for the source tags 0941 and 07A4, and the imported blueprint with `blueprint_refs.py search` for `derived limit`, `tower comparison`, `normalized tower`, and `completed tensor`. The hits include general derived limits, normalizations, and operation nodes, which are used as appropriate; none is an imported blueprint statement of this entire strict comparison. In particular the substitution lemma supplies the object identifications and their naturality, but does not state the result about an arbitrary supplied strict isomorphism `c`; the six steps perform that argument rather than create a node restating it.

The required logged searches used LeanFinder twice with different descriptions, Loogle, LeanSearch, and Mathlib grep restricted to CategoryTheory. The semantic hits concern ordinary adic completion, ordinary limits, condensed counits, and generic derived-adjunction counits. The grep hits are the pointwise left/right derived-functor interfaces. I read the pointwise right-derived interface and the ordinary adic-completion tensor source: they have neither these coefficient systems nor the comparison being proved. These are useful general infrastructure, but do not give the item by a one-line specialization. The elementary uses of identity, composition, conjugation, and naturality were kept as proof steps instead of spawning category-theory leaves.

## Review by NB

For the item I read Stacks `sites-cohomology.tex`, Tag 0941, label `lemma-derived-limit-is-ok`, including its K-injective tower construction, and Tag 07A4, label `lemma-pullback-tensor-product`, including the use of K-flat complexes with flat terms. The first identifies the actual total right derived functor with the derived limit; the second explains the finite comparison for which this supporting lemma is intended. Neither is cited as if it stated the entire lemma. I also read Bhatt–Scholze, Definition 3.4.10 and Lemma 6.5.9(4), in the local pro-étale paper, for completed operations. Lemma 6.5.9 is stated for qcqs schemes; this proof does not apply that theorem to arbitrary schemes, but uses the already stated, explicit operation and substitution interfaces. Therefore `proof_origin.by` is `agent`, with the categorical transport identified honestly. There are no new-node sources to review.

I opened and read the statement of every node cited by the six steps, rather than using facts from its proof. Step 1 uses `def-pur-integral-derived-operations` for the exact finite pullback computation and `def-weil-derived-tensor` for a K-flat computation of total tensor. Both apply to the actual finite coefficient sheaves; no replacement by the discrete integral constant sheaf is made. `lem-pur-completed-operation-tower-substitution` explicitly says the finite system operations on normalized inputs are normalized, so it supplies normalization of both A and D. `lem-coef-semilinear-derived-sections` supplies the coherent interpretation of the strict semilinear complexes. The strict inverse and commuting transition squares are hypotheses of this item, not conclusions smuggled into a definition. The equation q(pi)=pi explains why these maps are R-linear after restriction.

Step 2 takes exactly the exact-functor assertion of `lem-weil-pbc-ringed-strict-tower-homotopy-limit`. It applies it to the restricted strict R_X-towers on the small pro-étale site and writes both inverse equations using its functor laws. It does not claim uniqueness of a map produced by an arbitrary triangulated cone. Step 3 takes exactly the substitution identifications stated by `lem-pur-completed-operation-tower-substitution` for normalized T,U,V. It fixes their orientation and gives the formulas mu=b^{-1}L(c)a and nu=a^{-1}L(c^{-1})b, so checking inverseness is two explicit cancellations.

Step 4 uses `lem-coef-normalized-dvr-effectivity` only after normalization has been established. Its statement provides coherent counit isomorphisms without boundedness or constructibility. The substitution statement provides precisely the specified reduction identifications. Naturality here is the defining naturality of this canonical counit, and the proof displays its equation and the resulting reduction equation. All maps are in the coherent system category, so this proves the claimed compatibility with quotient transitions, rather than merely a collection of evaluated object isomorphisms.

Step 5 uses the substitution statement's explicit naturality for morphisms of input systems and the derived-limit functor already cited in step 2. It names every input/output map, writes the given compatibility yc=c'x, and substitutes the two naturality equations into the conjugation formula. Step 6 uses the semilinear section statement's detection of equivalences by evaluations, the functorial substitution statement, and the actual derived-limit functor. For resolution changes it uses precisely clause (2) of `lem-pur-integral-operations-well-defined`: unique natural comparison isomorphisms compatible with the displayed complex construction after localization. This is the needed compatibility for identifying the maps in step 5 with canonical resolution comparisons; it is not an appeal to an unnamed change-of-model argument.

I checked the delivery-errors B–E issues against these files. Every citation has a verbatim statement excerpt in `citations.json`; no step cites a definition as if it supplied an extra theorem. No hidden tensor-flatness or product-exactness assertion is needed: the finite model computation is given by the cited operation/derived-tensor interfaces, and the limit functor is supplied outright. No finiteness, boundedness, geometric smoothness or properness is added. No source route through a forbidden purity trace theorem is used. No statement-only node contains a disguised proof, because no new node was required. There is no circular use of the parent pullback–tensor theorem. The two elementary steps consist of displayed functor laws or pasting equations from the cited interfaces; the remaining non-elementary steps explicitly cite their inputs. All proof steps are shorter than 2,000 characters.

As small-case checks, c=identity with A=D gives the identity limit map in its substitution coordinates; the zero systems and empty sites give the same inverse and counit equations; the identity map f does not change any formula; and the argument imposes no bounds on the complexes, so both-sided unbounded flat-term K-flat inputs use the same total tensor computation. For arbitrary nontrivial quotient transitions the equations remain strict before localization, and the counit equations retain those transitions. These checks exposed no false clause requiring a statement correction.

## Unfinished work

None in this one-level split. Existing unsplit dependencies remain their own items; this delivery does not claim to have proved them or to have completed the transitive Lean proof.
