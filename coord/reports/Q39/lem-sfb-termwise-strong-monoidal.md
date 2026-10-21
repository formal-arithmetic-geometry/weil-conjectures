## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-termwise-strong-monoidal.json`: statement, split; no exact Mathlib match after five logged Q39 searches. Wrote seven proof steps. No new nodes or Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each of the 19 step/node citations.

## Attachments

None. The earlier proposed attachment was refused by the server. This delivery does not repeat it or use a project declaration as an uncited black box.

## WANTED

None.

## Findings and changes

The imported item had no proof. Its mathematical statement is correct and is retained verbatim, including countable-coproduct preservation, unbounded complexes, the direction of the inverse tensorator, and the absence of a symmetry hypothesis. The older searches, source, blueprint provenance and candidate metadata are retained. There was no earlier split or report in the sandbox to recover.

I read Stacks Tag 0FPQ (`sites-cohomology.tex`, `lemma-symmetric-monoidal-cat-complexes`, lines 12935-12957), including its proof hints about the degree-zero unit and coherence. That lemma concerns module complexes on a ringed site, rather than the abstract functor extension here; I have not presented it as a theorem asserting the item. I read the full project file `lean/WeilConjectures/Algebra/Homology/Monoidal/MapHomologicalComplex.lean`, especially the summand formula (61), associativity calculation (154), both unitor calculations (190 and 208), and monoidal instance (227). I also read the comparison construction in `lean/WeilConjectures/Mathlib/Algebra/Homology/Monoidal.lean` (414-439). These were used to check a direct natural-language argument, with `proof_origin.by = agent`; no Lean was written or compiled.

Read the chapter record, the unit `sk-def-sfb-dc-restricted-functors`, the nearest blueprint ancestor's reduction-of-RHom proof, and the three-level route rule in SETUP.md. This is the ordinary-complex normalization needed by the exact coefficient-model comparison, not a new route for the finiteness theorem. No SGA source is used in the proof.

Mathlib searches: Q39 ran LeanFinder twice (termwise strong monoidal extension; tensor comparison respecting associators and unitors), Loogle for `"mapHomologicalComplex", "Monoidal"`, grep for `mapCochainComplexMonoidal|mapHomologicalComplex.*[Mm]onoidal`, and LeanSearch for the additive monoidal extension on cochain complexes. The actual hits are recorded verbatim from `searches.jsonl`. LeanFinder gives the monoidal structure of complexes and tensor summands, and the second query gives finite distributivity. LeanSearch gives additive termwise extension and unrelated discrete/additive constructions. Loogle and grep returned no hits. None asserts the strong monoidal extension with the prescribed comparisons. None of the services was unavailable.

Before deciding that no new lemma was necessary, I searched the whole DAG for the item, strong-monoidal/termwise/total-tensor concepts and Tag 0FPQ, the project Lean for the item tag and the candidate names, and the whole blueprint with `blueprint_refs.py search` for `termwise strong monoidal`, `total tensor` and `monoidal functor`. The existing `lem-sfb-total-tensor-homotopy` states the precise triple-sum and unit constraints needed here. The total-tensor definition states both the signed differential and the tensor of maps. Thus the construction and the two-line coefficient checks belong in this item's proof; no clause is moved into a new node. `blueprint.same_as` remains empty after those searches.

## Not duplicates

No new nodes. Existing signed total tensor, strong monoidal functor and total tensor constraint nodes are cited directly.

## Review by Q39

I checked the seven steps against the statements of every node they cite, not against their proof internals. There are no new-node sources to review.

1. `def-weil-pbc-category-colimit` gives existence and uniqueness of the map out of the preserved coproduct. `def-sfb-preserves-kflat-quasi-iso` gives the degree-n sum indexed by p+q=n, and `def-sfb-strong-monoidal-functor` supplies the invertible coefficient tensorators. The index is explicitly in bijection with the integers, so the hypothesis on F suffices. The inverse is written on each coprojection and both composites are checked there. This is the coproduct universal property, not an unnamed comparison theorem.
2. The signed-total-tensor definition supplies the two differential terms; the strong-monoidal definition supplies tensorator naturality. The step writes both resulting components, including the sign (-1)^p, and uses additivity of F to preserve it. Coproduct uniqueness then tests the chain equation. The inverse chain equation is obtained by multiplying by the already constructed inverse, with no quasi-isomorphism or exactness assumption.
3. The tensor-of-maps formula is explicitly in the total-tensor definition, and the naturality equation is explicitly in the strong-monoidal definition. The step displays the two coefficient maps and identifies them using the inverse of that equation. The colimit statement gives uniqueness. No existence of a termwise comparison is borrowed from a source declaration.
4. `def-sp-abelian` supplies a zero object and additive Hom groups; `def-sfb-strong-monoidal-functor` supplies the unit isomorphism with the required orientation. I checked the proof that F(0) is a zero object using its zero identity. Consequently all off-zero degree maps and all differentials involving them are unique zero maps; the displayed j is a chain isomorphism.
5. I opened `lem-sfb-total-tensor-homotopy`: its statement really does give the coefficient associator and reindexed triple sums, not merely a monoidal existence claim. Countable nested indices and tensor preservation of colimits justify testing on triple inclusions, by two successive coproduct universal properties. The two displayed coefficient composites are precisely the inverse-tensorator version of the strong-monoidal associativity equation. Cancelling invertible maps proves equality; factors are never exchanged. I marked this step non-elementary because it invokes the existing tensor-constraint theorem.
6. The same total-tensor constraint statement gives the coefficient unitors on the (0,n) and (n,0) summands. I checked both unit identities in the strong-monoidal definition with e_F inverse, not e_F, in j. The zero-factor argument uses additivity of tensor. The displayed left and right coefficient formulas follow by cancellation, and the coproduct test covers all other summands. This is an explicit calculation from those statements, not an unproved compatibility assertion.
7. The strong-monoidal definition gives exactly three coherence equations and tensorator naturality. Taking the inverse comparisons constructed above and cancelling isomorphisms recovers those equations. The existing total-tensor lemma supplies the source and target complex monoidal structures. There is no symmetry clause to prove or assume.

For C1 and C4, every non-elementary input is therefore the statement of a cited node. The five generic off-unit tools are declared in `split_report.tool_uses`; none replaces a step of the unit route. Definition nodes are used only for their explicit formulas and universal properties. For B and D, there is no new-node relabelling, special case duplicate, hidden proof in a statement-only node, or unsupported Mathlib-leaf claim. For E, the colimit indices are small and countable, all complexes remain unbounded, and no exactness, braiding, flatness or boundedness was introduced.

I tested zero complexes, the zero abelian category, unit complexes in degree zero, complexes concentrated in arbitrary positive and negative degrees, and the identity functor. A negative odd first degree still gives the negative second differential term in Step 2; even degrees give the positive term. For arbitrary two nonzero differentials both coefficient terms match separately. For a triple of single-degree complexes, Step 5 reduces exactly to the given coefficient associativity equation. For a nontrivial unit comparison, Step 6 requires e_F inverse exactly as stated. Empty support and characteristic two cause no exception. All proof steps are shorter than 2000 characters (the longest is 1110), and none hides a further standalone lemma.

No statement correction was needed. The fault corrected from the earlier attempt is delivery as a genuine split, with every construction and coherence calculation written, instead of another attachment answer.

## Unfinished work

None for this one-level stage-1 split. Server dry run and push are performed after this report is written.
