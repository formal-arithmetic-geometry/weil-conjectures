# Q07 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-ring-sheaf-tor-amplitude-stalk-test.json`: item, statement unchanged, now split into five proof steps. Existing searches retained and actual Q07 searches appended; definition dependencies completed.
- No new nodes: the proposed geometric-point lemma was removed after the dry run found a newly landed node stating it.
- `citations.json`: one verbatim statement quotation for every node used by every proof step.
- `searches.jsonl`: the actual msearch log, including the additional searches that helped find existing tools.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint id, Tor-amplitude/stalk terminology, and geometric-point/algebraic-space terminology found no project declaration stating the item. The existing scheme constant-coefficient Tor-amplitude and flat-model files do not give this arbitrary ring-sheaf algebraic-space theorem. No compiler or Lake tool was run.

## Literature wanted

None.

## Corrections and route

The mathematical statement was retained, including arbitrary ring sheaves, arbitrary unbounded derived objects, all stalk-ring modules, and the chart clause. The imported node had no proof. In particular, the forward direction cannot merely test sheaf tensors and take their stalks: that would only immediately test modules known to occur as those stalks. The proof instead expands the source's pullback argument via the existing bounded-flat-model criterion, after which tensoring the bounded flat stalk complex tests an arbitrary stalk-ring module.

The reverse direction spells out the unbounded tensor comparison using two K-flat resolutions. Its derived isomorphism is proved by the representative argument in the item; it is not displaced into a new node. The existing `lem-sfb-space-geometric-points-conservative` supplies the actual geometric morphism required by the normalized ringed-point lemmas. It states the point construction and its inverse image as the exact pointed-neighbourhood colimit used here, without a Tor or quasi-coherence hypothesis.

I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/_section.md` context and the unit's current `_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3). The item remains an auxiliary prerequisite in the existing alteration/relative-perfectness branch. The DAG's unit record has historical material differing from the current blueprint, and `blueprint_refs.py ancestor` returns `None` for this created chain. I preserved the inherited null ancestor and via list, rather than inventing a blueprint ancestor or altering a unit. No key-node realization is part of this item.

## Unfinished work

No part of the requested stage-1 split is postponed. All supporting nodes already exist.

## Not duplicates

The required dry run discovered `lem-sfb-space-geometric-points-conservative`, newly present on the live repository. I opened its full statement: for any algebraic space over S it gives the point as an adjunction, identifies its inverse image with the pointed-etale-neighbourhood colimit, detects injectivity/surjectivity on geometric stalks and compares inverse images under space morphisms. Its point-realization clause subsumes the proposed 04K0 lemma. I deleted the proposed node, replaced its use in step 1 with this existing node, and regenerated the verbatim citations. Thus this delivery has zero new nodes and zero new Mathlib leaves.

Earlier searches of all DAG nodes for 04K0, `lemma-stalk-gives-point`, and geometric stalk/point terminology, and whole-blueprint searches with `blueprint_refs.py` for 04K0, 04K2, 04K5, point and stalk terminology, had not found that new live node. The existing `lem-sfb-space-etale-conservative-geometric-points` supplies the empty-space and conservative-set-stalk assertions and is also reused. Constant-ring scheme stalk formulas and structure-sheaf space tensor formulas were not used for arbitrary ring sheaves.

## Mathlib searches

For the item I ran two LeanFinder phrasings, LeanSearch, Loogle `"stalk", "tensor"`, and grep for Tor-amplitude/stalk tensor terminology. For the subsequently removed candidate node I ran two LeanFinder phrasings of the actual point-construction theorem, LeanSearch, Loogle `"AlgebraicSpace", "Point"`, and grep `AlgebraicSpace|geometric.*point.*topos|space.*stalk.*point`. All returned successfully, and the candidate searches remain in the actual log.

I read the returned results. They concern scheme etale categories, Zariski stalk maps, ring-theoretic tensor formulas, or general derived-category cohomological bounds. In particular, `Scheme.smallEtaleTopology` only defines the scheme site; `TopCat.Presheaf.stalk` is a topological-space stalk; and `Scheme.stalkMap_congr_point` is a ringed-scheme stalk-map congruence. None is 04K0 or the item's Tor criterion. The additional enough-points searches led to `ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectIsomorphisms`; I read `Mathlib/CategoryTheory/Sites/Point/Conservative.lean`, including the hypotheses and the definition of `HasEnoughPoints`. Those results assume the conservative family and do not construct the geometric points of an algebraic space. I also read `Mathlib/AlgebraicGeometry/Sites/Etale.lean` around the small-site definitions. No claimed Mathlib leaf is hidden here.

## Review by Q07

I read the item source in `sites-cohomology.tex`, Tag 0DJJ (`lemma-tor-amplitude-stalk`), including both proof paragraphs, and its forward input 08H5 (`lemma-tor-amplitude-pullback`) and the bounded-flat representative equivalence 08G1 (`lemma-tor-amplitude`). I read the point-realization source 04K0 (`lemma-stalk-gives-point`) in `spaces-properties.tex`, including its proof identifying the two neighbourhood colimits. I also read 04K1, 04K2 and 04K5 there: the point is the geometric stalk on the scheme-neighbourhood small site, and 04K5 applies to all sheaves of sets, without quasi-coherence or finiteness assumptions. The source's final exact-sequence sentence says points of S; its preceding precise assertion and proof use geometric points of X, as does the item. No statement correction was needed in this delivery.

For step 1 I opened and read the statement of the existing conservative-point node: it does give stalkwise detection of isomorphisms for sheaves of sets, so it applies to the underlying map from an arbitrary R-module sheaf to zero. A bijective module map has a linear inverse by applying the map to the addition and scalar equations. The normalized ringed-point definition explicitly transports ring/module operations, and the point-exact theorem explicitly applies to that presentation. These are actual stalk rings and actual module stalks, not an assumed equality with the structure-sheaf stalk or a constant coefficient ring. The newly found existing point-construction node supplies the geometric morphism as an adjunction, so no adjoint is inferred merely from preservation of limits and colimits.

For step 2 I opened the entire statements of the arbitrary-ringed-site flat-model criterion, point-flat theorem, exact-functor cohomology theorem, ordinary-module bounded-flat K-flat theorem and ordinary-module K-flat tensor-model theorem. The first has no constructibility or enough-points hypothesis and gives the same interval [a,b]; the point-flat theorem uses exactly the normalized point of step 1. The cohomology theorem ensures the stalk complex represents the stalk derived object. The bounded complex is bounded above, so the module K-flat theorem applies. The final tensor-model theorem permits any second complex, so N[0] needs no flatness. This avoids the arbitrary-N gap and proves the forward implication term by term. The degree calculation and resulting vanishing are elementary once those theorems have been applied.

For step 3 I read the statements of the K-flat resolution theorem, the ringed-site derived tensor descent theorem, the K-flat stalk criterion, point-flat theorem, total-tensor point comparison, ordinary-module tensor-model theorem, and exact-functor cohomology theorem. The resolution theorem gives flat terms as well as K-flatness for both P and Q. The descent theorem computes on two such resolutions. The stalk criterion's forward clause has neither boundedness nor a term-flatness assumption; term flatness is supplied separately only where the chosen representative setup requires it. The point-tensor theorem explicitly concerns unbounded signed total complexes, so there is no unsupported interchange of an infinite totalization. Exactness gives both stalk quasi-isomorphisms and the final cohomology comparison. Every use is part of a cited statement, not an argument borrowed from that node's proof. The derived comparison itself is assembled here, rather than asserted only degree by degree.

For step 4 the hypothesis is applied to the actual module M_x at every geometric point, then the already established zero detection from step 1 is applied to the cohomology sheaf. This is an elementary implication from steps 1 and 3, with no extra theorem hidden by the word “detection”. For step 5 I read the small-site and etale-restriction clauses of `def-trf-algebraic-space`. On a scheme chart the localized objects, maps and covers are exactly the scheme's small etale site; applying the proof already given with that represented space and the restricted arbitrary ring proves the chart equivalence. It does not silently assert that every stalk module extends to a global module sheaf. The empty-space clause is explicitly in the existing conservative-point statement.

I checked B--E of `coord/delivery-errors.md` against these files. There are no new-node shape, notation, self-containment, Mathlib-leaf or duplication obligations after the dry-run repair. The item has a genuine proof, not renamed clauses, and keeps its statement and imported metadata. The quoted citations were taken verbatim from each actual statement. The generic off-unit tools are declared in `split_report.tool_uses`, with their uses and why they do not replace the unit route. No SGA source is used.

I tested the empty algebraic space and empty chart (the module category is trivial), the zero ring and zero complex (all module tensors vanish), and a one-point field example (the criterion reduces to the usual ring-complex Tor criterion). For a nonflat module in degree zero, the forward argument does not falsely put its Tor amplitude in [0,0]: that hypothesis would be required before choosing such a flat representative. For unbounded complexes no boundedness is used in the converse; boundedness in the forward proof is a conclusion of 08G1 under the Tor hypothesis. The proof never assumes quasi-coherence, Noetherianness, quasi-compactness, a finite cover or flatness of the arbitrary test module. All five proof steps are below 2000 characters; none contains an unextracted comparison or induction called standard. There are no new nodes, and no dependency points to the relative-perfectness parent.
