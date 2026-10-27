# Stage-1 delivery: def-sfb-space-universal-relative-purity

## Files written

- `dag/nodes/sec-six-functors-basics/def-sfb-space-universal-relative-purity.json`: definition, split; no Mathlib match. Every constituent notion is already in the DAG or explicitly defined in the statement. No new nodes and no Mathlib leaves.
- `citations.json`: empty list, since a definition has no proof steps and hence no proof-step citations.
- `report.md`: this report. The search command also wrote `searches.jsonl`.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint tag and by universal purity, relative purity, impurities and associated points. The universal-purity declarations found concern polynomial weights, not this relative module predicate. None states this item.

## Wanted literature

None. All the sources needed here are present.

## Corrections and observations

Made the previously implicit type of X explicit: X is an algebraic space and Y is a scheme. No mathematical hypothesis, quantifier or conclusion changed. The original statement is already a direct definition, not a theorem requiring a proof. Quasi-separatedness, finite type of M, specialization and the chart relative-assassin union are defined in its text, so none needs an additional node. It would be a duplicate to create nodes restating these clauses.

The inherited `blueprint.from.node` is null. The required ancestor command also prints None; the parent chain has an existing recorded provenance limitation. I retain that field and the existing detailed place/via list. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/_section.md` and the current `sk-thm-sf-ctf-stability` unit and proof, in addition to the DAG chapter/unit records. The current proof's direct-image paragraph uses compactification. This is a foundational definition below the already landed proper-support flattening chain, not a replacement for that unit route. No unit record is edited.

## Not duplicates

No new nodes. DAG searches for 0CV8, 0CVD, 0CV0, impurities and universal relative purity found this item and users, including `lem-sfb-space-proper-support-universal-purity` and `lem-sfb-space-pure-dimension-flatness-representability`; those are theorems assuming or establishing the predicate, not competing definitions. The existing scheme definition `def-trf-relative-assassin` supplies exactly the chart-level relative assassin. Whole-blueprint `blueprint_refs.py search` searches for purity, impurity and relative assassin, and a text search of the latest blueprint for impurities/universally pure/relative purity, found no equivalent definition. Weight purity and smooth cohomological purity concern different objects. Thus `same_as` remains empty.

## Mathlib search results

Ran the five item queries recorded in `mathlib_searches` through the required command; their exact tool/query pairs appear in `searches.jsonl`. LeanSearch, Loogle, grep and both LeanFinder phrasings were available. Loogle and grep returned no hits. LeanSearch returned universal injectivity/openness and formal unramifiedness. LeanFinder returned specialization maps, universal closedness, module-support specialization and skyscraper sheaves, but no predicate about fibrewise associated points after arbitrary base change. Read the local universal-closedness definition in `Mathlib/AlgebraicGeometry/Morphisms/UniversallyClosed.lean` and the module-support specialization statement in `Mathlib/RingTheory/Spectrum/Prime/Module.lean`: they concern a whole scheme morphism or support over one ring, respectively. Neither defines this module-dependent universal relative purity. The pre-existing search records are retained, and their searches have now also been run for NI.

## Review by NI

I read `literature/stacks-project/spaces-flat.tex`, situation-pre-pure, definition-impurity (0CV8), and definition-pure (0CVD), especially clauses (2) and (4). The item preserves their intended domain, specialized to scheme Y and quasi-separated finite type f. It requires absence of impurities for every scheme B mapping to Y. This is the universal condition, not merely purity on the original base. For each such triple, the negation of b belonging to the image of the closure is exactly nonexistence of a theta in that closure mapping to b; the displayed final quantifier is the direct expansion of this definition. This set-membership expansion needs no external theorem or new lemma.

I also read `literature/stacks-project/spaces-divisors.tex`, lemma-locally-finite-type-locally-Noetherian-fibres, lemma-relative-assassin, and definition-relative-weak-assassin (0CV0). In lemma-relative-assassin take V=B and its identity etale map. Its conditions (3)/(4) test a point using an etale scheme U over X_B and its fibre over b. The union in the item is precisely this existential chart test. The source explicitly permits associated in place of weakly associated points when fibres are locally Noetherian; the preceding lemma supplies this for locally finite type morphisms. Thus the unrestricted, possibly non-Noetherian B in the universal quantifier is allowed: the finiteness concerns fibres over fields, not B itself. The definition does not assert a new chart-independence theorem or an all-base-changes theorem. Such theorems have not been slipped into the empty proof.

I opened and read the statement of every dependency. `def-pc-scheme` supplies schemes; `def-trf-algebraic-space` supplies algebraic spaces, representable etale charts and their small etale structure sheaves; `def-weil-size-convention` bounds all schemes and sites. `lem-trf-space-fibre-products-etale-covers` supplies precisely the algebraic-space sheaf fibre products X_B used here. `def-trf-space-quasi-coherent-module` supplies quasi-coherent module sheaves on the small etale site. `def-trf-space-etale-module-functors` specifies the tensor pullback used for M_B; direct image is mentioned only as the supplied convention and no theorem about it is invoked. `def-sfb-space-morphism-properties` supplies finite type, while quasi-separatedness is explicitly quasi-compact diagonal. `def-trf-relative-assassin` defines the scheme relative assassin as the union of fibrewise associated points, exactly the set used on U/B. `def-a1-space-point-topology` supplies point images and the atlas topology whose singleton closures occur in the impurity condition. No dependency is used for a theorem absent from its statement. There are no proof steps, so C1/C4 have no step citations to audit and `proof_deps=[]` is correct.

I tested the formula on small cases. M=0 and X empty have empty relative assassin, so purity holds vacuously. For an identity morphism X=Y, every base change is B with f_B the identity, so theta=b works whenever b specializes from b-prime. For the non-pure open immersion D(t) into Spec k[t] with its structure module, use B=Spec k[t], b-prime the generic point and b=(t): the generic fibre point is associated and its closure in D(t) contains no point above (t), giving an impurity. This also checks the direction of specialization. For b=b-prime the chosen point itself is theta, so a reflexive specialization never causes an impurity. No properness, flatness or Noetherian-base assumption has been introduced.

Against delivery-errors B--E: the item introduces its objects, every notion has a real defining dependency or an explicit inline definition, all sources are identified by their Stacks labels/tags, and its predicate is written out instead of defined by a tag. It creates no duplicate, elementary lemma or restatement node. It has no hidden proof steps, no long steps, and no off-unit proof citations. No SGA source, Lean writing, compiler or build is used. The sole editorial correction is the explicit type of X, described above.

## Unfinished work

None for this stage-1 definition. Its constituent nodes retain their independent stage states; no claim about proving those nodes is made.
