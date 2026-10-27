# Worker report: det-def-sfb-coefficient-morphisms

## Files written

- `dag/nodes/sec-proetale-coefficients/det-def-sfb-coefficient-morphisms.json`: definition, split into one proof step using five existing nodes; not a Mathlib leaf.
- `citations.json`: five verbatim statement quotations for the one proof step.
- `searches.jsonl`: the required Mathlib searches, including the second semantic phrasing.
- `report.md`: this report.

Zero new nodes and zero new Mathlib leaves. No Lean, compiler, Lake, build, repository, or launcher files were written. No agents were started.

## Attachments

None. The prior attachment proposal was rejected because its five cited declarations were unknown identifiers in the assigned upstream checkout. I therefore did not answer ATTACH. The live read clone does contain corresponding declarations in `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Basic.lean`, but the assignment's earlier rejection and the stage-1 rule require a split here rather than treating that proposal as an attachment. The existing DAG child nodes already bind the relevant declarations and are the proof dependencies used by this delivery.

## WANTED

None. The current blueprint and all cited DAG statements are present locally.

## What was wrong or incomplete

The imported item had status `imported`, an empty Mathlib-search list, and a proof copied from the blueprint without a stage-1 split record. Its blueprint proof cites five child nodes, all of which exist in the live DAG: `def-sfb-alpha`, `lem-sfb-alpha-ring-hom`, `def-sfb-alpha-bundled`, `def-sfb-eta`, and `lem-sfb-eta-ring-hom`. I retained the statement and its imported metadata, updated the source to `literature/blueprint/latest`, and made the proof a single explicit step with exactly those five uses. The step does not move any clause into a new node or infer a node's proof from its implementation.

I searched the whole DAG and current blueprint for duplicate statements and for the five child identifiers. Each child is already present and is strictly smaller: the two definition nodes specify alpha and eta, the alpha-ring and eta-ring nodes state preservation of ring-object structure, and the bundled-alpha node states the ring-object isomorphism. No new node is justified.

The existing source declarations in `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Basic.lean` agree with the concepts, but they were not used as an attachment claim. The Mathlib searches found only unrelated generic pullback and scheme declarations; Loogle reported the requested project identifier as unknown, and grep found no Mathlib declaration for these project-specific names. These results are retained in `searches.jsonl` exactly as emitted by `msearch.py`.

## Not duplicates

No new nodes were created. The five existing child nodes are reused rather than duplicated; each has a narrower statement than the item (alpha definition, alpha ring morphism, bundled alpha isomorphism, eta definition, or eta ring morphism).

## Review by NS

I read the current item, the latest blueprint node and proof, the chapter record, the unit record, the existing child-node statements, and the relevant source module. The item hypotheses are a condensed ring, a scheme morphism, pulled-back coefficient rings, and the strong/lax monoidal and adjunction structures listed in its statement. The proof step uses `def-sfb-alpha`, whose statement identifies alpha as the component of the pullback-from-point comparison; `lem-sfb-alpha-ring-hom`, whose statement says this alpha preserves the ring-object operations under the transported strong-monoidal structure; `def-sfb-alpha-bundled`, whose statement gives the composite bundled ring-object isomorphism; `def-sfb-eta`, whose statement defines eta as the adjunction unit followed by pushforward of alpha; and `lem-sfb-eta-ring-hom`, whose statement gives eta as a morphism of the induced lax-monoidal pushforward ring object. Thus every clause of the item is supplied by a cited statement, with no reliance on a cited proof or unstated hypothesis.

I checked the edge cases implicit in the statements: the construction allows an arbitrary scheme morphism (including an identity or empty scheme), and no commutativity or finiteness hypothesis beyond the condensed-ring/ring-object setup is added. The source and target of each displayed map type correctly: alpha has source `f^* Lambda_Y` and target `Lambda_X`, while eta has source `Lambda_Y` and target `f_* Lambda_X`. The five entries in `citations.json` are verbatim copies of the cited live statements, and `proof_deps` is exactly the union of the step's uses. The one proof paragraph is under 2000 characters and follows the current blueprint proof verbatim in substance.

## What I could not finish

Nothing remains for this stage-1 split. The required server dry run is the final validation before delivery.
