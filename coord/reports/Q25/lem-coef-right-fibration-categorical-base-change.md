# Worker report: lem-coef-right-fibration-categorical-base-change

## Files written

- `dag/nodes/sec-six-functors/lem-coef-right-fibration-categorical-base-change.json`: item, statement unchanged, split into five proof steps; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-right-fibration-inner-horn-pullback.json`: new statement-only lemma for the inverse image of one inner horn under a right fibration over a standard simplex; no Mathlib match, status unsplit.
- `citations.json`: a verbatim statement excerpt for every node cited by each proof step.
- `searches.jsonl` and `search-0.txt` through `search-9.txt`: the actual Mathlib queries and returned signatures. Only the node files and this report belong to the delivery.

## Attachments

None. The item has no Lean audit declaration to attach. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and `Comparator/` for the exact item and blueprint tag, and concept searches for right fibrations and categorical base change, found no matching project declaration. The new lemma's exact id and concept search also found no matching declaration. No upstream master sorry is treated as a proof. No Lean file was written and no compiler or build command was run.

## Sources wanted

WANTED: archived Kerodon Corollary 5.6.7.6 (029H), Proposition 5.3.6.1 and its proof in Subsection 5.3.6 (037W), for lem-coef-right-fibration-categorical-base-change.

WANTED: archived Kerodon Lemma 5.3.6.6 (02RK), for lem-coef-right-fibration-inner-horn-pullback.

These pages were read online; nothing was downloaded into the repository. The proof origin is agent because no local archival copy exists. These are Kerodon identifiers, not Stacks tags. Stacks does not state this quasicategorical result. No SGA source is used.

## Findings and changes

The item is true as imported and its conclusion is exactly the map needed by its citer `lem-coef-inner-anodyne-slice-categorical-equivalence`. Its hypotheses allow arbitrary simplicial A and B and a non-injective categorical equivalence u; I kept all of these. Kerodon 029H states the cocartesian version, while 02RK explicitly covers both cartesian and cocartesian fibrations. A right fibration is cartesian under the recorded horn definitions: each edge satisfies the final-horn test, and the dimension-one right horn supplies lifts with specified target. Thus the local new statement is the single-inner-horn specialization of 02RK.

There was no earlier split or report in this sandbox. I retained the imported searches and blueprint ancestry. The main obstacle is a dependency cycle, not a false statement: the existing marked/cartesian/cocartesian base-change statements already reach this item. For example the shortest path from the general cartesian invariance theorem is

`lem-coef-cartesian-base-equivalence-invariance -> lem-coef-kan-quillen-right-proper -> lem-coef-brown-fibrant-localization-pullbacks -> lem-coef-trivial-fibration-fraction-model -> lem-coef-terminal-local-kan-corepresentability -> lem-coef-pointwise-lan-mapping-property -> lem-coef-inner-anodyne-pointwise-lan-invariance -> lem-coef-inner-anodyne-slice-categorical-equivalence -> lem-coef-right-fibration-categorical-base-change`.

The cocartesian theorem reaches the same path through `lem-coef-marked-relative-cartesian-model`. The contravariant slice model and straightening presentation are circular for the same purpose. I did not cite them. Instead I isolated the local horn generator, wrote out closure under the countable horn attachments actually needed, used the existing functorial horn completion to get quasicategory bases, and then used the independent isofibration pullback-equivalence theorem. I checked by graph traversal that all old dependencies of this split have no path to the item.

The local generator is strictly smaller than the item: it fixes the base map to a single inner horn inclusion into a standard simplex. It has no assertion for arbitrary categorical equivalences or arbitrary bases. The five steps still supply the countable cell argument, extension of b, functorial replacement of u, isofibration check, and strict two-out-of-three comparison. This is not a new name for the whole item.

## Mathlib search findings

For both statements I ran LeanFinder twice with different semantic phrasings, Loogle, LeanSearch, and a source grep, using only msearch.py. All services answered. The exact records are in each node's mathlib_searches and in searches.jsonl; the full hits are preserved in the search text files. The nearest Loogle result, `SSet.innerFibration_pullbackObjObjπ`, is an internal-Hom corner statement, not preservation of weak equivalences by a degreewise relative pullback. I read PushoutProduct.lean:85-155 and InnerFibration.lean:29-100. The generic model-category hits in Instances.lean:110-155 provide pullback stability of fibrations and trivial fibrations; the equivalence u is not assumed a fibration, and the Mathlib simplicial structure here is Kan-Quillen, not Joyal. Horn constructors and the Quasicategory.hornFilling hits also give no local inverse-image equivalence. Thus neither statement is a Mathlib leaf.

## Not duplicates

lem-coef-right-fibration-inner-horn-pullback vs lem-coef-right-fibration-categorical-base-change: the new statement covers only one inner horn over a standard simplex; the item covers every categorical equivalence of arbitrary simplicial sets. The remaining proof is given in five steps, and the item is not used to prove the new node.

lem-coef-right-fibration-inner-horn-pullback vs lem-coef-cocartesian-categorical-base-change: that theorem concerns cocartesian fibrations and arbitrary categorical equivalences, while the new node is the local right-fibration generator. Its opposite specialization would suffice only after the general theorem were available independently; its dependency closure reaches this item, so it cannot be cited here.

lem-coef-right-fibration-inner-horn-pullback vs lem-coef-cartesian-base-equivalence-invariance: the existing theorem covers cartesian fibrations under a family of marked-model hypotheses and arbitrary categorical equivalences. The new node is a single-horn fact with no marked-model assumptions; the general theorem's closure reaches the item as displayed above.

lem-coef-right-fibration-inner-horn-pullback vs lem-coef-left-fibration-right-anodyne-base-change: that theorem pulls back right anodyne maps along left fibrations and concludes right anodyne. Opposites give left anodyne along right fibrations. Left anodyne does not imply categorical equivalence (already the initial endpoint inclusion in Delta^1 is a counterexample), so that statement does not supply the new conclusion.

lem-coef-right-fibration-inner-horn-pullback vs lem-coef-inner-anodyne-slice-categorical-equivalence: the latter is only for the particular slice projection C/c and an arbitrary inner-anodyne map. It is also the immediate parent of this item and cannot be used below it.

I searched the whole DAG by 02RK, 5.3.6.6, 029H, 02YL, inner-horn/pullback and right-fibration concepts. I also ran tools/blueprint_refs.py search for 'right fibration categorical equivalence pullback', 'inner horn', 'categorical equivalence', and '02RK'; all returned no imported blueprint match. No existing node has source tag 02RK. I read the nearby general statements rather than relying on their names. same_as remains empty. The new node's from.node and via are the item's nearest blueprint ancestor and full ancestry, as the ancestor command prescribes.

## Unfinished work

Only the new local generator remains unsplit, deliberately: the task is to split one level. Its statement, source and complete search record are provided. The item has a complete proof conditional on the cited nodes. No unit fields, live project files, launcher files, or Lean files were modified.

## Review by Q25

I read coord/brief-stage1.md, stages/1-dag.md, SETUP.md's three levels, the item's chapter and unit, GOAL.md, coord/dag-sync.md, and delivery-errors B through E in full. I read the main-20261015 blueprint ancestor's proof paragraph 2: this is supporting infinity-category infrastructure for the displayed finite-coefficient derived mapping-complex adjunction. The split stays below that unit route and changes no coefficient category or geometric exchange morphism. The item is not a target and there is no statement dispute.

I checked the item against Kerodon 029H and 02YL, and the finer proof route in 037W, especially Lemma 02RK and the final reduction to equivalences between quasicategories. I read the whole 02RK proof online. The new node is only its inner-horn/right-fibration case, whose right-fibration-to-cartesian specialization follows directly from the final-horn convention. It is self-contained, introduces n,i,Z,p, uses TeX, cites the three actual notion nodes, carries no proof or proof dependencies, and has all searches logged. I tested it with n=2,i=1 and p=id, with Z empty, with a constant Kan fiber, and with a nonconstant discrete presheaf on [2] (allowing empty fibers). These cases confirm that neither nonemptiness nor a quasicategory hypothesis on the horn inverse image is needed. The outer horn i=0 is deliberately excluded: with p=id its inclusion is not in general a categorical equivalence.

For Step 1 I opened the complete statement of lem-coef-small-inner-horn-completion: it gives precisely the displayed countable pushout construction, smallness, and cell inclusions, not just abstract existence of a completion. The new node gives exactly each pulled-back generator. The right-fibration definition gives its pullback lifting property; the Joyal model statement identifies monic equivalences as trivial cofibrations and supplies the two weak factorization systems. The step explicitly proves the colimit compatibility degree by degree and the countable lifting argument; it cites no generic properness or unlisted gluing lemma. In particular I checked that attaching characteristic maps need not be injective, since colimits are computed in fibers of sets over C.

For Step 2 the completion statement explicitly includes strict naturality of R(u), quasicategory outputs, and restriction lifting against every monomorphism in a containing universe. Taking the empty inclusion into a vertex therefore extends the exact map b. The Joyal statement supplies the inner horns and two-out-of-three, and the characterization theorem's clause (2) turns the completed categorical equivalence into a functor equivalence. The relevant universes are enlarged once to contain C and E, so no large base is treated as small in a smaller universe.

For Step 3 I read def-coef-infinity-fibrations and lem-cbc-left-fibration-equivalence-lift. The latter's prescribed-target clause, not merely its isofibration clause with prescribed source, is the one the opposite argument uses. I verified the orientation: e:q(x)->d reverses to an edge ending at q(x); lifting that edge with target x and reversing again gives the required source x. Inner horns fill in the total space by the two successive lifts explicitly given in the step. Opposites preserve the quasicategory condition by i->n-i and preserve the two inverse-triangle witnesses. The off-unit left-fibration node is declared as a generic tool in split_report.tool_uses; it replaces no unit step and no same-unit independent node supplies this clause.

For Step 4 I read lem-coef-infinity-isofibration-pullback-equivalence in full and its actual statement says that the projection r from a strict pullback of a functor equivalence along an isofibration is a functor equivalence, with no extra hypothesis on the equivalence. RA,RB and E-hat are quasicategories, and the latter projection is an isofibration by Step 3. The exact reassociation map (a,(v(a),e))->(a,e) is written, so the result concerns the required induced map. Clause (2) of the Joyal characterization theorem again gives the categorical-equivalence conclusion.

Step 5 uses only the earlier steps, the strict naturality equation, and the two-out-of-three clause of the Joyal model statement. I verified both composites on the pair (a,e), so the comparison is for the displayed map rather than an unspecified equivalent object. This step is elementary. All other steps are marked non-elementary and every theorem they use is cited. Every cited node's full statement was opened and the verbatim snippets in citations.json were checked against it. The excerpts for completion and Joyal are representative clauses; I also checked the other explicitly used clauses in their statements.

For E1-E6 I checked u=id, q=id, C a point, E empty, A and B empty, a non-injective equivalence between nerves, and a genuine non-quasicategory source A=Lambda^2_1 with B=Delta^2. In the empty cases the constructions preserve the empty object and the unique maps, without a hidden choice of a vertex. The proof never assumes that A,B or their original pullbacks are quasicategories. Only the completed bases and their right-fibration total spaces enter the isofibration theorem.

No proof step exceeds 2000 characters. I checked that the countable lifting argument and opposite-lifting argument are the routine operations stated in their cited inputs, while the substantive local inner-horn inverse-image fact is the new node, not hidden in a long step. There is no unrecorded mathematical correction, no hollow construction, no new definition, and no invented search. The required server dry run exited successfully with OK (not pushed), preflight passed, at 7efff01491. It reported no failures to repair. This direct delivery is then pushed through the same delivery tool.
