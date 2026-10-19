# Stage-1 report: lem-coef-space-universal-colimits

## Files written

- `dag/nodes/sec-six-functors/lem-coef-space-universal-colimits.json`: statement, split; six proof steps. The original statement is unchanged. Mathlib verdict: no match for coherent homotopy colimits of spaces.
- `dag/nodes/sec-six-functors/lem-coef-spaces-slice-cartesian-closure.json`: new statement-only node, unsplit; Mathlib verdict: no match. This is the existence of coherent internal Hom objects over a space, not a colimit-preservation assertion.
- `citations.json`: ten entries, one for every citation in the six steps, quoted verbatim from the cited statements.
- `report.md`: this report. `searches.jsonl` was produced by the required search command.

No unit, chapter, Lean, live project, or launcher file was changed. No compiler, Lake, build command, or local DAG-checking tool was run. All writes are in this item's sandbox.

## Attachments

None. I searched the read-only `WeilConjectures/` tree in slopmaster2 for the exact item id, its notion, universal colimits, homotopy pullbacks, locally cartesian closure, dependent products, and straightening. No declaration gives the whole item. I also searched the proposed child name and coherent slice-closure notion in the project source. Ordinary categorical results and upstream-master sorry declarations are not attachment evidence.

## WANTED

WANTED: archival copy of Kerodon https://kerodon.net/tag/05V5 (Corollary 7.7.3.23) and https://kerodon.net/tag/05UY (Proposition 7.7.3.17), together with Tags 05V1, 05V2, and 05V3, for this item and lem-coef-spaces-slice-cartesian-closure. These were read online; there is no archived copy under the provided literature tree. I cannot change literature/LIST.md or coord/HUMAN.md under this brief. The item's proof is therefore marked agent-written, with its online checks identified, rather than claiming an archived document proof.

WANTED: archival HTT, Corollary 4.2.4.8 and Proposition 1.2.13.8, the already cited small-colimit and overcategory inputs. Their complete interfaces are existing DAG nodes, not new uncited assumptions.

These are genuinely infinity-categorical facts. No Stacks tag states coherent slice cartesian closure or universality of homotopy colimits of spaces; the source identifiers above are Kerodon tags, explicitly distinguished from Stacks tags. No SGA source is used.

## Problems found and corrections

The imported item has an empty proof and a correct statement. I found no statement dispute and changed no hypothesis or conclusion. Its old searches concern presheaves as well as spaces; I retained them and added actual searches for this item's own statement. The source's very short instruction to combine two propositions is expanded into an argument; the proof does not merely cite another universality theorem.

The new blueprint snapshot files for the ancestor lie in `sec-six-functors/sk-thm-sf-package/`; the historical ancestry and inherited unit still say `sk-prop-sf-biduality-general`. I read both the historical master ancestor and the current proof, and preserved these maintainer-owned bindings. The item is a general foundational descendant of the mapping-complex adjunction in paragraph 2, not the unit's key statement, so no unit realization is edited.

The informal inference "a map over B, with a homotopy over A, is a map over A" could hide a compatibility problem. I expanded it in step 3: compose the specified A-homotopy with f to recover the B-homotopy, and use the supplied compatibility to contract the redundant choice. This works with all simplex parameters, so the calculation uses full mapping spaces.

## What remains

The item is split by one level. Its sole new child is deliberately unsplit and carries no proof, proof dependencies, or proof sketch in its statement. It will require the Kan-fibration relative-exponential argument of Kerodon 05UY. Nothing required for the item's one-level split was deferred. Delivery is reserved for the independent second reader; this worker runs only --no-push.

## Not duplicates

lem-coef-spaces-slice-cartesian-closure vs lem-coef-space-presheaf-cocompletion: the existing node gives the ordinary (unsliced) cartesian closure of the infinity category of spaces; the new node gives coherent exponentials in every slice over an arbitrary small space. The case B equal to a point is shared, but the unsliced statement does not supply the general fiberwise exponential.

lem-coef-spaces-slice-cartesian-closure vs lem-coef-infinity-relative-exponential-restriction: the existing node proves inner-fibration properties of a relative functor construction with a fixed quasicategory target and a monomorphism of cocartesian fibrations. It does not assert representability of maps into an arbitrary varying Y over B by a small space over B.

lem-coef-spaces-slice-cartesian-closure vs lem-cbc-enhanced-relative-exponential: the existing result concerns a fixed target quasicategory and cartesian-fibration source, with a cocartesian-fibration conclusion. It does not give the small Kan-valued internal Hom in a space slice with varying target Y over B.

lem-coef-spaces-slice-cartesian-closure vs lem-coef-space-universal-colimits: internal Hom representability contains no colimit claim. The item constructs a dependent product out of two such exponentials and a pullback, then calculates mapping spaces for its given cocone. Its content has not been transferred to a new base-change-colimit node.

I searched all DAG nodes for the new name, Tag 05UY, local cartesian closure, dependent products, relative exponentials and slice colimits. `tools/blueprint_refs.py search` was run for universal colimits, dependent product, cartesian closed, locally cartesian, slice colimit and exponential, and `ancestor` confirmed prop-coef-integral-exceptional-adjoint. No blueprint node states the new child. The general existing results above were read rather than inferred from their titles. No existing node has the new child's source tag.

## Mathlib searches and candidates

Every added record comes from a real invocation of `/home/ubuntu/weil-launcher-nt/msearch.py NC lem-coef-space-universal-colimits ...` and is preserved in `searches.jsonl`. For the child I ran LeanFinder on coherent slice internal Homs, Loogle on `"LocallyCartesianClosed"`, grep on `LocallyCartesianClosed|cartesian.closed|exponential` in AlgebraicTopology, and LeanSearch on local cartesian closure of small spaces. Before deciding absence I ran a second semantic phrasing about Kan fibrations and fiberwise function objects, and a second grep. All services were available for these queries. The item also has its own semantic, Loogle, grep and second-phrasing queries.

I read `Mathlib/CategoryTheory/LocallyCartesianClosed/ExponentiableMorphism.lean:41-53`: its class assumes an ordinary pullback right adjoint; it does not supply the required coherent one for spaces. `CategoryTheory.Cat.closed` and `CategoryTheory.Cat.cartesianClosed` at `CategoryTheory/Category/Cat/CartesianClosed.lean:71-80` concern ordinary categories. The grep hit at `AlgebraicTopology/Quasicategory/StrictBicategory.lean:28` is a future-work comment, not a theorem. Kan-fibration and model-category hits give definitions or ordinary homotopy classes, not slice exponentials. These are not one-line specializations to the child.

For the item I read `CategoryTheory/Limits/VanKampen.lean:43-49` (an ordinary universal-cocone predicate) and `CategoryTheory/Abelian/GrothendieckAxioms/Connected.lean:35-46` (ordinary connected indexing with exact colimits). Those do not prove the statement for an arbitrary small simplicial indexing set, especially the empty shape. No Mathlib leaves were manufactured from them.

## Review by NC

I read sections B through E of coord/delivery-errors.md in full, the stage-1 rules, the three blueprint levels in SETUP.md, GOAL.md, coord/dag-sync.md, the chapter and unit records, and both ancestor blueprint versions. For the item I read Kerodon 05V5, its two explicit inputs 05UY and 05V3, and the continuation 05V2 and 05V1. For the sole new child I read 05UY in full: its proof works with Kan fibrations over a Kan complex and constructs the relative simplicial exponential; it is not merely the theorem that ordinary simplicial sets form a presheaf category. I retain exactly its coherent, space-valued conclusion with the smallness visible.

Step 1 uses lem-coef-spaces-small-colimits-universe for all small simplicial shapes, including the empty shape, and lem-coef-infinity-relative-slice-sections for the sentence that the source functor from an overcategory creates existing colimits. I opened both statements: the latter explicitly says this for every x in C, without an essentially-small-D hypothesis on that sentence. Here C is S, x is B or A, and J is U-small, so their hypotheses hold. This supplies colimit existence without confusing colimits in a slice with those in its total category.

Step 2 uses lem-cbc-enhanced-functor-cone-calculus for the actual formula for mapping spaces in a cone category, specialized to a point-shaped diagram B. The same node's definition of the cone identifies that category with the coherent slice. I use lem-coef-infinity-yoneda-presheaf-limits for existence of small limits of spaces and its representable limit characterization. Pullbacks in the slice are then proved by the written calculation: mapping into the total-space pullback and imposing the specified base map give the same space in either order. I do not take a slice mapping theorem from a node that only defines a slice.

Step 3 uses the new child's full coherent exponential equivalence for a=(A,f) and y=(Y,fp), and uses the two mapping-space interfaces from step 2. All these are small objects over the same B. The identity section of [a,a] and the map [a,y] to [a,a] have the stated sources and targets, so their homotopy pullback exists by step 2. I checked that transposing the section produces pr_A, not a map with the wrong base or a chosen point of A. The homotopy fiber is over pr_A in Map over B, and its contraction of redundant B-compatibility gives exactly maps over A. The universality equivalences are natural in T, and that is all step 4 needs; no functor is chosen from an unproved mere existence statement.

Step 4 uses the explicit dual colimit criterion in lem-coef-infinity-yoneda-presheaf-limits. Its middle equivalence is applied to L as a colimit in S/B and to the test object P_Y, not to a colimit already pulled back. The last equivalence uses the just-proved natural representation at every F(j). Restriction along the cocone is tracked using that naturality, so the result proves that the actual pulled-back cocone is colimiting. Every small simplicial J is allowed; neither connectedness nor filteredness is introduced.

Step 5 uses the sentence in lem-cbc-enhanced-functor-cone-calculus saying that the full subcategory of initial objects is a contractible Kan complex. Thus its arrow is an equivalence between the two colimits, and its leg equations identify it with the required canonical map over A. Step 6 applies the same mapping-space criterion to the empty diagram and spells out the empty-space pullback. Both steps are elementary applications of the cited statements, not hidden geometric assertions.

I checked the child's edge cases B empty (the slice has just its empty object), B a point (the usual space of maps), X empty (the internal Hom is the terminal object id_B), and Y empty with some X-fibers empty (the representing fibers are terminal precisely where X has empty fiber, and empty where a nonempty fiber would need a map to the empty space). No surjectivity, nonemptiness or discreteness assumption is missing. For the item I checked J empty, f the identity, A empty, B empty, and maps of connected spaces having nontrivial loop-space fibers: all products in the proof remain homotopy pullbacks, so no ordinary set-theoretic fiber is substituted.

The child is self-contained, contains a statement only, gives the same space category and universes as the item, and has complete blueprint provenance. All new search records were actually run; none is an invented or unavailable search recorded as an absence. All ten citations have matching verbatim quotes in citations.json. I checked that the proposed existing dependencies have no path to this item, avoiding a circular justification. The generic cone-calculus citation is outside the inherited unit and is declared in split_report.tool_uses with its reason; the other existing theorem inputs share the inherited unit. No chapter route is replaced, no SGA source is cited, and no source or statement dispute was found.

## Second reading by NC

- Item statement: checked against Kerodon Tag 05V5, Corollary 7.7.3.23; universes, arbitrary small coherent shapes, slice colimits, pullback comparison, and the empty-colimit clause agree.
- Step 1: checked against Tags 05V5 and 05V3 and the cited small-colimit and slice-colimit node statements; it constructs both slice colimits with no extra nonemptiness or filteredness hypothesis.
- Step 2: checked against Tag 05V1 and the cone-calculus and Yoneda-limit statements; the mapping-space fiber and homotopy-pullback calculations use the stated slice objects and retain higher coherences.
- Step 3: checked against Tag 05UY together with Tag 05V1; the relative exponential is applied to $A\to B$ and $Y\to A\to B$, and the pullback represents maps over $A$, including empty fibers.
- Step 4: checked against Tag 05V2 and the cited colimit mapping-space criterion; the displayed equivalences are natural and identify restriction along the actual pulled-back cocone.
- Step 5: checked against Tag 05V5 and the initial-object clause of the cone-calculus node; the comparison is the canonical map over $A$ because its cocone legs are the pulled-back legs.
- Step 6: checked against the empty-shape clause of Tag 05V5 and the Yoneda-limit node; both slice colimits are initial, including when $A$ or $B$ is empty.
- New node `lem-coef-spaces-slice-cartesian-closure`: checked statement and hypotheses against Tag 05UY, Proposition 7.7.3.17; it states the coherent fiberwise exponential with small total space and allows empty spaces and fibers.

Changes made in this second reading:

- Re-ran every recorded Mathlib search whose result was absent from `searches.jsonl` and preserved the actual outputs; this repairs the search-log/preflight mismatch without changing any mathematical verdict.
- Added this second-reading audit. No node statement, proof step, citation, dependency, or source attribution required mathematical repair; no statement dispute was found.
