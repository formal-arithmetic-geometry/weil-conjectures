# Q88 stage-1 report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-subgroup-identity-neighbourhood-open.json`: statement unchanged, five-step split, not a Mathlib leaf.
- `citations.json`: one literal statement excerpt for every step/node citation.
- `report.md`: this report. The search command maintains `searches.jsonl`.

No new nodes, no new Mathlib leaves, no Lean files.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag, flat subgroup, subgroup openness, and identity neighbourhood. No declaration states the item. The topological subgroup declarations are about continuous groups, not group schemes with their structure sheaves.

## WANTED

WANTED: Brian Conrad, *Reductive group schemes*, Theorem B.3.2(2), printed pp.288–290, as `literature/conrad-reductive-group-schemes.pdf`, for lem-sfb-flat-subgroup-identity-neighbourhood-open. The source PDF was read online at the existing node's URL; it is absent from the local literature. No literature or launcher file was changed. The actual general proof is explicitly agent-written from the local Stacks facts, rather than claimed to be Conrad's proof verbatim.

## Corrections and source scope

The item is true as stated; no STATEMENT-DISPUTED repair is needed. Its source attribution requires care: Conrad's final paragraph on printed p.289 first proves flatness near the identity, then global flatness by a fibrewise argument, and concludes that a flat closed immersion between Noetherian schemes is open. It does not explicitly state this arbitrary-base lemma. The existing source field already describes the lemma as an agent general tool formulation. I retained that provenance and wrote an independent, fully relative translation proof, with proof_origin.by = agent. In particular, neither topological openness alone nor flatness of H over S alone proves that the closed ideal vanishes.

The current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit statement and direct-images proof were read. The ancestor is the direct-image preservation argument (3), reached through the recorded supporting prerequisites. The blueprint ancestor command prints `None`; the inherited null from.node and complete via chain are therefore preserved, not replaced with an invented imported ancestor. Searches of the whole imported blueprint for `identity neighbourhood`, `subgroup`, `flat open`, `stalk isomorphism`, `finite presentation`, `01TT`, and `01U8` found no equal statement. The generic scheme tools used below support the translation argument without replacing any unit step.

## Mathlib searches

Read all results in `searches.jsonl`, including both semantic phrasings. The Q88 commands ran leanfinder twice, leansearch, loogle, and grep; all services answered successfully. Searches and actual result summaries are appended to the item's pre-existing Q44 search records. `AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono`, read in FlatMono.lean:38–39, needs Flat i, while the item only assumes Flat (H → S). It is not an attachment or a one-line Mathlib match. Topological subgroup openness does not establish the sheaf assertion. The other geometric hits state the definition or consequences of open immersions. Existing DAG Mathlib leaves provide the general facts used by the split.

## Not duplicates

No new node was created. DAG searches by keywords, Stacks tags and declaration names found existing nodes for all required results. In particular:

- The lfp base-change clause is already clause (3) of `lem-weil-pbc-qcqs-morphism-permanence`; a new lfp-base-change node would duplicate it.
- `lem-weil-pbc-open-immersion-etale` and `def-weil-etale-morphism` together give flatness and lfp for an open immersion; no new permanence lemma is needed.
- `lem-weil-pbc-flat-lfp-open` gives openness without a quasi-compactness assumption.
- `lem-weil-pbc-flat-local-hom-faithfully-flat` and `lem-weil-pbc-faithfully-flat-universally-injective` give the needed injection of local rings; no fpqc ideal-descent node is needed.
- `lem-weil-pbc-sets-sheaf-iso-on-stalks` applies to underlying set sheaves on the actual open subspace. It needs no etale geometric points.
- `lem-sfb-closed-subgroup-identity-stalk-detection` concerns a connected finite-type group over an algebraically closed field and cannot be used over this arbitrary S.

## Review by Q88

I checked the item against its hypotheses and Conrad Theorem B.3.2(2), printed p.289, and checked every invoked general fact in the local Stacks sources. No new node needs an additional source review. The argument is for arbitrary schemes: no affine, Noetherian, separated, finite-type, quasi-compact, smooth or connected hypotheses on G are supplied implicitly.

Step 1 uses the universal property of `def-pc-fibre-product` to form the two group-law automorphisms and D → P. Their displayed inverse formulas are inverse as morphisms, by the group axioms, not merely on geometric points. `lem-weil-pbc-open-immersion-base-change` says precisely that base-changing v gives an open immersion (Schemes Tag 01JY, lemma-base-change-immersion). `def-weil-open-immersion` identifies this with an open subscheme; carrying that subscheme by an automorphism requires no new theorem. The group actions and products here are all over S.

Step 2 uses `lem-weil-pbc-flat-morphism-base-change` (Morphisms Tag 01U9, lemma-base-change-flat), and ONLY clause (3) of `lem-weil-pbc-qcqs-morphism-permanence` (Morphisms Tag 01TS, lemma-base-change-finite-presentation). That clause allows arbitrary base change; the qcqs conditions of other clauses are not imposed. `lem-weil-pbc-open-immersion-etale` gives etaleness of k (Tag 02GP, lemma-open-immersion-etale); `def-weil-etale-morphism` explicitly includes flatness and lfp, so the definition is not being used for a permanence theorem. `lem-pc-flat-compose` and `lem-sbc-locally-finite-presentation-composition` then apply to k followed by pr_G, exactly as their statements say (Tags 01U7 and 01TR, lemma-composition-flat and lemma-composition-finite-presentation). Both factors have the requisite properties. This is the only use of flatness and lfp of H → S.

Step 3 uses the whole openness assertion of `lem-weil-pbc-flat-lfp-open`, checked in Morphisms Tag 01UA, lemma-fppf-open. The actual set image U is open; I do not infer that i is an open immersion at this point. The equations i r = q and q s = i are written explicitly, giving both set inclusions without any claim that scheme points themselves form a group. `def-weil-closed-immersion` supplies the homeomorphism onto the image. Neither commutativity nor smoothness is needed.

Step 4 applies `def-weil-flat-morphism` to the local ring map of q at z. It is a LOCAL flat homomorphism, so `lem-weil-pbc-flat-local-hom-faithfully-flat` applies (Algebra Tag 00HR, lemma-local-flat-ff). `lem-weil-pbc-faithfully-flat-universally-injective` applies with the base ring itself as N (Tag 05CK, lemma-faithfully-flat-universally-injective), with the tensor identification written out. The germ composition factors through i, forcing i's stalk map to be injective. Its surjectivity follows directly from the affine quotient clause of `def-weil-closed-immersion` (Morphisms Tag 01QO), by lifting a localized fraction. Injectivity of i on points ensures r(z) is the chosen h. The choice z = s(h) works even without any cover compactness. This repairs the gap a merely topological proof would leave.

Step 5 uses the ordinary sheaf criterion `lem-weil-pbc-sets-sheaf-iso-on-stalks`, checked in Sheaves Tag 007T, lemma-points-exactness (3), on the topological space U after identifying H with U. Thus its stalks are exactly those in Step 4. The sectionwise inverse of a bijective ring homomorphism preserves all ring operations, and inverting the restriction squares proves naturality. `def-weil-open-immersion` then gives exactly the full scheme assertion. There is no appeal to an etale-site conservativity theorem or to a result about abelian sheaves with unstated ring compatibility.

I checked B–E of delivery-errors.md in full. Every non-elementary fact is in a cited statement; every quote in citations.json is checked as a literal substring. There are no unsplit proof sketches, no new duplicates or repackaged item clauses, no SGA citations, and no proof step exceeds 2000 characters. The elementary group-law and tensor-unit calculations remain in the proof rather than being promoted to nodes.

For edge cases: if S is empty all schemes over it are empty, so the conclusion and all stalk checks are vacuous. For nonempty S, the specified identity section ensures the needed point z above each h. Taking H = G works for non-smooth groups such as mu_p in characteristic p. A disconnected constant finite group with an open subgroup is also covered. A proper nilpotent closed thickening of the identity with the same underlying support does not provide a factorization of an open neighbourhood through H; this confirms why schematic factorization i b = v, rather than set containment, is essential. No false fieldwise point argument is used.

## Unfinished work

None in the authorized stage-1 scope. No Lean was written or compiled. Dry run and delivery results are recorded after running the required server checks.

Dry-run correction: the first citation gate required longer excerpts for flat composition and local faithful flatness. Both citations now quote their complete statements, including the hypotheses. The proof is unchanged.
