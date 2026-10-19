# Stage-1 repair report: lem-sfb-eta-ring-hom

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-eta-ring-hom.json`: the retained three-step split, with the maintainer-requested `split_report.tool_uses` declaration and current chapter/unit metadata in the sandbox copy. The delivery tool preserves the base's maintainer-owned fields.
- `citations.json`: all eight step/node quotations refreshed from current node statements.
- `report.md`: this replacement report, superseding the retained report's obsolete missing-metadata observations and repeated earlier second readings. The actual search evidence remains in `searches.jsonl` and the item's `mathlib_searches`.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. A fresh read-only search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for `lem-sfb-eta-ring-hom`, `condensedPushforwardHom`, and `isMonHom_condensedPushforwardHom` found no declaration. Upstream master `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Basic.lean:417–428` defines the precise composite and its ring-homomorphism instance, but its comparison monoidality instance at lines 350–352 is still `sorry`. Master is reference material, not finished evidence.

## WANTED

None. This split uses the current blueprint's monoidal-adjunction route and existing categorical nodes. No geometric Stacks lemma or SGA source is required.

## Return repaired

The current return is the landing refusal for reviewed head `f7c2d2406a0b`: `fix dag/units/sk-def-sfb-coefficient-morphisms.json: not a file of the delivery (a fix only adds a NEW statement node; it never touches another node)`.

I opened the retained immutable review and proposed fixes in `/home/ubuntu/weil-launcher-nt/reviews/Q30__lem-sfb-eta-ring-hom__f7c2d2406a0b/`. Its `review.md` records a mathematically acceptable split and requests two metadata corrections. I applied both, rather than merely rebasing or repeating the returned files:

1. Added the requested `split_report.tool_uses` entry for `det-def-sfb-ring-object-transport`. Its clauses 3 and 1 are the generic black-box categorical facts used in steps 1 and 2. The coefficient-morphisms unit supplies the concrete adjunction and alpha map; its route does not replace this tool. No maintainer-owned top-level `tool_uses` field is set.
2. The returned landing instruction says a fix may add only a new statement node and must not touch another node. I therefore removed the unit copy from this retry. The shared unit's empty `realized` fields remain a maintainer-side bookkeeping issue; this item delivery does not modify that other node.

The proposed reviewer JSON has extra literal TeX escaping in unrelated fields. I copied only its requested `tool_uses` value into the item; the separately requested unit realization cannot be included because the landing return rejects edits to another node.

I compared the sandbox with the returned head's retained `snapshot/`: the pre-repair sandbox item was identical to that returned item. I then compared every directly cited node (all statement and proof dependencies) against the current shared DAG. None of their fields or statements changed since that reviewed head. I nevertheless reopened every proof-cited statement and its current blueprint source, and refreshed all eight citation quotations. The earlier `def-sfb-eta` repair remains valid: its current statement explicitly refers to `def-sfb-finite-upper-lower-star-adjunction`, the pulled-back coefficient objects, and abelian sheaves on the small pro-étale sites. The delivery script constructs the repair commit on its freshly fetched current base; no manual git command was run.

## Statement and source comparison

I read the current `dag/chapters/sec-proetale-coefficients.json`, `dag/units/sk-def-sfb-coefficient-morphisms.json`, their `main-20261015` source sections, and the item's statement and `.proof.md`. The chapter and unit records now exist and the item is bound to them. The previous report's missing-record assertion is obsolete. I read the unit record but did not include it in this retry because the landing return forbids changing another node in a fix.

The original item's objects were implicit, and its imported proof cited only alpha while also using monoidality, transport, and composition. The retained split introduces those same objects explicitly and replaces the nonexistent umbrella node citation `sk-def-sfb-finite-pushforward-pullback` with its existing detailed structure nodes. It retains arbitrary condensed rings, arbitrary scheme morphisms, abelian sheaves, and the exact induced pushforward ring structure. No finiteness, commutativity, nonzero, or nonemptiness hypothesis is introduced. There is no statement dispute or mathematical statement correction in this repair.

The proof follows the unit's mate construction. The broader unit node already uses this eta lemma, so it is not cited to prove eta. The realization record is bookkeeping, not a dependency edge or substitute proof.

## Mathlib and duplicate search

No new node is created. The original actual searches, including their second phrasings, remain unchanged with their evidence in `searches.jsonl`; no unrun search is added. The retained invalid Loogle query is labeled invalid and does not establish absence. Generic hits include `CategoryTheory.Adjunction.mapMon`, `CategoryTheory.Functor.map.instIsMonHom`, and `CategoryTheory.Functor.mapMonNatTrans`.

For this repair I read the pinned Mathlib source `Mathlib/CategoryTheory/Monoidal/Mon.lean:204–240`, `825–925`, and `1060–1078`: composition preserves the two monoid-morphism equations, lax monoidal functors transport monoids and their morphisms, monoidal transformations lift, and `Adjunction.mapMon` requires the supplied monoidal adjunction. These results do not supply the scheme-specific adjunction and alpha premises; the existing DAG nodes supply those. The item therefore remains split, not a Mathlib leaf.

Fresh whole-blueprint searches for `monoidal adjunction` and `eta_f` locate the existing adjunction, transport and eta nodes, and the encompassing coefficient-morphisms unit. None states an alternative complete equivalent of this item that avoids its argument. The item's nearest blueprint ancestor is itself. It is imported, so `blueprint.from` correctly remains null and `same_as` is empty. The exact proof locations are in the steps and `split_report.blueprint`.

## Not duplicates

No new nodes or same-tag pairs. The existing categorical transport theorem is reused. Ring-morphism composition is an elementary proof step, not a helper node.

## Review by Q30

I performed this repair review with the current node statements and sources open, rather than treating the previous approval as sufficient. I read the item's current blueprint statement and proof, the coefficient-morphisms chapter/unit route, each cited node's source text, and the upper-star unit and adjunction statements that specify the inherited hypotheses. There are no new-node sources to audit.

Step 1 uses `sk-def-sfb-pulled-back-coefficients`, which explicitly states that R = Lambda_Y is a ring object; `lem-sfb-finite-monoidal-adjunction`, which explicitly states that this adjunction's unit and counit are monoidal natural transformations; and transport clause 3, which explicitly states that their components at ring objects are ring morphisms. I checked the transformation is id to GF, with F = f^* and G = f_*. The composite lax tensor map is G(muF) after muG and its unit map is G(epsilonF) after epsilonG, so successive transport gives exactly the same ring structure on GFR. The inherited coefficient category is Ab and f is an arbitrary scheme morphism: the historical `finite` prefix is not a hypothesis. This step is non-elementary and all the facts it uses have cited statements.

Step 2 uses `lem-sfb-alpha-ring-hom`, whose actual statement gives alpha: FR to Lambda_X as a ring morphism for this same strong monoidal structure; `def-sfb-finite-lower-star-lax-monoidal`, whose statement supplies the structure on G; and transport clause 1, whose statement explicitly preserves ring morphisms. Thus G(alpha) has source GFR with the structure from step 1 and target G Lambda_X with the structure required by the item. No inverse to alpha or commutativity hypothesis is used. This step is also non-elementary and properly cited.

Step 3 uses the current `def-sfb-eta` statement for eta = G(alpha) after the adjunction unit, and clause 2 of `det-def-sfb-ring-object-monoid` for the two morphism conditions. The written calculation gives (vu)e_R = v e_T = e_S and (vu)m_R = v m_T(u tensor u) = m_S(v tensor v)(u tensor u) = m_S((vu) tensor (vu)). All maps have the displayed source R, intermediate object T = GFR, and target S = G Lambda_X. This uses associativity of composition and tensor bifunctoriality; it is elementary once steps 1–2 are established. The eight refreshed quotations copy the actual statements verbatim and include every use in every step.

I also opened `def-sfb-alpha-bundled` while checking the prior review's proposed unit realization, but that bookkeeping change is excluded from this retry by the landing instruction. The shared unit record remains untouched.

I checked delivery-errors B–E: there is no new unsplit node, incomplete new statement, new leaf claim, or elementary helper; all item notions have definition dependencies. Every non-elementary inference is a cited node statement, not a source tag or hidden construction in another proof. The transport tool is declared in `split_report`; the concrete monoidal-adjunction lemma realizes the blueprint's own functoriality reference. No step is moved into a restatement node and no induction or omitted argument is used. The broader unit is not a proof dependency, so its existing dependence on this item does not create a cycle.

For small cases I checked identity morphisms, the zero coefficient ring, discrete fields, and noncommutative discrete rings: only unit and multiplication preservation are used. For the fold map from two copies of a point to a point, eta is r mapped to (r,r), which preserves both operations componentwise. For an empty source the pushforward ring is terminal and the map preserves the zero-ring unit; a map into an empty target forces the source empty. No restriction excludes these cases. No false statement or failing inference was found.

The accepted item metadata change requested by the latest maintainer review is present in the actual delivery file. The separately requested unit realization is intentionally absent because the landing return rejects that file in a fix. The older changed-eta citation issue is also revalidated. This is the repairing worker's reading; a fresh second reader still performs the required independent review and delivery.

## Second reading by Q30

- Item statement: checked against `lem-sfb-eta-ring-hom.md`, the coefficient-morphisms unit statement, and all seven `stmt_deps`; verdict: the condensed ring, arbitrary scheme morphism, pulled-back coefficients, specified strong/lax structures, induced pushforward structure, and ring-object conclusion agree clause by clause, with identity, zero-ring, field, and empty-scheme cases retained.
- Step 1: checked against the current statements of `sk-def-sfb-pulled-back-coefficients`, `lem-sfb-finite-monoidal-adjunction`, and clause 3 of `det-def-sfb-ring-object-transport`; verdict: the unit component is a ring-object morphism for the stated monoidal adjunction, and the displayed composite structure is exactly the required transported structure.
- Step 2: checked against `lem-sfb-alpha-ring-hom`, `def-sfb-finite-lower-star-lax-monoidal`, and clause 1 of `det-def-sfb-ring-object-transport`; verdict: applying the lax pushforward to alpha gives a ring-object morphism with precisely the target structure in the item.
- Step 3: checked against `def-sfb-eta` and clause 2 of `det-def-sfb-ring-object-monoid`; verdict: eta is the composite from steps 1–2, and the written unit and multiplication equations prove the defining morphism conditions by associativity and bifunctoriality.
- New nodes: none; there are no new statements or Mathlib leaves to audit, and the existing transport node is the declared generic tool.
- Changes made in this reading: added this required second-reading record only; no mathematical statement, proof step, citation, or node metadata required correction.

## Unfinished work

None for this one-level split. The reused lemmas remain their own items; this report does not assert that they have closed Lean proofs. Only the sandbox is edited. No Lean is written, compiled or built. The required delivery checks validate the DAG-only commit on the current fetched base in its own temporary worktree.

## Earlier second reading (a previous round; superseded)

- Step 1 checked against the current statements of `sk-def-sfb-pulled-back-coefficients`, `lem-sfb-finite-monoidal-adjunction`, and clause 3 of `det-def-sfb-ring-object-transport`, plus the blueprint proof sentences 1–2; verdict: all hypotheses and the transported composite structure match, with no hidden source-tag dependency.
- Step 2 checked against the current statements of `lem-sfb-alpha-ring-hom`, `def-sfb-finite-lower-star-lax-monoidal`, and clause 1 of `det-def-sfb-ring-object-transport`, plus blueprint proof sentence 3; verdict: the source and target structures and the ring-morphism transport are stated exactly, with no invertibility or finiteness hypothesis added.
- Step 3 checked against `def-sfb-eta` and `det-def-sfb-ring-object-monoid`, and by expanding the two unit/multiplication equations; verdict: the composition calculation is elementary after steps 1–2 and proves precisely the item conclusion.
- New nodes checked: none; there are no new statements, Mathlib leaves, duplicate nodes, or missing searches to audit.
- Item statement checked against `lem-sfb-eta-ring-hom.md` and the current chapter/unit records hypothesis by hypothesis, including arbitrary condensed rings and scheme morphisms and the induced lax-pushforward ring structure; verdict: faithful and edge cases (identity, zero ring, fields, empty schemes) remain included.

I changed only this second-reading section in the sandbox report. The item JSON, citations, searches, and requested unit realization/tool-use metadata were independently rechecked and needed no further repair.
