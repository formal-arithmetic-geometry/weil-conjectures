# Q60 stage-1 report: lem-sfb-coefficient-mate-module-hom-comparison

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-coefficient-mate-module-hom-comparison.json`: item, statement; split into five proof steps. Statement and statement dependencies preserved. Added current logged Mathlib searches and completed the proof, proof dependency union, proof origin and split report.
- `citations.json`: 17 entries, one for every step/dependency pair, quoted verbatim from the corresponding existing node's statement.
- `report.md`: this report. `searches.jsonl` is the search wrapper's actual log; `write_split.py` is the sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves are reused, not redelivered. No unit or chapter record, Lean source, repository or launcher file was written.

## Attachments

None for this item. I searched `lean/WeilConjectures/` for the exact blueprint tag and the coefficient/mate terminology, then read `CategoryTheory/ModuleObjects/MapMod.lean` (especially lines 235–297), `CategoryTheory/ModuleObjects/ChangeOfScalarsSquare.lean` (especially lines 73–98) and `SixFunctors/ProEtale/ModuleObject/UpperLowerStar/Defs.lean` (lines 175–220). The project has the lifted monoidal adjunction, the square isomorphism and its identity component, and the special case for condensed coefficients. None of these alone states this whole generic coefficient-mate comparison with all its clauses. I therefore split rather than claim a partial attachment. The existing declaration `CategoryTheory.Mod.comapMapModComapIso_hom_app_hom` is already attached to `lem-sfb-comap-mapmod-square-underlying`; I cite that node.

## WANTED

None. All documents used are available locally. No SGA source was used.

## Sources and route

Read `AGENTS.md`, the worker role, the stage-1 brief and stage document, `GOAL.md`, the three levels in `SETUP.md`, the current unit and chapter records, and delivery-errors B–E in both the live and imported versions. This is stage 1 only; nothing was compiled.

The item's source points to the first sentence of the current unit proof, the adjunction furnished by `def-sfb-module-upper-lower-adjunction`. I read the unit proof and that definition's proof in `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-module-pushforward-pullback/`. They give exactly the route: lift the monoidal adjunction, compose with scalar extension/restriction, then identify the right adjoint using the coefficient mate. I also read `sk-def-sfb-transport/def-sfb-modobj-transport-adjunction.proof.md` and `sec-six-functors-basics/sk-def-sfb-coefficient-comparisons/def-sfb-comap-mapmod-square.proof.md`. For the general Hom formulas and composition I read Stacks `categories.tex`, Tag 0037 (`definition-adjoint` and the following adjunction-map formulas) and Tag 0DV0 (`lemma-compose-counits`). Blueprint proofs are agent-written, so the expanded proof is correctly marked `proof_origin.by = agent`.

The route stays inside the unit's lift/scalar-composition argument. The square definition is a generic comparison already named in the item's statement, and its underlying-component lemma is Lean-closed. Monoid transport and the two general categorical adjunction nodes are existing Mathlib leaves. No off-route theorem is substituted for a unit step and no new tool approval is requested.

## Existing-node and Mathlib searches

Ran `tools/blueprint_refs.py ancestor` for the item, and searched the whole imported blueprint for `monoidal adjunction`, `natural bijection`, `coefficient mate` and `mapMod`, alongside whole-DAG terminology searches and project Lean searches. The existing transport adjunction and square comparison supply the formal inputs; the scheme/condensed-coefficient adjunction is only a specialization. No other blueprint node states this whole generic comparison, so `same_as` remains `[]`. The existing exact ancestor/place are retained.

Ran the mandatory search wrapper with this item and group Q60: two different LeanFinder phrasings, Loogle, LeanSearch, the expected-declaration grep, and a broader `scalarRestriction|mapMon|mapMod` grep in `CategoryTheory/Monoidal`. All services answered. Actual query texts and returned names are in the node and `searches.jsonl`; inherited searches are retained. Read the pinned Mathlib `CategoryTheory/Monoidal/Mod.lean:350–415`, `Mon.lean:848–873` and ordinary scalar-restriction comparisons in `Algebra/Category/ModuleCat/ChangeOfRings.lean:200–275`. Mathlib has internal restriction and transport of monoids; `Mon.lean:856` still has a TODO for module transport. Ordinary ModuleCat scalar adjunctions do not specialize to arbitrary internal modules in arbitrary monoidal categories. The item is therefore not a Mathlib leaf.

## Not duplicates

No new nodes were created. All needed facts were found in existing nodes. In particular, I reuse `def-sfb-modobj-transport-adjunction`, `def-sfb-comap-mapmod-square` and `lem-sfb-comap-mapmod-square-underlying` instead of introducing a new node for one of the item's own clauses.

## What was wrong and what was changed

The imported item was an unsplit statement with no proof. Its statement is well typed and true under its explicit assumption that the indicated scalar extension and its adjunction are available. No statement dispute, hypothesis change or correction of the blueprint route was necessary. I supplied the missing proof, including the direction of the square comparison, the actual lax-tensor naturality equation and both adjunct formulas. I did not assume the coefficient map invertible or the right adjoint strong monoidal.

## Review by Q60

I checked delivery-errors B–E with the actual cited statements and the sources open. No new node needs a self-contained statement, new searches, a source tag or a duplicate comparison. The item retains every hypothesis and every conclusion; the proof is not a relabeling into new nodes. Every use has a verbatim statement quote in `citations.json`. The five steps have lengths 682, 715, 1087, 1251 and 1010 characters; none crosses the 2000-character review threshold, and no hidden comparison lemma is left inline.

Step 1 uses the statement of `def-sfb-modobj-transport-adjunction` that the unit at B is a monoid morphism, and clause 1 of `det-def-sfb-ring-object-transport` that G sends a monoid morphism to one. The ring-object morphism definition in `sk-def-sfb-ring-object` gives the unit/multiplication conditions for their composite. I wrote how those equations compose; this is an elementary substitution, not another theorem about monoidal adjunctions. Hypotheses hold because G is lax monoidal and alpha is already a monoid morphism.

Step 2 reads the actions directly from `def-sfb-modobj-restriction` and `def-sfb-modobj-transport`. The structure-map naturality used is explicitly in the statement of `det-def-sfb-ring-object-transport`. Its specialization at (alpha, identity N), followed by tensor bifunctoriality, gives exactly the item's common-action equation. Both expressions have source B tensor GN and target GN. No associator or symmetric interchange is needed: there are only two tensor factors at this point. This is a short calculation from the cited definitions, so it is marked elementary.

Step 3 applies the actual statement of `def-sfb-comap-mapmod-square` with its categories interchanged, since the functor here is G:D to C. I checked all four monoids and all four arrows, and the square is precisely eta = G(alpha) composed with u_B. Its given direction is opposite to theta, so the proof explicitly inverts it. The identity component comes from the statement of `lem-sfb-comap-mapmod-square-underlying`, not from an unmentioned detail of the square node's proof. Removing restriction along identity is the literal action formula of `def-sfb-modobj-restriction`. The module-composition clause of `sk-def-sfb-module-objects` makes the inverse component an identity as well. This handles the specified comparison, not merely some isomorphism of the right adjoints.

Step 4 uses the lifted adjunction exactly as stated in `def-sfb-modobj-transport-adjunction` and the scalar adjunction in clause 2 of `sk-def-sfb-change-of-scalars`. I checked the delicate hypothesis issue here: that latter node gives sufficient braided/coequalizer hypotheses for constructing scalar extension, but the ITEM expressly assumes that this scalar extension and adjunction are already defined. The proof uses the assumed adjunction, not an assertion that those sufficient hypotheses follow for arbitrary C,D. The composite-adjunction node states the exact Hom chain used, with reverse order of the right adjoints. Postcomposition with theta is then bijective by its inverse. I wrote the two naturality checks, and `lem-weil-pbc-adjunction-of-natural-bijection` supplies the adjunction from that natural family. This is a cited use of its statement, not just of the definition of adjunction.

Step 5 uses the underlying Hom-bijection clause of `def-sfb-modobj-transport-adjunction` and the explicit unit/counit formulas in the statement of `lem-weil-pbc-adjunction-of-natural-bijection`. Restriction does not change underlying N; theta and its inverse do not change the arrow by step 3. Thus forward G(tilde t) composed with u_M and inverse v_N composed with F(s) have exactly the stated domains and codomains. Linearity in each direction is supplied by the lifted bijection, and final A-linearity by the assumed scalar adjunction of `sk-def-sfb-change-of-scalars`. Invertibility and naturality follow from composition of these bijections, not from inverting alpha.

I tested F=G=identity, when eta=alpha and the result becomes the usual scalar adjunction; alpha=identity, when it reduces to the lifted monoidal adjunction; and the noninvertible coefficient map Z to Z/2 in abelian groups, when the two actions are the usual restricted action and the Hom formulas are the ordinary scalar ones. Zero modules in this example give singleton Hom sets on both sides. A terminal monoidal category gives only identity comparisons and needs no additive assumptions. These cases test the direction and noninvertibility clauses. No smallness, closedness, commutativity, abelianness or extra exactness hypothesis is used in the proof beyond the explicitly assumed scalar adjunction. No source or statement error was found.

## Unfinished work

None in this stage-1 item. The dependent nodes retain their own states; no claim is made here to prove them in Lean. Required remote checks and the delivery dry run are run before pushing.
