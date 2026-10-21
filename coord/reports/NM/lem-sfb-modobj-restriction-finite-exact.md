# Worker report: lem-sfb-modobj-restriction-finite-exact

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-modobj-restriction-finite-exact.json`: item, statement; split into five steps. Statement and statement dependencies unchanged. Mathlib has ordinary scalar restriction, but not this theorem for arbitrary internal monoids.
- `dag/nodes/sec-six-functors-basics/lem-sfb-modobj-forget-creates.json`: new statement-only supporting node; no Mathlib match. The general internal-module lifting construction already has project declarations, recorded below for attachment. Its audit state is left `none` for the maintainer's transitive closure check, rather than asserting a newly measured closure state.
- `citations.json`: one entry per cited node per numbered proof step, with verbatim statement excerpts.
- `searches.jsonl`: actual search-command log; used to populate the Mathlib records without inventing queries or results.

## Attachments

`CategoryTheory.Mod.createsLimit` belongs to `lem-sfb-modobj-forget-creates`, `lean/WeilConjectures/CategoryTheory/Monoidal/Mod/Limits.lean:109` (limit clause).

`CategoryTheory.Mod.createsColimit` belongs to `lem-sfb-modobj-forget-creates`, `lean/WeilConjectures/CategoryTheory/Monoidal/Mod/Limits.lean:215` (colimit clause).

The same file explicitly constructs the actions and universal cones/cocones: `limitSMul`, `limitModObj`, `isLimitLiftedLimitCone`, `colimitSMul`, `colimitModObj`, and `isColimitLiftedColimitCocone`. I read their complete definitions and proofs. There is no `sorry` in this file or its project import `WeilConjectures/Mathlib/CategoryTheory/Monoidal/Mod.lean`; the maintainer's tool remains responsible for verifying transitive closure. No declaration in `WeilConjectures/` states the item itself: the tag search is empty and the internal-module source defines scalar restriction and constructs (co)limits separately. Ordinary ModuleCat restriction and abelian-special-case project facts do not cover arbitrary monoidal categories.

## WANTED

None. The source of the item is an agent-extracted generalization of the first sentence of `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-module-lower-shriek/def-sfb-module-open-lower-shriek.proof.md`. Its internal-module construction is explicit in the project source above. I do not assign a Stacks tag to a general monoidal-category assertion that the cited Stacks material does not state. The item's proof remains agent-origin, not a claimed literature theorem.

## Findings and unfinished work

The imported statement is correct, including the absence of closedness, braiding, commutativity, and invertibility assumptions. No statement dispute or change of unit route is needed. The seed had no proof, so its nontrivial internal-module lifting argument needed to be named. The new node states that construction for an arbitrary small diagram with an existing underlying (co)limit; it does not state scalar-restriction preservation. Finite existence and preservation are actually proved in the item, rather than renamed as new nodes.

All five steps are below 1000 characters; none exceeds 2000. The only universal-property comparison inside steps 3 and 4 is the elementary argument that the unique maps between two universal cones or cocones are mutually inverse. It is written out and is not a further lemma hidden behind “transport”. No compiler, Lake, build tool, forbidden server checker on this machine, repository write, or ordinary git command was used.

The support node is intentionally not recursively split. Its exact project attachment candidates are supplied for the maintainer's independent check. No mathematical part of this item remains unfinished.

## Search and duplicate review

I searched the full DAG statements for module forgetful functors, limits/colimits, and creation, searched text for `Mod.createsLimit` and `Mod.createsColimit`, and read the potentially relevant kernel, abelian, Grothendieck, scalar-restriction, module-equivalence, and lifted-pullback statements. I ran `tools/blueprint_refs.py ancestor` and blueprint searches including `module limits`, `forgetful colimits`, `internal module`, `module colimit`, `module objects`, `forget creates`, and `monoid colimits`. The ancestor is `def-sfb-module-open-lower-shriek`; the new node's `via` is the item. No blueprint node states arbitrary-diagram internal-module creation. The item's previously recorded `same_as` entries are retained: they are the abelian special cases used by its parent, not substitutes for its generality.

Mathlib searches used only `msearch.py`. Both the item's scalar-restriction question and the support node's lifting question received semantic searches, Loogle patterns, and local Mathlib grep; two phrasings were used. All services answered. The internal `Mod.comap` and `Mod.forget` hits are definitions, not (co)limit theorems. I read Mathlib `CategoryTheory/Monoidal/Mod.lean:351–405` and `Algebra/Category/ModuleCat/ChangeOfRings.lean:932–950`: the latter preservation instances are for ordinary rings in Type and ModuleCat, not arbitrary internal monoids. MonCat and representation results likewise have different ambient objects. The new node is therefore not a Mathlib leaf; its implementation is a project theorem.

## Not duplicates

- `lem-sfb-modobj-forget-creates` vs `lem-sfb-modobj-kernels`: the latter lifts one kernel in an additive monoidal category; the new node concerns arbitrary small diagrams, both universal cones and tensor-preserved universal cocones, without any additive hypothesis. The existing kernel statement is not general enough.
- `lem-sfb-modobj-forget-creates` vs `lem-sfb-modobj-abelian`: abelianness of the module category does not assert that specified underlying universal cones and cocones lift, and assumes an abelian ambient category.
- `lem-sfb-modobj-forget-creates` vs `sk-def-sfb-change-of-scalars`: change of scalars defines Res/Ext/Coext and states an abelian exactness special case; it gives no underlying-diagram creation theorem in an arbitrary monoidal category.
- `lem-sfb-modobj-forget-creates` vs `det-prop-sfb-module-pullback-exact-lifted`: the latter is an additive exactness lifting theorem between abelian module categories, not arbitrary-diagram creation without additive hypotheses.
- `lem-sfb-modobj-forget-creates` vs `lem-weil-pbc-internal-module-ab-equivalence`: the latter identifies modules in Ab with ordinary ModuleCat, not modules in an arbitrary monoidal category.
- `lem-sfb-modobj-forget-creates` vs `lem-weil-pbc-constant-internal-module-sheaf-equivalence`: that equivalence has sheafification and site hypotheses and does not supply the general lifting statement.
- `lem-sfb-modobj-forget-creates` vs `lem-coef-module-operadic-colimit-detection`: that assertion is about coherent modules in an infinity-category and assumes preservation by every acting object. Here the category is ordinary, only A-tensor preservation is needed, and limits require no preservation hypothesis.
- `lem-sfb-modobj-forget-creates` vs `lem-sfb-modobj-restriction-finite-exact`: the new node has one monoid, an arbitrary indexing category and a specified underlying universal (co)cone; it constructs a module action. The item has a monoid morphism and proves finite existence plus preservation by a specific scalar-restriction functor. Its proof must still identify restricted actions and handle arbitrary universal cones/cocones.

There are no common Stacks tags in this delivery.

## Supporting construction checked

For clause 1, on an underlying limit L, define the action a by p_j a = a_j(A tensor p_j). Naturality of the diagram makes the right sides a cone. The limit universal property supplies a. Postcompose each action identity with every p_j: the unit identity becomes that of K(j) using naturality of the left unitor, and the associativity identity becomes that of K(j) using tensor functoriality and naturality of the associator. Joint determination by the p_j proves both identities. For any module cone with apex N, the underlying limit lift f:N→L is linear because its linearity equation agrees after every p_j. Underlying uniqueness gives uniqueness in modules. Any other action making the p_j linear satisfies the same equations and hence equals a. No preservation by A tensor is used for limits.

For clause 2, if i_j form an underlying colimit, preservation by T=A tensor makes T(i_j) a colimit cocone. Define b:A tensor Q→Q by b T(i_j)=i_j a_j. This also uniquely determines b among actions making i_j linear. Precomposing the unit identity with every i_j proves it from the units on K(j). For associativity, use the colimit cocone T²(i_j): applying the same J-colimit-preserving T twice preserves the cocone. The two sides of the action associativity equation agree on each T²(i_j) by associativity on K(j), tensor bifunctoriality and associator naturality. For an arbitrary module cocone Q→N, its underlying colimit desc f is linear because the required equality agrees after every T(i_j). Underlying uniqueness gives the module universal property. This is precisely the computation read at project Limits.lean:133–221, and shows why no separate hypothesis on A tensor A or right tensor factors is missing.

## Review by NM

I read the item's source sentence, the current chapter and unit records, and both complete constructions in project `CategoryTheory/Monoidal/Mod/Limits.lean`. The source only asserts exactness in the sheaf application; the item generalizes the construction, and my proof uses exactly its monoidal and finite-(co)limit hypotheses. I retained all the item's statement dependencies, its statement text, and its blueprint provenance. The new node states the universal construction in that source file, with J small and with preservation by A tensor explicitly required only for the colimit clause. It is statement-only, with an empty proof and proof-dependency list, real search results, an unused id, a source place, and the correct ancestor/via fields.

For step 1 I opened `def-galois-finite-limits-colimits`: it quantifies over finite indexing categories, which supplies the underlying universal cones/cocones used here. Both clauses of the new node give their lifts, and the two separate hypotheses R tensor and S tensor preserving finite colimits provide exactly its colimit assumption. This proves existence for every finite diagram in each module category.

For step 2 I opened `def-sfb-modobj-restriction`: its statement explicitly gives the restricted action, says S-linear maps become R-linear, and states identity on underlying objects and morphisms. Therefore the equality of underlying diagram and cone/cocone data used here is definitional, not a property borrowed from its proof. This step is elementary.

For step 3 the new node's first clause supplies a unique action on the same underlying limit vertex. The restricted S-action makes the same projections R-linear by step 2. Hence the actions agree and the restricted chosen lift is limiting. The maps comparing any other limiting cone to this one are unique maps from their universal properties; their two composites must be identities. A functor preserves these equations, and the explicit factorization through the cone isomorphism proves the universal property after restriction. No uncited theorem about arbitrary exact functors or forgetful reflection is assumed.

For step 4 the new node's second clause is used twice, with S and then R; I checked separately that both tensor-preservation hypotheses are present. The cocone legs are unchanged by the restriction node's statement. The same action uniqueness identifies the two module cocones. The proof writes out how arbitrary colimiting cocones are handled, so it does not assert only preservation of a convenient chosen colimit. These are the parts of both cited statements included verbatim in `citations.json`.

For step 5 I opened `def-galois-exact-functor`, whose statement defines exactness as both finite-limit and finite-colimit preservation. It requires no abelian structure. The finite existence assumptions were established in step 1; this final inference is elementary. Every non-elementary construction used by the item is the new cited statement, rather than a conclusion read only from some cited node's proof. The proof dependencies are exactly the union of the uses lists; no support-node dependency returns to this item.

I tested the empty indexing category explicitly: a terminal object carries the unique action for the empty limit, and preservation of the empty colimit makes A tensor 0 initial, permitting the unique action on 0. For a singleton diagram the original module action is recovered. In Set with cartesian tensor, the result is the familiar construction for actions of arbitrary monoids; no additive category is available there, demonstrating that the abelian alternatives are insufficient. In Ab I checked a noninvertible map Z→Z/2: restriction is exact although extension of scalars need not be, so the proof must use underlying cocones, not flatness or an inverse coefficient map. Zero rings, zero modules, and empty categories of indices introduce no exception. For nonbraided categories the formulas use only left tensoring and the associator; no interchange of factors occurs.

I checked B1–B10, C1–C8, D1–D5, and E1–E7 against these files. No source error, missing hypothesis, unit-route replacement, generic off-unit theorem use, or SGA source was needed. No corrections to the imported statement were made. The distinction between the supporting lifting result and the actual preservation argument is intentional; no clause of the item is merely relabeled as a new theorem.
