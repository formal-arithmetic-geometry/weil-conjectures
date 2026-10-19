## Worker report

# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-cocartesian-categorical-base-change.json`: statement node, split in five steps; no Mathlib match. Its statement, statement dependencies, source, creation metadata and blueprint ancestry are unchanged.
- `citations.json`: one entry for each cited node in each numbered step, with the actual statement copied verbatim as the quote.
- `report.md`: this report. `write_split.py` is sandbox-only preparation, not a delivery file.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id and cocartesian/coCartesian/Cocartesian, categoricalEquivalence/CategoricalEquivalence and Joyal; no project declaration states the item. The reference master source was also searched, without treating its sorry declarations as completed proofs. This node has no recorded slopmaster2 declaration or open frontier requiring a separate attachment.

## Sources wanted

WANTED: Kerodon Corollary the project server, tag 029H, and Proposition the project server, tag 025H, archived source, for lem-coef-cocartesian-categorical-base-change.

WANTED: Jacob Lurie, Higher Topos Theory, Section 3.1.3, Corollary the project server, Proposition the project server and Corollary the project server, archived source, for lem-coef-cocartesian-categorical-base-change.

These were read online, not downloaded into the shared literature. Kerodon and HTT are not present in the named literature tree. The proof is therefore marked `proof_origin.by = agent`, with its actual source URL and places. The tags are Kerodon tags; there is no Stacks tag stating this quasicategorical theorem.

## Findings and corrections

The item is true as stated. Its full arbitrary-simplicial-set scope is supported by Kerodon 029H and by the opposite of HTT Proposition the project server. Neither A nor B needs to be fibrant, and u need not be a monomorphism. No statement dispute or statement change is needed.

The live shared snapshot acquired a reviewed split of `lem-coef-marked-relative-cartesian-model` during this reading, including the existing statement-only `lem-coef-cartesian-base-equivalence-invariance`. Reopened both current files. This permits a shorter split using the existing conditional Cartesian theorem, rather than constructing new flatness or model-localization nodes. I have not created any nodes restating its clauses. The conditional theorem requires a family of relative marked model structures: step 1 explicitly supplies this family before step 4 uses its conclusion. Its arbitrary-base definition and its precise clause (1) are retained.

The Mathlib searches were run only with the prescribed msearch command under group NM and this item, including the second phrasing. All four services responded. Read the returned ordinary cocartesian definitions, all-horn Kan fibration definitions, generic base change instances, internal-Hom corner theorem, and Joyal's trick. They do not state this theorem. Three exploratory searches about generic model localization were also recorded; they are not ingredients of the final proof. Existing inherited search history was retained, and the new searches were appended. No Mathlib leaf is claimed.

## Not duplicates

No new nodes. Whole-DAG statement searches for categorical equivalence, cartesian/cocartesian pullback and homotopy pullback found the existing relative marked model theorem, its conditional Cartesian base-equivalence theorem, and the relative marked lifting calculus. These are cited. `tools/blueprint_refs.py ancestor lem-coef-cocartesian-categorical-base-change` gives `prop-coef-integral-exceptional-adjoint`; searches for `cocartesian categorical equivalence` and `categorical` over the whole imported blueprint gave no blueprint node stating this result. The broader categorical search returned ordinary trace/category material. The item's `same_as` remains empty. No elementary step was promoted to a node.

## Review by NM

I read Kerodon 029H in full and followed it to 025H. The former states the categorical-equivalence consequence for simplicial sets; the latter expressly describes two successive arbitrary pullback squares, exactly the scope required here. I also opened the HTT PDF and read Proposition the project server and Corollary the project server on printed pages 205–206. The Cartesian theorem is dual to the present assertion after the initial pullback to B. The proof below stays at the existing marked-model foundation. It does not use the relative-exponential restriction node above this item.

For step 1, I opened the current statement of `lem-coef-marked-relative-cartesian-model` and compared it with every family hypothesis in the statement of `lem-coef-cartesian-base-equivalence-invariance`. The model class, cofibrations, sharp mapping tests, fibrant objects, enrichment, fiber/inverse criteria and every base-change Quillen adjunction are all stated. The simplicial tensor is the marked product with K sharply marked: currying identifies maps U × K^sharp → V over the base with simplicial maps K → Map^sharp(U,V), using its displayed enrichment. This is a degreewise identification, not an extra model theorem. The fixed universe is the one used in the family statements, so no size assumption is lost. This is a non-elementary application of the existing model theorem; I do not claim to reprove it from its definitions.

For step 2, I reopened `def-coef-infinity-fibrations`: it gives the initial/final horn criteria and the prescribed source/target lifts for the given quasicategories Z and S. Reversing the order in a simplex sends those precise horns and prescribed edges to one another. The statement of `lem-coef-joyal-model-structure` gives the hFun testing convention and the generating presentation of h; reversing the two factors in the simplicial internal Hom and the 2-simplex composition relations proves the two displayed opposite identities. Taking the opposite of a quasi-inverse equivalence of ordinary categories remains an equivalence, so testing u at C^op proves the categorical-equivalence assertion for u^op. This is the written elementary argument, not an unquoted theorem that opposites preserve Joyal weak equivalences.

For step 3, I reopened `lem-coef-relative-marked-anodyne-calculus`. Its final paragraph says that pullback of a cartesian fibration along any map is cartesian, and its first paragraph explicitly extends the horn definition to arbitrary simplicial bases and total spaces. Thus the application to b^op has all hypotheses, even for non-quasicategorical B. In particular I have not applied the more restrictive quasicategory definition directly to E → B^op.

For step 4, I reopened clause (1) of `lem-coef-cartesian-base-equivalence-invariance`. Substitution S = B^op, Z = E, T = A^op, a = u^op gives exactly the projection stated in this step. The family hypotheses came from step 1, the fibration hypothesis from step 3, and the equivalence hypothesis from step 2. The clause explicitly imposes no quasicategory condition on S or T. It states categorical equivalence of the actual projection, not just equivalence of its endpoints. No monomorphism hypothesis was inserted.

For step 5, I reopened the degreewise-pullback convention in `def-cbc-enhanced-diagrams-cones` and the testing definition in the Joyal node. I checked the two inverse degreewise formulas and both projections; the map after reassociation is exactly (a,z) ↦ (u^op(a),z). Opposite reversal yields precisely the map u_Z in the original statement. The already-written opposite testing argument works in both directions because reversal is an involution. Nothing about a homotopy category of model categories or its saturation is being assumed here.

Against B1–B10 there are no new nodes, hollow notions or unsearched new statements. Against C1–C8 I read the statements of every cited node, supplied a verbatim quote for every step/node pair, and used no node's internal proof as an interface. The non-elementary facts are the family of marked models, arbitrary-base pullback stability, and conditional Cartesian base-equivalence invariance, each explicitly cited. Every proof citation is in the same unit; no tool use is needed. I checked the dependency closures of the reused theorems and found no path back to this item. The server checks remain authoritative. Against D1–D5 no content was moved to a new restatement node; the steps carry all opposite and iterated-pullback identifications and discharge the existing conditional theorem's hypotheses. Against E1–E7 the object E is B^op ×_(S^op) Z^op, not an unrelated fiber, and the final map preserves the original b and bu structure maps.

Small cases checked: S or Z empty; r the identity; u the identity; S a point (product with Z); u a noninjective equivalence of nerves of contractible groupoids; and u an inner horn inclusion. The construction uses arbitrary A,B, not their nerves or their homotopy categories. For the simplest explicitly nonfibrant-base case, take B = Λ²₁ (the inner 2-horn), A = B, u = id and r = id_(Δ⁰): the intermediate q is id_B and is covered by the cited arbitrary-base theorem. Empty pullbacks require no point choices, and all opposite and reassociation formulas remain valid. More generally inner-horn u = Λ²₁ → Δ² is admitted without presuming its source fibrant. I corrected the initial possible route through quasicategory-only pullback theorems by instead using the existing arbitrary-base marked calculus and the Cartesian theorem. No new node requires a separate small-case test.

The chapter and unit files and the main-20261015 ancestor proof were read. This item is below the displayed coefficient-adjunction calculation, along its preserved relative-exponential via chain. No chapter/unit route, target statement, coefficient category or base-change morphism was changed. Unit realized fields do not belong to this item and were not edited.

## Unfinished work

None in the requested one-level split. There are no new nodes to split. Awaiting the required fresh second reader; no delivery push is authorized in this turn.

## Second reading by NM

- Item statement: read Kerodon Corollary the project server (029H) and Proposition the project server (025H), and HTT Proposition the project server on printed pp. 205–206. Kerodon 025H explicitly treats two successive arbitrary pullbacks, so its bases are respectively A, B and S, its cocartesian fibration is r, and its categorical equivalence is u. The item retains the hypotheses that Z and S are quasicategories while imposing none on A or B and no injectivity on u; all hypotheses and the actual projection agree. There is no Stacks source for this quasicategorical statement, and no statement correction is needed.
- Step 1: reopened the complete statement of `lem-coef-marked-relative-cartesian-model` and compared it with every family hypothesis of `lem-coef-cartesian-base-equivalence-invariance`; model classes, cofibrations, sharp mapping tests, natural fibrant markings, enrichment, fiber/inverse tests, input universes and Quillen adjunctions all agree. Read HTT Corollary the project server on printed p. 162. Expanded the tensor assertion into its currying bijection and its compatible simplex restrictions, so it follows from the cited enrichment and marked-product definitions rather than an unstated theorem.
- Step 2: reopened `def-coef-infinity-fibrations` and `lem-coef-joyal-model-structure`; reversal sends index i to n-i, the distinguished first edge to the last edge, and prescribed sources to prescribed targets. The item has the quasicategory hypotheses this definition requires. The two internal-Hom/h-category opposite identities follow by reversing both factors and the edge/2-simplex presentation; an opposite ordinary equivalence has the opposite quasi-inverse. Made the order-reversal automorphism explicit as $\rho(\alpha)(i)=n-\alpha(m-i)$ and defined the simplicial operators of the opposite. This is a clarification of the correct construction, not a statement dispute.
- Step 3: reopened the arbitrary-base pullback clause of `lem-coef-relative-marked-anodyne-calculus`, and checked the object $E=B^{\mathrm{op}}\times_{S^{\mathrm{op}}}Z^{\mathrm{op}}$ and projection q. That clause applies to the reversed cartesian fibration and arbitrary $b^{\mathrm{op}}$, even when B is not a quasicategory. It requires no model structures, so does not use a hidden hypothesis from step 1.
- Step 4: reopened clause (1) of `lem-coef-cartesian-base-equivalence-invariance`: substituting $S=B^{\mathrm{op}}$, $Z=E$, $T=A^{\mathrm{op}}$, and $a=u^{\mathrm{op}}$ gives exactly v. Steps 1–3 provide every conditional-model, fibration and equivalence hypothesis. The cited statement supplies the actual projection for arbitrary bases, not an equivalence of unspecified objects. This is an existing general Cartesian theorem, not a new restatement node.
- Step 5: reopened `def-cbc-enhanced-diagrams-cones` and `lem-coef-joyal-model-structure`. The two displayed degreewise maps are inverse and commute with operators; the condition $b_0=u^{\mathrm{op}}(a)$ identifies the projection v with the required map on pairs. Expanded the final categorical-equivalence test into the opposite restriction functor at $C^{\mathrm{op}}$, replacing the reference to applying the previous calculation in reverse.
- New nodes: none. B1–B7 create no statement, definition, duplicate or leaf to audit. The delivery contains only the original item, with its statement, statement dependencies, source, ancestry and creation metadata unchanged; citations.json has seven step/node pairs and every quote equals the current cited statement verbatim.
- Edge cases: for empty S both A and B are empty, and for empty Z both pullbacks are empty; all displayed maps are identities in these cases. For r or u an identity the reassociation formulas reduce to the relevant identities. For $S=\Delta^0$ the assertion is invariance under product with Z. For $B=\Lambda^2_1$, $A=B$, $u=1$ and $r=1_{\Delta^0}$, q is the identity of the non-quasicategory B and the cited arbitrary-base clause applies. In degrees 0 and 1 the reversal formulas fix vertices and reverse the ordered edge, respectively; pullback formulas are valid in both. The noninjective nerve equivalence collapsing the two-object contractible groupoid to a point is also admitted. No point choice, nonemptiness, or monomorphism is used.
- Independent searches: ran fresh prescribed msearch LeanFinder, Loogle and grep queries with flat-inner-fibration/weak-equivalence vocabulary. LeanFinder returned generic model-category and truncated-nerve declarations; read the all-horn definition in Mathlib `CategoryWithFibrations.lean:44–82`, the truncated-nerve `functorEquiv` in `NerveAdjunction.lean:288–312`, and generic full-subcategory weak-equivalence identifications in `Bifibrant.lean:120–125,194–199`. None states this item; Loogle and grep returned zero hits. The actual search records are appended in searches.jsonl and mathlib_searches. No Mathlib leaf is claimed.
- Scope/route: read coord/dag-sync.md, GOAL.md, the unit/chapter records and the current main-20261015 ancestor proof at `sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, paragraph 2's displayed derived adjunction. This split follows the existing relative-exponential via chain below that proof. All theorem dependencies are in the item's unit; no route, target or maintainer-owned unit metadata changes. A read-only source search found no cocartesian/Joyal declaration in slopmaster2 or master. No SGA source is used.

Changes made: expanded step 1's tensor currying, step 2's simplex reversal, and step 5's final opposite test; appended genuine independent Mathlib search records; added this second reading. The statement and citation set were unchanged. The elementary work in steps 2 and 5 is the displayed order/coordinate/presentation calculation; the non-elementary model, pullback and Cartesian invariance facts remain explicit citations to their current interfaces.

## Q71 repair note
The prior NM delivery was live-superseded before this group ran and left no Lean record. I supplied the missing statement module `Sheaf.CategoryTheory.CocartesianCategoricalBaseChange`. It uses the existing `CategoryTheory.CoherentNerve.IsCategoricalEquivalence` predicate and Mathlib's degreewise `pullback.map`; the displayed map is the canonical map from the pullback over `u ≫ b` to the pullback over `b`, induced by `u`, `id Z`, and `id S`. The cocartesian hypothesis is retained as `hr` exactly as required by the node's cocartesian-fibration clause. The theorem proof is `sorry` as required for stage 2. Compilation with `scompile.py` succeeded without errors or warnings.

## Earlier second reading (a previous round; superseded)
I reread the node statement, the three recorded statement dependencies, and the completed Lean signature. The binders introduce quasicategories `S` and `Z`, the cocartesian map `r`, arbitrary simplicial base map `b`, categorical equivalence `u : A ⟶ B`, and the induced canonical degreewise pullback map. The Lean map uses `pullback.map` with `u`, `𝟙 Z`, and `𝟙 S`, and its two commutativity proofs are definitional simplicial-map identities. The theorem has a postponed proof only. Edge cases include identity `u`, empty pullbacks, and arbitrary (possibly non-quasicategorical) `A` and `B`; no monomorphism or nonemptiness condition is added. The existing project predicate is imported from `CoherentNerveInfrastructure`, avoiding a duplicate notion. `scompile.py` compiled the module cleanly.

## Second reading by Q71

This is the independent stage-2 reading of the repaired Lean module, superseding
all earlier signature assessments in this inherited report. I opened the item's
current node and sandbox module together, all three statement-dependency nodes
and their recorded source modules, and the source of the additional categorical
predicate used by the first worker. There is no statement_change, new node, or
dependency-module delivery. The natural-language node is unchanged.

Source check: the source is Kerodon, not a Stacks .tex lemma. I independently read
https://kerodon.net/tag/029H (Corollary the project server) and
https://kerodon.net/tag/025H (Proposition the project server), including their displayed diagrams
and proofs. The latter treats two successive arbitrary simplicial pullbacks of a
(cartesian or cocartesian) fibration of infinity categories. Substitute Z → S for
U, B → S for the right-hand base map, and A → B for the equivalence. This gives
exactly this node. There is no ambient nonemptiness, monomorphism, or fibrancy
assumption on A or B. The item explicitly keeps the quasicategory hypotheses on
Z and S. There is no source-based correction to make.

My object/hypothesis/conclusion list and its Lean rendering:

1. One fixed universe of simplicial sets, containing S, Z, A, B:
   `(S Z A B : SSet.{u})`. The input universe u is arbitrary. Verdict: exact.
2. S and Z are quasicategories: `[SSet.Quasicategory S]` and
   `[SSet.Quasicategory Z]`. I opened Mathlib's inner-horn definition in
   Quasicategory/Basic.lean and the enhanced-diagrams node. No instance for A
   or B occurs. Verdict: exact, including empty quasicategories.
3. A simplicial map r : Z → S which is cocartesian:
   `(r : Z ⟶ S) (hr : cocartesianFibration r)`. I opened
   Sheaf.CategoryTheory.InfinityFibrations, especially IsCocartesianEdge and
   cocartesianFibration. The recorded declaration requires the two instances
   already supplied here and includes InnerFibration plus lifts of each base
   edge with prescribed source and the initial outer-horn condition. It is the
   node's notion, not ordinary-category cocartesian arrows. Verdict: exact.
4. Arbitrary simplicial sets A, B, map b : B → S, and map u : A → B:
   `(b : B ⟶ S) (u : A ⟶ B)`. Neither u nor b has an injectivity or fibration
   binder. Verdict: exact.
5. u is a categorical equivalence in the dependency's convention:
   `hu : ∀ (C : SSet.{max u v}), C.Quasicategory →
   ((hoFunctor.map ((MonoidalClosed.pre
   (uliftFunctor.{v, u}.map u)).app C)).toFunctor).IsEquivalence`.
   I read the full signature of SSet.exists_joyal_model_structure and Mathlib's
   hoFunctor/uliftFunctor. This is verbatim its weak-equivalence test. The
   internal hom is the simplicial Fun, MonoidalClosed.pre is restriction,
   hoFunctor imposes edge/triangle relations, and IsEquivalence concerns the
   resulting ordinary functor. Verdict after repair: exact. Both universes u
   and v are declared; max u v permits arbitrary enlargement, including v = 0.
6. A has structure map bu to S: the source pullback is
   `pullback (u ≫ b) r`. This is composition b after u, not an independently
   chosen map or a homotopy-pullback replacement. Verdict: exact.
7. The specified u_Z has target `pullback b r` and coordinates u and id_Z:
   `pullback.map (u ≫ b) r b r u (𝟙 Z) (𝟙 S) (by simp) (by simp)`.
   The cospan structure maps are exactly bu,r and b,r. The two simp proofs
   certify the commuting squares, not extra mathematical hypotheses. Evaluation
   of the presheaf pullbacks gives (a,z) ↦ (u(a),z) degreewise. Verdict: exact.
8. The conclusion asserts categorical equivalence of that actual canonical map:
   the same larger-universe hoFunctor/MonoidalClosed.pre testing expression,
   now applied to `uliftFunctor.map (pullback.map ...)`. It gives all test
   quasicategories after all the object and equivalence hypotheses, with no
   chosen inverse or merely existential equivalence of endpoints. Verdict:
   exact. No other conclusion clause is added or omitted.

Mismatches found and repaired:

- The worker used CoherentNerve.IsCategoricalEquivalence for both hypothesis and
  conclusion. Opening its definition revealed tests on cores of internal homs
  only in SSet.{u}; the cited Joyal dependency instead records ordinary
  homotopy-category tests in SSet.{max u v}. I replaced both occurrences with
  that dependency's exact expression and declared v. I do not assert those two
  mathematical characterizations are inequivalent; this repair avoids silently
  assuming their comparison and preserves the stated universe scope directly.
  No replacement predicate or private definition was introduced.
- The theorem's short proof-plan docstring omitted the marked-model family,
  arbitrary-base pullback step, and precise reassociation/test calculation. I
  expanded it to the node's five steps, naming every cited node and spelling out
  reversal, currying and both reassociation maps. No theorem was proved.
- The stated proof dependency MarkedRelativeCartesianModel had been omitted
  from imports. I added its ordinary (non-public) import as required by the
  stage-2 rule. I removed the public CoherentNerveInfrastructure import: it no
  longer supplies any symbol in this statement. The two proof dependencies
  relative-marked-anodyne-calculus and cartesian-base-equivalence-invariance
  have no recorded Lean modules in this snapshot, so none is invented here.

Dependency/interface check: EnhancedDiagramsCones provides the Mathlib simplicial
primitives; InfinityFibrations is used through its recorded declaration;
JoyalModelStructure supplies exactly the testing convention above. I also read
MarkedRelativeCartesianModel's recorded theorem and its source signature for
its proof-only import. There is no sibling module or new definition node to
review under H12/H13. The only postponed theorem in this delivery is
SSet.Enhanced.cocartesian_categorical_base_change, with whole proof `by sorry`.
There are no data definitions, axioms, private copies or hollow constructions.

Edge cases: empty S forces all objects mapping to S to be empty; empty Z gives
empty pullbacks without a point choice. Empty A or B is not excluded (hu still
has to hold). For u = id the map is the canonical identity comparison; for
S = Δ[0] it is the product comparison with Z. A non-quasicategorical A or B,
for example B = Λ²₁ with identity u, is permitted. Noninjective equivalences,
such as the nerve of the collapse of a contractible two-object groupoid, are
permitted. No dimension parameter or positive-dimension hypothesis is added;
the degreewise map covers degrees zero and one as well as higher degrees.
There is no coefficient ring, characteristic, zero object or scheme in this
statement, so those potential exclusions do not arise. The universes of input
simplicial sets are equal exactly as the node specifies, while test objects may
live in any max u v. autoImplicit is false, and I checked all binders by eye.

Independent searches (all via the required Q71/item msearch wrapper where
applicable):

- LeanFinder: `pullback along cocartesian fibration categorical equivalence`.
  Eight hits were ordinary FiberedCategory Cartesian/cocartesian arrows or
  CategoricalPullback.functorEquiv. I opened the ordinary cocartesian definition;
  it has ordinary categories and a unique factorization, not simplicial horns.
- Loogle: `"IsCategoricalEquivalence"`. Zero hits.
- LeanSearch: `Pullback of a Joyal equivalence by a cocartesian inner fibration
  preserves categorical equivalences of simplicial sets`. Eight hits concerned
  generic fibrations, ordinary pullbacks, sieves and Joyal's trick. I opened
  ModelCategory/Instances.lean: the base-change weak-equivalence instances need
  trivial fibrations, so they do not state this arbitrary-u result.
- Fresh rg searches used `cocartesian.*categorical`,
  `categorical.*cocartesian`, `base.?change.*categorical`,
  `IsCategoricalEquivalence`, `flat.?inner` and capitalization variants across
  Mathlib, /home/ubuntu/weil-src-slopmaster2/WeilConjectures, and the shared
  lean/Sheaf. There is no upstream theorem for this item. The shared project
  has the InfinityFibrations predicate, the differently expressed coherent-nerve
  predicate, Joyal's explicit test, the marked model package, and a downstream
  reference in RelativeExponentialRestriction. IsofibrationBaseChange assumes
  two quasicategorical isofibrations and a functor equivalence; I opened it and
  confirmed it is a different statement. The arbitrary-base Cartesian node is
  already a proof dependency, not an existing Lean match for this declaration.
  No duplicate definition or statement was added.

Validation: the final module compiled cleanly via the prescribed scompile.py,
including the private-overlay compilation of its proof-only import. An initial
line break before `.IsEquivalence` was rejected by Lean and was repaired before
this clean compile. The node's lean.statement was extracted from `theorem`
through the colon-signature before `:= by`, verbatim; only its lean field was
changed. The module lines are at most 100 characters. The next steps are the
required server dry run and delivery.

Dry-run result: deliver2.py --no-push printed OK for commit 72fdbc8a3f: preflight passed and the module compiled. The wrapper correctly excluded the inherited stale lean_audit field; I also restored that field in the sandbox from the current shared node. Only lean differs now. The final delivery uses the same checked Lean signature.
