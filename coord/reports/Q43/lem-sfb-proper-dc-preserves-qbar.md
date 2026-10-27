# Q43 — lem-sfb-proper-dc-preserves-qbar

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-proper-dc-preserves-qbar.json`: existing statement, now split into six steps. No statement or Lean signature changed. No new nodes or Mathlib leaves.
- `citations.json`: sixteen entries, one for every step/node pair, with literal excerpts of the current cited statements.
- `report.md`: this report. `searches.jsonl` was produced by the required search command.

## Attachments

None. I searched the project `WeilConjectures/` by the item tag, proper/constructible terminology, and the exact coefficient-specific declaration. `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj`, in `ProperLowerStarEllAdic.lean:119`, ends in `sorry` at line 125. The other occurrences consume that declaration. The general constructibility and uniform-bound declarations in `Sheaf/AlgebraicGeometry/EllAdicProperConstructibleCohomology.lean` and `EllAdicProperHeartUniformBound.lean` are also sorried; they are existing DAG inputs, not attachments.

## WANTED

None for this split. Bhatt–Scholze, the current blueprint, the Stacks source and the project comparison declaration are available locally. No download was made.

## Corrections and scope

The imported item has no proof. Its explicit hypotheses allow any Noetherian k-scheme Y, including a structure morphism which is neither separated nor finite type, and characteristic zero. Thus merely citing the rational proper-base-change theorem on standing separated finite-type positive-characteristic schemes would not prove this item. I use the existing Noetherian proper-finiteness inputs whose statements expressly cover the item's hypotheses. This is the proper-finiteness component already called for by the open-coefficients unit, with generic derived-category assembly; it does not replace the unit's open-image route.

I checked the live coefficient definition in `CategoryTheory/RingObjects/Condensed/EllAdic.lean:160–234`: `padicAlgClRingObj` is the finite-subextension-valued condensed ring, exactly as `sk-def-sfb-qlbar-condensed` states. It is not the all-continuous-map coefficient convention. I did not use the all-continuous comparison or generator lemmas. No characteristic, finite-type or coefficient-topology hypothesis was silently added.

The inherited `blueprint.same_as` listed `det-thm-sfb-proper-base-change-rational`. That node has several clauses and stronger standing-scheme hypotheses; it does not state this full Noetherian-base item. After whole-blueprint searches, I set `same_as` to the empty list and retained the existing precise `from` reference to `lem-sfb-dc-lower-star-preserves`. The ancestor helper prints None because this maintainer-created audit node has `created.item: null`; no new node is being created that would require a computed ancestor.

## Mathlib searches and duplicate checks

I ran the required msearch commands for this item, with two semantic phrasings, two grep patterns, LeanSearch and Loogle. All executed queries are preserved exactly in the appended `mathlib_searches` and the command log. Two Loogle patterns reported unknown identifiers; the report records invalid queries, not successful absence evidence, and the subsequent valid `AlgebraicGeometry.IsProper` search returned the ordinary scheme-morphism infrastructure. LeanFinder returned condensed module constructors, finite-presentation predicates and proper-morphism facts; LeanSearch returned underived pushforward/adjunction and properness declarations. The source grep returned constructible sets in Chevalley's theorem, not constructible cohomology. None states this theorem or specializes to it in one line.

I searched the whole DAG and the blueprint for properness, colimits and bounded constructibility, and opened the nearby rational proper-base-change, coefficient-change and constructible-generation statements. Existing Noetherian proper constructibility, uniform bound and bounded heart-amplitude dévissage nodes supply everything needed. No new node, elementary duplicate, clause restatement or Mathlib leaf was invented. I read every cited statement and traversed their statement/proof dependencies: none reaches the item, so these choices introduce no cycle.

## Not duplicates

No new nodes. The two specialized arithmetic inputs are strictly separate existing assertions: constructibility of every output cohomology module, and an upper bound on heart objects in a specified closure. The split carries the bounded-complex assembly and the bounded-below comparison itself; it does not move the item into a new lemma.

## Review by Q43

I read the item's current blueprint statement and proof, the chapter and open-coefficients unit, and Bhatt–Scholze Theorem 6.7.1, Lemma 6.7.2 and Remark 6.8.15 in the local PDF. The proper alternative in 6.7.1 is distinct from its quasi-excellent alternative. The local proof uses the former via the existing Noetherian arithmetic inputs; it does not assume excellence or positive characteristic of the base field. I also read Stacks `derived.tex`, Tags 05TI (`lemma-enough-injectives-right-derived`, part 2) and 05TH (`lemma-injective-acyclic`), and the live bounded-below/unbounded comparison file. There are no new-node sources to check.

For step 1 I verified that the bounded-constructible definition gives a finite cohomological interval and stratified locally finitely presented cohomology, with no completeness condition; the coefficient definition agrees with the current Lean ring object. The derived-pushpull definition specifies the total derived composite on module objects. This step only unfolds those definitions.

For step 2 I read `lem-sfb-noetherian-proper-constructible-cohomology`: its conclusion is literally that every cohomology module of the actual Rp_*K is constructible, and it explicitly allows arbitrary structure map aY and characteristic zero. Its coefficient list includes the finite-subextension-valued algebraic closure with the actual multiplication. K has exactly its required bounded constructible cohomology. I use only this conclusion, not the proof of the cited node, and do not infer a bound from it.

For step 3 I read `lem-sfb-noetherian-proper-heart-uniform-bound`: it gives one integer d on precisely the replete Serre/coproduct closure written in the step. Every H^i(K) is a generator of that closure; zero has an explicit rank-zero finite presentation. I then checked `lem-pc-right-derived-functor-triangulated` supplies both exactness and shift compatibility, and `lem-sfb-bounded-heart-amplitude-devissage` applies to a bounded K with those cohomologies and upper bound b. Its conclusion is b+d. This avoids any unbounded-tail or derived-completeness inference. The triangulated-functor K-injective hypothesis is supplied by the category check in step 4.

For step 4 I checked the sheaf-category node states the Grothendieck property, additive closed symmetric monoidal tensor and exact sheafification, rather than just defining them. The module-object Grothendieck theorem applies to these commutative coefficient objects. The enough-injective and K-injective nodes each state the required existence theorem. The site's smallness is the project's fixed small-site/universe convention, with no large indexing diagram introduced here.

For step 5 I checked `lem-weil-pbc-right-derived-plus-injective` actually has codomain D-plus, and read the full formula in `src-right-derived-functor-plus-compatibility` and the corresponding live declaration. Its additive/enough-injective/K-injective hypotheses are met. The underived module pushforward is additive termwise on maps; the comparison identifies R-plus with this item's total unbounded derived functor, so its lower bound belongs to the correct object. I only claim existence of a lower bound c, which these cited statements give, rather than the stronger assertion of preserving the chosen a.

For step 6 I checked both vanishing inequalities and constructibility against the definition. Taking min(c,b+d) ensures an ordered interval even for zero cohomology. Zero K, empty schemes or fibres, an identity proper map, a one-degree complex and arbitrary integer shifts all satisfy the proof with the same reasoning. No perfection or Tor-amplitude assumption enters. Each proof step is under 1000 characters, so no long inline lemma is hidden.

I checked delivery-errors B–E: self-contained statements and literal TeX are retained; there is no new statement or definition; every non-elementary inference cites a node whose statement supplies it; all sixteen quotes were tested as exact substrings; no citation uses a proof-only construction; no new dependency reaches the item; no node duplicates the conclusion; all scheme and coefficient hypotheses were matched explicitly. The off-unit citations are generic finiteness/category tools and are declared with their individual reasons in `split_report.tool_uses` for the maintainer to judge. No existing node outside the item was edited.

## Unfinished work

None at stage 1 for this item. The cited existing inputs remain separate DAG obligations; this report does not claim a completed Lean proof. No Lean files were written or compiled. Delivery validation and the final delivery commit are reported by the delivery command.
