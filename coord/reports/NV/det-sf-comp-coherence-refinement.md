# Stage-1 report: det-sf-comp-coherence-refinement

## Files written

- `dag/nodes/sec-six-functors-basics/det-sf-comp-coherence-refinement.json`: nine-step split; no new nodes and no Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each of the 26 step/citation pairs.
- `searches.jsonl`: the search wrapper's genuine log. `prepare.py` is historical scratch from the previous attempt, not a project delivery file; do not regenerate from it, because the node and stable quotations were subsequently repaired directly.

## Attachments

None. I searched the project source for the exact blueprint tag and for the refinement comparison. `WeilConjectures/SixFunctors/Etale/Derived/LowerShriekCoherence.lean` has `AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekComparison` and its identity/composition declarations, but these are on bounded-below étale derived categories. Its torsion-coefficient isomorphism result does not provide the unbounded pro-étale module-object theorem for every admissible coefficient and its ambient localizing closure. It is not an attachment to this item. The upstream master's sorry declarations were not counted as proofs.

## WANTED

None.

## Source error

STATEMENT-DISPUTED: the imported standalone statement suppresses the standing scheme setting required by the proper-base-change assertions used in its own current blueprint proof. The failing application is concrete: the literal imported hypotheses permit the identity compactification of `Spec Z` with finite coefficients of characteristic ell; none of the three cited coefficient proper-base-change statements accepts this input as a standing scheme over a field of characteristic different from ell. This is a missing-context/type-of-theorem-application objection, not a claimed counterexample to the refinement identity. I restored explicitly the setting of `sk-def-sfb-dc-setting` (separated finite-type k-schemes, k of characteristic p>0 different from ell) and the coefficient/module-category meaning of `sk-def-localizing-closure`. The sibling `det-sf-comp-coherence-single` now has this same explicit setting. It implies the qcqs hypotheses needed for that sibling. No target statement in Challenge or Lean was edited.

All original conclusions remain: existence and uniqueness and the identity/composition formula for arbitrary unbounded K, and isomorphism for the full ambient localizing closure, with no derived-completeness restriction on that closure. I made the unit and canonical composition identifications explicit. The item is not weakened to finite coefficients, classical origin, or bounded-below K.

The unit record `dag/units/sk-prop-sf-comp-coherence.json` still describes the older master finite-étale-origin proof in the smooth-purity chapter. I followed the supplied current `main-20261015` unit statement and proof in `sec-six-functors-basics/sk-prop-sf-comp-coherence/`, whose route is extension by zero/proper image, generators, proper base change at the closed complement, localizing determination, and uniqueness. This item is not the unit's key statement; the stale unit record was left untouched.

## Changes and searches

I read the chapter and unit, the current target `.md` and `.proof.md`, and the current unit proof. Their directory is `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-comp-coherence/`. The imported proof left the all-coefficient proper-base-change assertion and several exact/derived operations uncited. The finite étale-origin comparison it mentioned is only a parenthetical illustration; it cannot prove the all-coefficient assertion. I use the existing finite, integral and rational base-change nodes instead. An early sandbox candidate used `det-sf-comp-composition-base-change`; I removed it because its dependencies return to this coherence item. The final dependency closure has no path back to the item.

I searched the whole DAG and blueprint for refinement/comparison and the required generic ingredients, including `tools/blueprint_refs.py search refinement`, and reused existing nodes throughout. There is no new assertion moved into a child node, no new definition, and no duplicate-node pair to justify. The item's imported blueprint identity is preserved; `from` stays null and `same_as` is empty because the nearby finite étale comparisons do not state this theorem.

Mathlib searches used only the supplied wrapper. LeanFinder's first query returned underived pushforward composition and natural-isomorphism declarations; its second phrasing returned complex shape-extension identities and a scalar-congruence formula. LeanSearch returned geometric open/proper base-change properties. None provides this derived refinement theorem. Loogle's first pattern was invalid (`IsIso` unresolved), so I recorded that error and followed it with the successful `"lowerShriek"` substring query (no hits). Some first grep subdirectories accidentally included a duplicated `Mathlib/` prefix; these are expressly marked invalid evidence. Corrected searches in `CategoryTheory` and `Algebra/Category/ModuleCat/Sheaf` were then run. The latter found `SheafOfModules.pushforwardComp` at `Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:139`, and I read lines 110–180: it is the underived composition isomorphism, with sectionwise identity formulas, not the target's refinement or derived-support theorem. The actual query strings, results and errors are retained without inventing searches.

## Review by NV

I checked delivery-errors B–E against the final files. No new nodes are introduced, so B's new-node and Mathlib-leaf requirements have no new instances. The original blueprint fields and import flags are retained. The statement spells out the setting, rings, categories, compactifications, refinement, unit and canonical map; its definition dependencies name those notions, rather than an unrelated meaning of “admissible”. In particular, the exceptional-adjoint admissibility definition is not used to define coefficients.

For step 1 I read the statements of `lem-sfb-alpha-iso`, `lem-weil-pbc-proetale-immersion-limit-preservation`, `lem-weil-pbc-proetale-ringed-open-closed`, `sk-def-sfb-module-lower-shriek`, `lem-weil-pbc-termwise-adjunction-homotopy`, and `lem-weil-pbc-exact-functor-derived-functor`. They supply respectively cartesian coefficients, exact identified module inverse images, the actual open adjunction/unit/support vanishing, the matching linearized extension-by-zero definition, the complex/homotopy adjunction, and termwise derived exact functors. I checked the generic ringed statements allow a sheaf of rings, not merely a discrete constant coefficient. The descent argument writes the unit, counit and triangle identities; it does not cite a definition for the theorem that adjunction descends.

For step 2 I read `prop-pur-kinjective-resolutions-exist` (functorial resolutions on small ringed sites), `sk-def-sfb-module-derived-pushpull` (the derived functor of the whole module pushforward), `lem-weil-proetale-weakly-etale-localization` clause (1) (the actual open slice-site equivalence), both `def-sfb-finite-lower-star` and `def-sfb-module-lower-star` (sectionwise direct image and scalar action), and `lem-weil-pbc-right-adjoint-preserves-kinjective` (exact left adjoint). All are used with the fixed small-skeleton universe. I use localization clause (1), not its later discrete-constant-ring clause for a non-discrete ring. The equation at V over X uses the cartesian refinement condition. It constructs restriction for all unbounded complexes directly, and does not misuse proper base change on all unbounded objects.

Step 3 is the explicit adjunction bijection, plus naturality and the shift calculation from the previous two steps. Its argument proves the uniqueness clause; no child node simply restates that clause. The two maps in the naturality square have the same stated adjoint. Shift compatibility, required by localizing determination, is included.

For step 4 I read `lem-weil-pbc-qc-open-immersion-finite-type`, `det-sf-comp-coherence-single`, and `sk-def-localizing-closure`. The first justifies the finite-type hypothesis; the open diagonal is an isomorphism, hence closed, giving separatedness. The two compactifications are of the morphism j over Z, not mistakenly of f over Y. Both Z and Z' are standing schemes and hence qcqs. The second application, to j' over Z', gives generator preservation; the ambient sums are precisely the sums in the definition of Loc. No unsupported assertion that a proper direct image preserves every unbounded coproduct is used.

For step 5 I read all three `det-thm-sfb-proper-base-change-{finite,integral,rational}` statements and their current blueprint statement/proof files in `sk-thm-sfb-proper-base-change/`. Finite clause (2) takes Dctf, integral clause (3) takes Dbc, and rational clause (3) takes Dbc. The statement of `det-def-sfb-constructible-tor-amplitude` really gives Dctf contained in Dbc, so the latter hypotheses follow for L=j'_!K. I checked Z_l and Q_l by E=Q_l, rather than leaving two coefficient cases implicit. `lem-weil-pbc-proper-fp-permanence` gives the proper base change, and the open-closed node really states the required vanishing. B' is the scheme-theoretic fibre product, not a falsely asserted factorization from a set-theoretic image. Its complementary open is X, and all four schemes in the base-change square are in the stated scheme setting. No projection-formula clause is used.

For step 6 I read `lem-exc-open-closed-detection`: it is a theorem for module sheaves with inverse-image ring identifications. I apply it only to the cohomology sheaves of the cone, using exact inverse images from step 1. The resulting acyclic cone is zero by the definition of the derived category. For step 7 I read `det-sf-determination-localizing`: it requires exact functors preserving ambient sums and a shift-compatible natural transformation. Steps 3–4 verify these hypotheses, and step 6 verifies every generator.

For step 8 I read the full statement of `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, especially its normalization by a K-injective resolution v of a_*I, and the composition isomorphisms in `sk-def-sfb-module-pushforward-pullback`. I also read Stacks `sites-cohomology.tex`, Tag 0D6E, `lemma-derived-pushforward-composition`. The proof explicitly restricts h_*v to j'^*v and cancels this same resolution map against the inverse used in restriction. Thus the canonical comparison becomes identity on X; an unspecified choice of functor isomorphism is not substituted. Step 9 checks properness of the composite with the permanence node, verifies its inverse-image and triangle identities, and applies the already proved uniqueness. This is the transitivity argument itself.

I read the relevant Stacks source passages in `proetale.tex`, Tag 09AH, `lemma-ses-associated-to-open`, and the preceding open unit lemma (09BN); in `derived.tex`, Tags 08BJ (`lemma-adjoint-preserve-K-injectives`), 070I (`lemma-K-injective`), and the cited exact-functor framework; and the current blueprint files listed above. These corroborate the node statements used. No SGA route is invoked. All non-elementary inputs are existing cited nodes, with off-unit generic uses declared in `split_report.tool_uses`; definitions remain definitions.

I checked the zero complex and identity refinement, and composition when either refinement is identity. If X is empty, density forces the compactifications empty; the conclusions reduce to zero objects and their unique maps. If the closed complement is empty, the generator argument reduces to the invertible open unit. Nothing in the proof requires a uniform cohomological bound for arbitrary K. The coefficient categories are the same module-object categories in every application. Each quotation in `citations.json` is copied directly from the current cited node's statement, including its hypotheses. The dependency lists are the unions of the actual proof-step uses. No Lean file was written and no compiler was invoked.

## What could not be finished

No mathematical subtask remains for this stage-1 split. The required delivery dry run must accept this sandbox before READY is reported. During this continuation I re-opened every cited node statement and the current blueprint unit and proof; I made the closed-complement standing-scheme check explicit. Additional genuine wrapper searches are recorded verbatim in the node and searches.jsonl, including an invalid Derived-name Loogle pattern with no absence conclusion. The mandated syntax with a trailing dot is rejected by this installed deliver.py; its documented two-positional-argument syntax is used thereafter. Earlier attempts waited on the shared group/fetch locks and timed out without reporting a content failure. The second reader is to repair and deliver; this worker does not push.

## Not duplicates

No new nodes.

## Dry-run repair

The first completed citation check found that the upstream module lower-shriek statement had changed two contextual phrases. I reread its updated live statement and kept its unchanged extension-by-zero clause, including exactness and the open adjunction, as the verbatim quotation for step 1. This is exactly the portion used; no mathematical claim or dependency changed.

## Validation blocked by launcher

After the stale quotation repair, the required rerun again waited on the shared launcher fetch lock (the delivery process was in locks_lock_inode_wait, holding deliver-NV.lock and a worktree slot). It produced no preflight output or OK for more than ten minutes; earlier runs also timed out before preflight. The installed command rejects the brief's trailing dot, so documented GROUP ITEM --no-push syntax was used. No delivery was pushed. The repaired sandbox needs a successful tool rerun before it can be marked READY; dry-run.log records the actual outcomes.

## Continuation audit

I rechecked all 26 step/citation pairs against the shared DAG on 2026-10-16; each is a verbatim statement passage. I also reopened the current unit proof `sk-prop-sf-comp-coherence.proof.md`, the source statements and proofs `sk-thm-sfb-proper-base-change-{finite,integral,rational}.md` and their `.proof.md` companions, Stacks Tag 09AH (proetale.tex, lemma-ses-associated-to-open), Tag 08BJ (derived.tex, lemma-adjoint-preserve-K-injectives), and Tag 0D6E (sites-cohomology.tex, lemma-derived-pushforward-composition). The finite, integral and rational citations are used only for their base-change clauses; their projection formulas are not needed. The closed complement is a genuine scheme-theoretic fibre product, and its open complement is X.

Four further actual wrapper searches were run and their exact query strings were added to the item. The successful Loogle pushforwardComp search confirms the earlier candidates are underived; I read SheafOfModules.pushforwardComp and its component formulas at PushforwardContinuous.lean:139–152. LeanFinder returned condensed Kan extensions and shape-extension formulas; LeanSearch returned compactly supported function and zero-object facts. The module-sheaf grep found no refinement or lowerShriek declaration. None states this item.

The exact blueprint-id search under the slopmaster2 project source found no declaration. LowerShriekCoherence.lean:231 is a bounded-below étale, discrete torsion-coefficient isomorphism and is not an attachment. The final proof dependency union equals the union of step uses. A transitive DAG scan also encountered the inherited missing id def-weil-pbc-etale-morphism; no delivered citation names it. The delivery preflight must judge inherited findings against its baseline.

## Second reading by NV

- Item node: checked the current blueprint statement, [sk-def-sfb-dc-setting], [sk-def-localizing-closure], and [sk-def-nagata-sketch-data]; the explicit standing scheme/coefficient context and all three clauses agree, including arbitrary unbounded (K).
- Step 1: checked each of the six cited node statements; exact inverse image, open adjunction/unit/vanishing, and termwise derived adjunction are all stated under the hypotheses used.
- Step 2: checked the K-injective, localization, lower-star, coefficient-action, and K-injective preservation statements; the sectionwise restriction calculation uses (h^{-1}(X)=j'(X)) and does not invoke proper base change for unbounded complexes.
- Step 3: checked the adjunction and restriction isomorphism from steps 1–2; the Hom-bijection proves existence, uniqueness, naturality, and shift compatibility in a few direct lines.
- Step 4: checked [lem-weil-pbc-qc-open-immersion-finite-type], [det-sf-comp-coherence-single], and [sk-def-localizing-closure]; both compactification functors have the required exactness, coproduct preservation, and generator preservation into the ambient target.
- Step 5: checked the closed-complement fibre product and all three proper-base-change statements; (B,B') are standing schemes, (h_B) is proper, (i'^*j'_!K=0), and each coefficient case has the required (Dctf/Dbc) hypothesis.
- Step 6: checked [lem-exc-open-closed-detection] and exactness from step 1; vanishing of both inverse images of every cohomology sheaf correctly implies the cone is zero.
- Step 7: checked [det-sf-determination-localizing]; step 3 supplies shift compatibility, step 4 supplies exact sum-preserving functors, and step 6 supplies the generator isomorphisms.
- Step 8: checked [lem-weil-pbc-ringed-topoi-derived-pushforward-composition] and [sk-def-sfb-module-pushforward-pullback], including the K-injective-resolution normalization; restriction of the canonical comparison is the identity via the same resolution map.
- Step 9: checked properness and refinement identities for composites and the uniqueness argument; identity and transitivity hold for every unbounded (K) under the canonical comparison.
- New nodes: none; no unsplit or Mathlib leaf requires review.
- Sources and edge cases: reread Stacks Tag 09AH in `proetale.tex`, Tags 08BJ and 070I in `derived.tex`, Tag 0D6E in `sites-cohomology.tex`, and the current blueprint proof; tested zero/empty objects, identity refinements, and empty complements.

No mathematical or citation repair was needed in this second reading. The worker's standing-context correction, dependency expansion, exact quotations, and search log were retained; only this review section records the independent audit.
