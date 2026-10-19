# Stage 1 report: lem-sfb-profinite-to-proetale-continuous

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-profinite-to-proetale-continuous.json`: item, statement unchanged, split into three proof steps; no direct Mathlib match for this geometric functor.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-representably-flat-compatible-preserving.json`: new statement-only Mathlib leaf, `CategoryTheory.compatiblePreservingOfFlat`, `Mathlib/CategoryTheory/Sites/CoverPreserving.lean:116–140`.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-cover-compatible-continuous.json`: new statement-only Mathlib leaf, `CategoryTheory.Functor.isContinuous_of_coverPreserving`, `Mathlib/CategoryTheory/Sites/CoverPreserving.lean:160–171`.
- `citations.json`: five verbatim quotes supporting every citation of every proof step.
- `report.md`: current self-review and handoff. `searches.jsonl` preserves actual prescribed search results, including the latest repeated searches.

There are **two new nodes, both Mathlib leaves**. The earlier third leaf, `lem-sfb-finite-limits-representably-flat`, was removed by the preceding second reader because the existing `lem-weil-pbc-presheaf-pullback-sets-left-exact` already states its conclusion in clause (2). It is absent from the delivered files and dependencies.

## Attachments

None. Fresh searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the blueprint id, `isContinuous_profiniteToProEt`, `profiniteToProEt`, and the generic criterion names found no project declaration stating this item. Instances for other geometric functors do not state this one.

The reference-only master declaration `AlgebraicGeometry.ProEtale.isContinuous_profiniteToProEt` at `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Basic.lean:209–212` has a proof using the two generic criteria, but its inputs `preservesFiniteLimits_profiniteToProEt` (197–198) and `coverPreserving_profiniteToProEt` (205–207) contain sorry. It is not attachment evidence.

## WANTED

None.

## What was wrong or incomplete

The imported statement mentioned the functor without a statement dependency; the split adds `def-sfb-profinite-to-proetale`. Its single proof paragraph omitted the general implications from finite limits to flatness, flatness to compatibility, and compatibility plus cover preservation to continuity. The first is supplied by an existing Mathlib leaf; the latter two are the new leaves. The exact compatibility condition is written out, rather than replaced by the weaker informal phrase about images of matching families.

The current shared item has status imported, chapter `sec-proetale-coefficients` and unit `sk-def-sfb-pullback-from-point`. Both chapter and unit JSON records now exist and were read alongside the blueprint `_section.md`; clause 1 gives exactly this route. The earlier report claiming absent metadata is superseded by this fresh reading. The item is not the unit's key definition, so no unit realization record is delivered. No maintainer metadata is changed.

The statement is unchanged, no statement dispute was found, and no coefficient categories are identified. The route uses no SGA source. The Mathlib proof only requires finite completeness of the source category; the blueprint's stronger descriptive phrase about both categories is not needed as an added hypothesis.

The old report mixed superseded three-leaf inventories with later two-leaf repairs and several historical tool-capacity failures. This report replaces that history with the present two-leaf delivery. Earlier successful dry runs preceded the duplicate removal and cannot validate it; the current retry is recorded below.

## What could not be finished

Nothing remains in the one-level mathematical split. The existing geometric finite-limit and cover-preservation statements remain dependencies, as the blueprint requires. Only the prescribed dry-run result below determines READY. This worker does not push; a fresh reader receives the sandbox.

## Not duplicates

- `lem-sfb-representably-flat-compatible-preserving` vs `lem-sfb-profinite-to-proetale-continuous`: the new leaf proves the explicit compatibility condition for an arbitrary flat functor and target topology; it supplies no cover-preservation or geometric continuity conclusion.
- `lem-sfb-cover-compatible-continuous` vs `lem-sfb-profinite-to-proetale-continuous`: the new leaf is the general criterion with two hypotheses; it supplies neither hypothesis for the geometric functor. Steps 1–2 and the existing geometric covering lemma establish them.
- `lem-sfb-cover-compatible-continuous` vs `lem-weil-pbc-site-continuous-pushforward-sheaf`: the existing node assumes Stacks family-site continuity, including preservation of covering pullbacks. The new leaf instead assumes the explicit Grothendieck-sieve cover-preservation and compatibility conditions and concludes continuity.
- `lem-sfb-cover-compatible-continuous` vs `lem-weil-pbc-etale-base-change-continuous`: the existing statement is specific to etale base change, not a general compatibility criterion.
- `lem-sfb-cover-compatible-continuous` vs `lem-weil-pbc-site-equivalence-is-morphism-of-sites`: the existing statement assumes an equivalence preserving coverings in both directions; the new criterion assumes no equivalence, fullness or faithfulness.

Whole-DAG statement searches for representable flatness, compatibility, covering and continuity, together with whole-blueprint searches using `tools/blueprint_refs.py search`, found no replacement for the remaining two leaves. The overlapping statements above were opened and read. The more general geometric `lem-weil-pbc-profinite-test-object-functor` supplies geometric preservation properties already available through this unit's two named dependencies; it does not state either new criterion. The ancestor command identifies this item itself as the blueprint ancestor. Both new leaves have precise source sentences and `same_as: []`; the item's list is also empty. The broad search for compatible objects returned unrelated statements, not a generic compatibility criterion.

## Review by NA

I reread delivery-errors B–E, the stage-1 brief, SETUP's three blueprint levels, GOAL and dag-sync. For sources I opened the current blueprint item and its separate proof file, clause 1 of the pullback-from-point unit, and the chapter record. For each new leaf I read its source sentence and its full Mathlib declaration, including the definitions on which its signature depends. I also read Stacks `sites.tex`, Tag 00X3 (`lemma-directed`, lines 452 onward) and Tags 00WV/00WW (`definition-continuous` and `lemma-pushforward-sheaf`, lines 2524/2548 onward). The latter family-site lemma is an analogue of the final step, not a substitute for the recorded Mathlib compatibility predicate.

Step 1 uses the entire sentence of `lem-sfb-profinite-to-proetale-finite-limits` and clause (2) of `lem-weil-pbc-presheaf-pullback-sets-left-exact`. I opened both statements: the first gives finite-limit preservation for precisely u, and the second defines I_Y with objects (S, Y → u(S)) and morphisms a satisfying u(a)φ = φ′, then asserts filteredness of I_Y opposite under the required preservation hypothesis. This is exactly the structured-arrow category used in the next step. A common larger universe contains the source and target object/morphism sets. No colimit assertion is used. `Profinite.hasLimits` at `Topology/Category/Profinite/Basic.lean:217–218` supplies the inferred finite-limit instance (B8). I also read `flat_of_preservesFiniteLimits` at `Functor/Flat.lean:163–169` and RepresentablyFlat at 70–71 to check this interpretation. No finite-completeness assumption on the target is needed. The existing leaf is a generic tool from another unit and is permitted as a Mathlib leaf.

Step 2 uses `lem-sfb-representably-flat-compatible-preserving`. I read `CompatiblePreserving` at `Sites/CoverPreserving.lean:78–86` and `compatiblePreservingOfFlat` at 116–140. The leaf and theorem have the same arbitrary target topology, presieve, matching family, common target-side domain w, commuting-square equality and restricted-section equality. Cofilteredness from step 1 is exactly its flatness hypothesis. The theorem works for every set universe and thus supplies the universe required in step 3. Nothing about compatible families is extracted merely from a definition node.

Step 3 uses the complete explicit cover-preservation conclusion of `lem-sfb-profinite-to-proetale-cover-preserving` and `lem-sfb-cover-compatible-continuous`. I opened both statements. The source is profinite sets with the coherent topology, the target is the weakly etale/fpqc small pro-etale site from `def-weil-pbc-proetale-site`, and the latter's blueprint_update does not change these site data. I checked CoverPreserving at `CoverPreserving.lean:58–59`, the criterion at 160–171, and IsContinuous at `Continuous.lean:193–198`. The compatibility hypothesis must hold at the maximum object/morphism universe; step 2 supplies it. The conclusion is preservation of set-valued sheaves under restriction, so substituting u(S) from the defining-functor statement gives exactly the displayed presheaf. No additional sheaf comparison or coefficient-category theorem is hidden here.

B1–B10: the two leaves are self-contained, statement-only, with no proof steps/dependencies or sketches, single TeX escaping, explicit nonstandard terminology, correct blueprint origins, and exact declarations/files/lines. The generic leaves introduce their categories, topologies and functor directly; application-specific site/functor references were removed. Their sole stmt_dep is now def-weil-pbc-sites-and-cohomology, cited only for its clause (1) convention that set-valued presheaves are contravariant functors to sets; no family-site continuity predicate is imported. The application uses the existing defining-functor dependency of the item. The matching-family and sieve constructions are standard category-theoretic notions and their needed conditions are spelled out. Actual msearch.py records support every recorded query; the retained queries include two phrasings, semantic, Loogle and grep searches. Fresh grep/Loogle/LeanFinder calls reconfirmed the matches. Semantic results with older universe signatures were checked against the pinned source, not accepted without reading it.

C1–C8 and D1–D5: every non-elementary implication is a cited statement. I checked all five citation quotes against the exact current statements; they are verbatim passages. proof_deps is exactly their union. The only identifications supplied in the proof are the written object/morphism identification of I_Y with the comma category and substitution of u(S). The two generic criteria do not restate the geometric conclusion or supply either geometric input. The removed flatness leaf stays removed. The reachable overlay contains 135 nodes with no missing/merged dependency or cycle. No off-unit non-Mathlib theorem replaces the unit's route.

E1–E7: the hypotheses were checked at each application above. Identity functors satisfy the generic assertions. For terminal categories the compatibility equation is the unique-arrow equation. An empty source is excluded by step 1's finite-limit hypothesis; an empty target makes representable flatness vacuous. Empty covers are allowed: the sheaf hypothesis then forces the unique section, so the continuity criterion needs no nonempty-cover assumption. For the geometric functor, S empty gives the zero ring and empty spectrum, a singleton gives Spec Z, and a finite discrete S gives its finite coproducts. No connectedness, nonempty-object or individually-surjective-map hypothesis was added. I found no source error or statement dispute.

## Earlier second reading (a previous round; superseded)

The preceding fresh reader had removed the duplicate flatness leaf and rewritten step 1 to use clause (2) of the existing presheaf-pullback leaf. This retry rechecked that repaired argument and both remaining leaves directly, retained the three node files and five citations unchanged, refreshed actual searches, and replaced the stale report inventory. There is still no push: the dispatcher brief for this worker requires handing the accepted sandbox to another reader.

## Required dry run

The final sandbox is submitted to `python3 /home/ubuntu/weil-launcher-nt/deliver.py NA lem-sfb-profinite-to-proetale-continuous --no-push`. Its actual output is captured in `dry-run.log`. Earlier failures were terminations before preflight and do not constitute current preflight results. No Lean files, compiler, live project, live launcher, lock, or other process has been changed.

### Retry attempt 1 on this reading

The normal command acquired the NA group lock and worktree slot 17, then waited on `weil-newtargets.fetch.lock` (read-only `/proc/locks` inspection). It was killed externally with exit 137 after about four minutes, before preflight and without output in `dry-run.log`. I sent no termination signal. This is a tool/infrastructure failure, not a preflight rejection. The unchanged mathematical overlay is being retried with the same prescribed command; nothing was pushed.

## Earlier second reading (a previous round; superseded)

- Step 1 checked against the blueprint proof, `lem-sfb-profinite-to-proetale-finite-limits`, `lem-weil-pbc-presheaf-pullback-sets-left-exact`, and Mathlib's finite-limit instance; verdict: the structured-arrow identification and cofilteredness use exactly the cited clauses.
- Step 2 checked against `lem-sfb-representably-flat-compatible-preserving` and Mathlib `compatiblePreservingOfFlat` (`CoverPreserving.lean:116–140`); verdict: the explicit compatibility hypotheses and universe quantification match.
- Step 3 checked against `lem-sfb-profinite-to-proetale-cover-preserving`, `lem-sfb-cover-compatible-continuous`, and Mathlib `isContinuous_of_coverPreserving` (`CoverPreserving.lean:160–171`); verdict: cover preservation plus compatibility yields precisely the stated sheaf restriction.
- `lem-sfb-representably-flat-compatible-preserving` checked as a self-contained exact Mathlib leaf with explicit representable-flat and compatibility definitions; verdict: sound and non-duplicate.
- `lem-sfb-cover-compatible-continuous` checked as a self-contained exact Mathlib leaf with explicit cover-preserving, compatibility-preserving, and continuity conclusions; verdict: sound and non-duplicate.
- Removed the proof-sketch application sentences from both new leaf statements because B1 requires statement-only nodes. This fresh retry also removes the residual application-convention sentences and their unused stmt_deps: the generic assertions are self-contained, with the generic presheaf convention explicitly cited from clause (1) of def-weil-pbc-sites-and-cohomology. Application data remain in the item proof and its defining-functor dependency.
- Rechecked zero/terminal and finite discrete profinite cases, empty and terminal sites, and the absence of coefficient-category identifications; no statement dispute or source error found.
- The prescribed dry run reports `OK (not pushed) ... preflight passed` after this repair; no Lean compiler or Lake command was run.

## Fresh retry review (2026-10-16)

Reopened every cited statement and the pinned Mathlib source. The first step uses only clause (2) of the existing left-exact pullback leaf, identifying its I_Y and its morphism equation explicitly with the structured-arrow category; no property is borrowed from a proof. The Profinite finite-limit instance supplies its remaining hypothesis. The second and third steps match the exact compatibility and covering predicates in CoverPreserving.lean. Empty profinite sets, terminal categories and arbitrary presieves do not need new hypotheses. The unit and chapter records now exist and confirm the original route. The two leaf statements no longer refer to special application conventions; this also corrects the flatness leaf's former reference to a functor-definition node absent from its stmt_deps. No mathematical conclusion or citation quote changed. The command syntax supported by deliver.py is `... --no-push` without a trailing dot. A fresh final dry run follows this cleanup; no push is requested.

The first fresh dry run passed at 3c858a077e. The cleanup dry run then rejected both new leaves because they cited no definition node. I repaired this by citing only the presheaf convention from clause (1) of `def-weil-pbc-sites-and-cohomology`, whose statement I opened: a set-valued presheaf is a contravariant functor to sets. The source and target are still arbitrary Grothendieck topologies, and both continuity and compatible-preservation are still defined by the explicit predicates in these leaves; in particular clause (3)'s different family-site continuity is not used. This is a definition citation, not an additional mathematical hypothesis or a theorem taken from a proof. The two Mathlib matches and all five citation quotes remain exact. The final rerun is captured in dry-run.log.

## Second reading by NA

- Step 1 checked against the current blueprint proof, `lem-sfb-profinite-to-proetale-finite-limits`, `lem-weil-pbc-presheaf-pullback-sets-left-exact` clause (2), and `Profinite.hasLimits`; verdict: the finite-limit hypothesis and the structured-arrow/cofiltered identification match exactly, with no colimit conclusion used.
- Step 2 checked against `lem-sfb-representably-flat-compatible-preserving` and Mathlib `compatiblePreservingOfFlat` (`CoverPreserving.lean:116–140`); verdict: all presieve, family, commuting-square, and universe conditions are present and applied under representable flatness.
- Step 3 checked against `lem-sfb-profinite-to-proetale-cover-preserving`, `lem-sfb-cover-compatible-continuous`, and Mathlib `Functor.isContinuous_of_coverPreserving` (`CoverPreserving.lean:160–171`); verdict: the coherent and pro-étale site hypotheses yield exactly the stated sheaf restriction.
- New node `lem-sfb-representably-flat-compatible-preserving` checked against the exact Mathlib declaration and definitions at `CoverPreserving.lean:78–86,116–140`; verdict: self-contained statement-only Mathlib leaf, with the presheaf convention cited and no duplicate found.
- New node `lem-sfb-cover-compatible-continuous` checked against the exact Mathlib declaration and definitions at `CoverPreserving.lean:58–59,81–86,160–171` and `Continuous.lean:193–198`; verdict: self-contained statement-only Mathlib leaf, with the presheaf convention cited and no duplicate found.
- Edge cases checked: terminal and empty categories, the empty profinite set, singleton and finite discrete profinite sets, terminal/empty covers, and arbitrary presieves; verdict: no extra nonemptiness, connectedness, or coefficient hypotheses are required.
- Changes made: no mathematical statements or citations changed; this section records the second-reader checks required by the delivery contract. The prior duplicate flatness leaf remains removed, and both retained leaves remain exact Mathlib matches.
