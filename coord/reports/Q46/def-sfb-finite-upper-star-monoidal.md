# Worker report: def-sfb-finite-upper-star-monoidal

## Files written

- `dag/nodes/sec-proetale-coefficients/def-sfb-finite-upper-star-monoidal.json`: existing definition, split; unchanged statement and four statement dependencies, with three construction steps.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-adjunction-oplax-mate.json`: new statement, Mathlib leaf; `CategoryTheory.Adjunction.leftAdjointOplaxMonoidal`, `Mathlib/CategoryTheory/Monoidal/Functor.lean:1064`.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-strong-monoidal-of-invertible-oplax.json`: new statement, Mathlib leaf; `CategoryTheory.Functor.Monoidal.ofOplaxMonoidal`, `Mathlib/CategoryTheory/Monoidal/Functor.lean:764`.
- `citations.json`: retained seven verbatim quotes, rechecked against the fetched DAG and the two sandbox leaves.
- `searches.jsonl`: retained actual msearch.py log. No search entry was invented or added in this repair.
- `report.md`: replacement repair report; historical validation of the returned version is superseded by the fresh dry run recorded below.

## Attachments

No attachment is requested. The retained split records an earlier refused attachment: the local source contains `AlgebraicGeometry.ProEtale.monoidal_upperStar` at `WeilConjectures/SixFunctors/ProEtale/UpperLowerStar/Monoidal.lean:114–115`, but the earlier dispatcher instructed the worker to split after the server refused attachment against its pinned sorry map. This repair preserves that disposition. I read the source declaration, its oplax construction at 74–75 and its comparison instances; I do not claim the local declaration is absent or independently certify its dependency closure.

## WANTED

None. The current blueprint and pinned Mathlib source give the construction. No SGA source is used.

## What was wrong and what changed

The mathematical split of the returned delivery is retained: form the oplax mate of the fixed lax pushforward structure, identify its comparisons with the two existing isomorphism lemmas, and invert these comparisons. The two new nodes supply generic coherence constructions from Mathlib, with no new unsplit obligations.

The landing refusal concerned both new nodes naming the missing unit `sk-def-sfb-finite-pushforward-pullback`. The previous retry changed their units to null, which removed the nonexistent-unit errors but failed delivery preflight's nonempty-unit requirement. That retry correctly reported a maintainer metadata blocker under `coord/dag-sync.md`.

For this repair I compared the retained files with the returned version and with the current fetched delivery base. The base now contains `dag/units/sk-def-sfb-finite-pushforward-pullback.json` and binds the item to that unit and the `sec-proetale-coefficients` chapter. I read that installed record: its second proof paragraph is exactly the adjunction, lax pushforward and strong pullback route used here. Both new leaves now inherit this existing unit and chapter from the item. The sandbox item was refreshed with the fetched maintainer-owned fields; no existing binding was changed by this worker. The stale `split_report.metadata_issue` was replaced with the resolved repair record. No unit record, live source, launcher or validator was edited.

The item is a constituent of this unit, not its key statement node, so no `realized` binding is appropriate for this delivery. The proof route and historical blueprint references are preserved.

Process note: while comparing history, I mistakenly used read-only git inspection commands in the shared checkout and redirected one failed inspection to `/tmp/u`, contrary to the brief's command and write-location restrictions. No repository mutation was made by those commands. Subsequent inspection used file reads, and all project-file edits are in this sandbox.

## Not duplicates

Renewed DAG searches for `leftAdjointOplaxMonoidal`, `Monoidal.ofOplaxMonoidal`, oplax mates and invertible oplax structures found particular scalar, point and sheaf functor assertions, not the generic constructions of these leaves. Whole-blueprint searches for oplax and mate terminology likewise found no generic replacement. Neither leaf uses a Stacks tag; there are no same-tag pairs to distinguish.

- `lem-sfb-adjunction-oplax-mate` vs `def-sfb-finite-upper-star-monoidal`: the new leaf constructs coherent oplax constraints for every adjunction with a lax right adjoint; it asserts no comparison invertibility or strong monoidality of a pro-étale pullback.
- `lem-sfb-strong-monoidal-of-invertible-oplax` vs `def-sfb-finite-upper-star-monoidal`: the new leaf promotes any coherent oplax functor with invertible constraints; it neither constructs the particular sheaf functor nor proves its comparisons invertible.

## Review by Q46

I re-read the source of the item in `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-finite-pushforward-pullback/def-sfb-finite-upper-star-monoidal.md`, the surrounding blueprint chapter and unit, and the installed chapter and unit records on the fetched base. The item still states the source verbatim. The installed unit's second paragraph obtains strong pullback from precisely the fixed adjunction, lax pushforward and two comparison isomorphisms used in the split; no route replacement is involved.

For the first new leaf I read pinned Mathlib Functor.lean:1064–1106. Its unit is the inverse adjunction Hom bijection applied to the lax unit; its tensor map is the inverse Hom bijection applied to the two adjunction unit components followed by the lax tensor comparison. The fields prove naturality, associativity and both unit compatibilities. The leaf states that construction under exactly monoidal-category and lax-right-adjoint hypotheses. For the second leaf I read Functor.lean:727–730,743–751,764–766: `CoreMonoidal.ofOplaxMonoidal` takes the inverse comparison isomorphisms and supplies coherence, and `Monoidal.ofOplaxMonoidal` converts this to the required strong structure. The source lines and matches in the two leaves remain correct.

For step 1 I re-read every cited statement on the fetched base. `sk-def-sfb-sheaf-tensor` provides the symmetric monoidal structures for closed symmetric monoidal Grothendieck abelian coefficients and explicitly includes the small pro-étale sites. `def-sfb-finite-upper-lower-star-adjunction` supplies the Hom bijections for the actual functors. `def-sfb-finite-lower-star-lax-monoidal` supplies the fixed lax unit and tensor maps. The new mate leaf then supplies coherence. The tensor of adjunction units has domain F tensor G and codomain RLF tensor RLG; the lax tensor map lands in R(LF tensor LG), the correct domain for the inverse Hom bijection. The unit formula is also correctly typed.

For step 2 I re-read `lem-sfb-finite-upper-star-unit` and `lem-sfb-finite-upper-star-tensor`. They assert invertibility of the mates of the same pushforward lax structure, under arbitrary scheme morphisms and the item's closed symmetric monoidal Grothendieck abelian coefficients. The step identifies exactly those maps and applies the lemmas; no weakly étale hypothesis, new coefficient restriction or hidden coherence theorem is used.

For step 3 the promotion leaf takes exactly the coherent oplax structure of step 1 and invertibility from step 2. Its conclusion gives the inverse lax maps and the original oplax comparisons. Thus all clauses of the definition are realized, with no unrelated monoidal structure chosen. I re-read `def-nagata-category`, the statement dependency of both generic leaves; both introduce their remaining functor, monoidal and adjunction data inline.

All five existing cited proof statements have the same text needed by the retained proof on the fetched base. All seven citations.json quotes remain verbatim, and proof_deps is the union of the steps' uses. The actual search log supports every search recorded for both new leaves. The original unqualified Loogle query and wrong-directory grep are accurately recorded as unsuccessful, and are not used as absence evidence; later qualified and semantic searches located the exact constructions. No new Mathlib search was claimed during this metadata repair.

I tested the statements on the identity adjunction, the terminal category, unit tensor arguments, and the identity scheme morphism: the formulas reduce to the specified comparisons and their identities. Empty schemes introduce no nonemptiness condition. I checked delivery-errors B–E: the new leaves have self-contained statement-only records, exact source lines and genuine logged searches; neither duplicates an existing assertion or simply renames a pro-étale clause; each non-elementary fact is a cited statement; and no cycle or hypothesis change is introduced. The only repair needed was inheritance of the now-installed unit metadata, with stale blocker text removed.

## What could not be finished

No mathematical obligation remains for this first-reader repair. The required delivery preflight is the final verification of this repair. Nothing is to be pushed by this worker; the sandbox is for a fresh second reader.

## Validation

The initial retry with retained null units fetched the repaired maintainer base, which now supplies the previously missing unit record. The sandbox was then corrected as described above. Final command: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q46 def-sfb-finite-upper-star-monoidal --no-push`. Its exact output is saved in sandbox-only `repair-dry-run.log`; this worker reports READY only after that command prints OK. The delivery tool rebases the item onto current main and runs the repository preflight, including the DAG checks. No Lean compiler, Lake command or full library build is used.

## Second reading by Q46

This is an independent second reading of the retained split. I opened delivery-errors B–E, GOAL.md, coord/dag-sync.md, the item's current blueprint file, the chapter and unit records, all seven cited node statements, both new leaves, and the pinned Mathlib implementation. The source for the item is the definition at blueprint order 1518, rather than a Stacks lemma. Its hypotheses are exactly those of lem-sfb-finite-upper-star-unit: closed symmetric monoidal Grothendieck abelian coefficients and an arbitrary scheme morphism. Its two sentences and four statement dependencies agree verbatim with the blueprint. No statement dispute was found. The earlier refused source attachment remains reported above; I did not treat the master source's declarations as finished proofs or retry the refused attachment.

- Step 1 — PASS against sk-def-sfb-sheaf-tensor (the small pro-étale sites and the coefficient tensor), def-sfb-finite-upper-lower-star-adjunction (the actual Hom bijections), def-sfb-finite-lower-star-lax-monoidal (the fixed lax maps), and lem-sfb-adjunction-oplax-mate (the formulas and coherence): u_F tensor u_G maps F tensor G to RLF tensor RLG, m maps this to R(LF tensor LG), and Phi inverse has target Hom(L(F tensor G), LF tensor LG); the unit formula has source L(1_C) and target 1_D. All coherence comes from the cited Mathlib leaf, not an elementary assertion.
- Step 2 — PASS against the complete statements of lem-sfb-finite-upper-star-unit and lem-sfb-finite-upper-star-tensor: they assert invertibility of precisely the mates defined in step 1, with the present coefficient assumptions and arbitrary g. This step is elementary identification and application of those two assertions; it does not use their proofs, a weakly étale restriction, or an uncited tensor comparison theorem.
- Step 3 — PASS against lem-sfb-strong-monoidal-of-invertible-oplax and Mathlib Functor.lean:727–730,743–750,764–766: the inverses give the lax maps, and their inverse oplax maps are the original d_0,d_{F,G} by the two-sided inverse identities. The resulting structure is the specified mate structure, so the definition's construction and strongness clauses are both covered.
- New node lem-sfb-adjunction-oplax-mate — PASS against CategoryTheory.Adjunction.leftAdjointOplaxMonoidal at Functor.lean:1064–1106: arbitrary monoidal categories, adjunction and lax right adjoint suffice; fields 1065–1066 are exactly the displayed formulas, and the remaining fields prove naturality, associativity and both unit laws. It has a statement only, introduces all objects, uses single-escaped TeX, and is an exact Mathlib leaf with declaration/file/line. Added the already-existing def-sfb-monoidal-category as a definition dependency; no new definition was made.
- New node lem-sfb-strong-monoidal-of-invertible-oplax — PASS against CategoryTheory.Functor.Monoidal.ofOplaxMonoidal at Functor.lean:764–766 and CoreMonoidal.ofOplaxMonoidal:743–750: precisely an oplax structure and invertible unit/tensor maps are required, with no symmetry, additivity or preservation assumptions. Inverse comparisons occur at 745–746. It has a statement only, is self-contained and has the exact Mathlib declaration/file/line. Added the existing monoidal-category and strong-monoidal-functor definition dependencies, rather than duplicating their notions.

For B3 I opened def-nagata-category, def-sfb-monoidal-category and def-sfb-strong-monoidal-functor. The last two define exactly the structures used here. I also read their source in categories.tex, Tag 0FFK, label definition-monoidal-category and the preceding equation-pentagon/equation-triangle, and Tag 0FFL, label definition-functor-monoidal-categories. The nodes use the inverse of the Stacks associator and specify the chosen unit and coherent unit map, matching the pinned Mathlib convention. The leaves' functors, adjunction Hom bijection and lax/oplax data are introduced inline. Neither leaf's source is a Stacks assertion, so no Stacks tag has been used in place of a proof-node citation.

I independently searched the whole DAG for leftAdjointOplaxMonoidal, Monoidal.ofOplaxMonoidal, oplax mates/adjoints and invertible oplax comparisons; the existing sheaf, point and scalar pullback results do not state the generic constructors. The existing def-sfb-strong-monoidal-functor defines strong structure but does not assert its construction from arbitrary oplax data. Whole-blueprint searches with tools/blueprint_refs.py for "oplax" and "mate" found only particular pullback structures and other mate comparisons; no generic replacement. The ancestor command confirms def-sfb-finite-upper-star-monoidal as both leaves' blueprint ancestor. Both leaves are retained as exact Mathlib constructors, not new unsplit obligations or restatements of the item: the first supplies general mate coherence, the second supplies the inverse-constraint coherence. No whole pro-étale monoidality conclusion has been moved into either leaf.

My own msearch.py queries use doctrinal-adjunction/colax terminology, invertible comultiplication/counit terminology, and class-based Loogle queries. The independent Loogle queries returned leftAdjointOplaxMonoidal and Monoidal.ofOplaxMonoidal respectively. A fresh grep located both constructors and CoreMonoidal.ofOplaxMonoidal. Their actual log records were appended to the corresponding leaves' mathlib_searches without altering earlier records. The first semantic query returned related mate identities rather than the exact constructor, and its verdict says so. The grep service's single-file output puts line numbers in its file field; its raw result is preserved, and the exact filenames and line numbers were verified by opening the source.

Small cases checked: for the identity adjunction on modules over a field with the identity right-adjoint lax structure, Phi and u are identities and the mate maps are the identity comparisons, including at the zero module and at the tensor unit. For the one-object terminal monoidal category, every map is the sole identity and both constructions apply without a nonemptiness or nonzero hypothesis. The empty scheme likewise adds no restriction: the existing sheaf-tensor and comparison statements apply to every scheme. Noninvertible comparisons are allowed in the first leaf and explicitly excluded only in the second, exactly as the Mathlib declarations require. There is no numerical parameter whose n=0 or n=1 case is omitted.

Changes made and reasons:

- Added references and stmt_deps to the existing definitions of monoidal category in both leaves and strong monoidal functor in the promotion leaf, completing B3 while preserving all mathematical assertions.
- Recorded independent searches and their actual outcomes for each new leaf, including the successful class-based matches.
- Updated the two affected citations.json quotes and mechanically compared all seven quotes with the cited node statements; all quotes are verbatim and every step-use pair is covered exactly once.
- Appended this second reading. The first reader's sections, including "## Review by Q46", the item's statement and all three proof steps are preserved.

No Lean file was written and no compiler, Lake or build command was run. The required dry run and delivery follow this review.

Second-reader validation: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q46 def-sfb-finite-upper-star-monoidal --no-push` printed `OK (not pushed) deliver/Q46/def-sfb-finite-upper-star-monoidal at 4224e2a54a: preflight passed`. The required repository preflight, including the split and DAG checks, succeeded. The subsequent delivery command reruns preflight before pushing.

The first push attempt was stopped by preflight after the shared origin advanced: it reported HEAD was no longer based on origin/newtargets-dag and consequently included unrelated queue/index changes and lem-cbc-zariski-enhanced-derived-descent in its diff. Those files are not in this sandbox, and nothing was pushed. The delivery tool is rerun to reconstruct the same reviewed sandbox change on the latest base; no live metadata or tooling is edited.
