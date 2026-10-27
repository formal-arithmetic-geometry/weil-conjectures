Current status (2026-10-24): the inherited source metadata has now been corrected in the live repository. The required resumed dry run passed at e14d964180a. Earlier blocker sections below are retained as the history of previous attempts and no longer describe the current validation. The sandbox source has been refreshed verbatim from live; this delivery proposes no change to that maintainer-owned field.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dc-hom-single.json`: statement item; repaired split, not a Mathlib leaf. The exact statement and all maintainer-owned fields are retained. The split-owned blueprint.from chain is corrected to the original blueprint node.
- `citations.json`: twenty entries, one for every cited node in every numbered proof step, quoting the node's entire statement verbatim.
- `searches.jsonl`: actual current msearch.py records. The item's mathlib_searches are transcribed from these records, with the same tool and query and the returned declarations.
- No new DAG nodes; zero new Mathlib leaves. The extraction script and the text extracted from the source PDF are sandbox scratch material only.

## Attachments

None. The project search by the item id and by boundedConstructible/hom found the matching theorem in `lean/Sheaf/AlgebraicGeometry/BoundedConstructibleHomSingle.lean:45`, but its proof is `by sorry`. The upstream ProEtale/ModuleObject/Derived/BoundedConstructible.lean preservation argument calls this theorem, so it is not independent attachment evidence. The upstream finite-coefficient and étale declarations concern different coefficient categories. No compiler or Lake command was run.

## WANTED

None. Bhatt–Scholze and the relevant Stacks text are present locally.

## Problems corrected

The existing integral step applied `lem-sfb-integral-general-lfp-hom-finiteness`, whose statement assumes positive characteristic, to an item explicitly including characteristic zero. This is a proof-citation error, not an error in the item statement. I replaced it with the existing arbitrary-field theorem `lem-per-adic-closed-constructible` after checking the hypotheses and the general-lfp/completion bridge. Its first conclusion is about the ambient ordinary internal Hom; completed tensor in its other conclusions does not change this Hom. The bridge reads the same underlying object over the completed coefficient sheaf; it does not complete an arbitrary input or substitute a discrete integral coefficient ring.

The old rational and closure steps descended to bounded complexes but referred to earlier cases phrased for degree-zero objects. Steps 2–4 now explicitly establish the needed intermediate assertions for all bounded constructible integral and rational inputs before specializing to F[0],G[0]. No circular use of the parent preservation theorem or its degree-zero devissage is made.

The active proof and proof_origin cite Bhatt–Scholze, not the inherited prohibited legacy reference in the item's maintainer-owned source metadata. That metadata and the Lean record were not edited. The current blueprint was read through `literature/blueprint/latest/`; its integral-completeness and coefficient-descent route is retained.

## Unfinished work

None at stage 1. This delivery is a natural-language split and does not claim a Lean proof. No edits were made outside the assigned sandbox.

## Not duplicates

There are no new nodes or new-versus-existing pairs. The whole-DAG search by internal Hom, finite coefficients and the source's Lemma 6.7.13 found `lem-per-finite-tor-internal-hom-any-field` and `lem-per-adic-closed-constructible`. The latter, together with `lem-sfb-integral-constructible-completion-bridge`, eliminates the need to create a characteristic-zero finite-coefficient lemma or a new integral finiteness clause. Blueprint searches for internal Hom, RHom, 6.7.13, finite-field internal and internal Hom finiteness found no blueprint node equivalent to the exact degree-zero item: the preservation nodes state the bounded-complex theorem, not this degree-zero lemma. The item's same_as remains empty.

## Review by Q17

I read the current item, the chapter and unit records, and the latest blueprint proof of `lem-sfb-dc-hom-preserves`. For the source I read Bhatt–Scholze Definition 6.5.1's surrounding constructibility discussion, Proposition 6.6.11 and its proof, Lemma 6.7.13 and its proof, Proposition 6.8.11(3), Lemmas 6.8.12–13, Proposition 6.8.14 and Remark 6.8.15. These justify the three coefficient stages and the intermediate use of complete integral objects. I also read Stacks sites-cohomology.tex at lemmas internal-hom, section-RHom-over-U and restriction-RHom-to-U (08J9, 08JA, 08JB), and the current blueprint statement of finite-type finite dimension. No new nodes require further source checks.

For step 1 I opened the statements of normed-coefficient-realization, internal-scalar-tensor-comparison and derived-tensor-hom. The realization supplies the exact equivalence and preservation of the actual general-lfp predicate; it does not assert a Hom comparison. The proof therefore writes the natural Hom-bijections explicitly, using the cited tensor comparison and closed adjunction. An inverse equivalence is restriction along the inverse coefficient isomorphism, so exactness holds on every scheme as required by the tensor comparison.

For step 2 I checked the two finiteness statements against a finite-type scheme over any field. Noetherianity of the field is verified from its ideals and finite dimensionality comes from lem-kun-dimension-finite-type, not from a hypothesis silently added to the item. Primality of ell is part of the coefficient certificate, and ringChar(k) != ell implies ell is nonzero, hence a unit in the field and in every local ring. I opened the coefficient-limit identification, constructibility/completion bridge and module-object/ringed-site-derived-comparison statements. They give the actual coefficient identification, both object predicates, and the same underlying sheaves; no perfectness of a constructible sheaf on the whole site is assumed.

For step 3 I read lem-per-adic-closed-constructible's first assertion: for P,Q in its integral category, its ambient H_R(P,Q) remains in that category, over ANY field with ell invertible. Step 2 supplies exactly that category, with the required separatedness, finite type, Noetherianity and dimension hypotheses. The module comparison's statement identifies the derived Hom objects and evaluation, and the bridge's reverse implication supplies the item's general-lfp conclusion. This corrects the characteristic-zero gap without inventing a duplicate integral clause.

For step 4 the rationalization equivalence supplies bounded constructible integral representatives, not necessarily sheaves. The previous step applies to those complexes. I opened the Hom-inversion statement and checked its two hypotheses: the first representative is bounded constructible and the second bounded below. The extension-preservation node says exactly that the resulting rational object remains bounded constructible.

For step 5 I opened all six cited statements. Predicate comparison converts the initial general-lfp inputs into the finite scalar-model category used by the two-colimit theorem, and also converts the descended models as needed. The two-colimit theorem descends objects; finite-extension preservation permits their compositum. Internal-Hom continuity asserts the exact small-filtered-diagram and common-termwise-lower-bound property required by the closure comparison; it is not merely a global Hom statement. The other comparison hypothesis is that L_E is bounded below, which follows from its bounded constructibility. Extension-to-closure preservation and predicate comparison give the desired output. The models need not be degree-zero, since step 4 was explicitly stated for bounded complexes.

I checked small cases: empty X, a zero input, ell=2 in characteristic zero, and torsion integral inputs. The geometric hypotheses and comparisons still apply in the empty and zero cases. Characteristic zero supplies invertibility without a positive-prime characteristic witness. Torsion is allowed by the integral bridge and adic theorem; there is no unjustified global locally free assumption. Nonprime ell has no coefficient certificate, rather than creating an extra case.

Against delivery-errors B–E: every object and used fact is supplied by an existing statement; every non-elementary use is in uses and proof_deps; no step invokes a cited node's proof; no new node relabels a clause; the bounds and coefficient categories match; and the comparisons, rather than a bare word 'transport', are written or directly stated by a cited theorem. All five steps are below 2000 characters and contain no hidden independent lemma. Dependency traversal found no path back to this item from the newly used existing tools. The split_report explicitly declares the off-unit tools and explains why they implement the unit's existing route. The exact item statement, its hypotheses and its conclusion were not weakened or altered.

## Server validation and blocker

The first server review_split and full deliver.py --no-push rejected the unchanged inherited source metadata because it names SGA 4½, and also rejected the inherited blueprint.from.node because it named a created node. The full preflight additionally rejected the words "the item's" in two proof steps; those phrases were made explicit. The authoritative tools/node_fields.py lists blueprint.from as split-owned, so I repaired the chain to lem-sfb-dc-hom-preserves with lem-sfb-dc-hom-small-coefficients in via.

The remaining route-lock error is outside the split's editable fields: tools/node_fields.py and tools/README.md explicitly make source maintainer-owned, but tools/review_split.py scans that unchanged source.place and rejects its inherited legacy reference. The new proof sources and proof_origin use only allowed sources. Repair requires the maintainer to correct source.place, or a launcher repair to the gate's treatment of inherited protected metadata; the worker must not patch the launcher, bypass the gate or alter protected fields. The completed split, quotations and actual search log remain in this sandbox. Nothing was pushed.

Final full dry run: deliver.py Q17 lem-sfb-dc-hom-single --no-push exited 1 with exactly ONE remaining preflight reason: review_split rejects SGA 4½ in the unchanged maintainer-owned source.place. The blueprint and proof-text diagnostics were repaired and no longer appear. Nothing was pushed.

## Resumed validation on 2026-10-24

I retained the previous proof, report, quotations and recorded searches, and compared the sandbox with the current live item. Only split-owned fields differ. The live item still has no reviewed stage-1 record, no repair note, and no finished matching theorem: boundedConstructible_hom_single remains `by sorry`. The protected source metadata is byte-identical to live. No new nodes were introduced.

The required first dry run on the preserved split exited 1 with exactly one reason: review_split rejects SGA 4½ in the inherited source.place. I then independently inspected tools/node_fields.py: source is in MAINTAINER, not SPLIT_OWNS; tools/review_split.py lines 177–186 scan that source even when unchanged. This is a gate/protected-metadata conflict, not a failure of the new proof route. The authorized delivery command must refuse the push until a maintainer corrects that metadata or the gate. I did not change either.

The current server check_dag reports no finding introduced by this sandbox or on its nodes. The separate server review_split reproduces only the route-lock error. I opened every cited statement again, matched all 20 entries of citations.json verbatim, checked proof_deps against the union of uses, and verified the five step lengths (862, 995, 759, 671, 1144 characters). The current blueprint statement still has the same integral/rational/closure content. The existing search log was retained; the resumed service results were read and the new LeanSearch wording was appended to mathlib_searches. They provide only generic Ext/derived-category or condensed-category results and no match for the geometric finiteness assertion.

No git commands, compiler, Lake invocation, repository write, launcher edit or agent launch was used. Delivery remains BLOCKED by the single server preflight rejection; nothing was pushed.

## Latest resumed dry run (2026-10-24)

The required initial dry run of the retained item and report completed with exit 1. Its only preflight reason is again the route-lock rejection of SGA 4½ in the inherited source.place. No delivery process remains active and nothing was pushed.

I compared the retained JSON against the current read-only repository: the only changed top-level fields are blueprint, mathlib_searches, proof, proof_deps, proof_origin and split_report. The source object is identical. The live item is split without a reviewed record, and no repair note exists. tools/node_fields.py still places source in MAINTAINER and omits it from SPLIT_OWNS; tools/review_split.py still scans the inherited source in its route-lock check. Removing or changing that reference would modify protected metadata, so the worker cannot repair this diagnostic within the authorized scope.

I verified again that all 20 citations cover exactly the step/node uses, every quote is verbatim in the current cited statement, and proof_deps equals the union of uses. Step lengths remain 862, 995, 759, 671 and 1144 characters. The existing search log and all proof work are retained. The project Lean search finds no matching finished declaration in WeilConjectures; the assigned Sheaf theorem still ends in sorry. The next action requires a maintainer correction of source.place or a tool-owner repair of the inherited-metadata check. No repository or launcher file was written, no git command or compiler was run, and no agents were started.

## Dispatcher retry validation — 2026-10-24T03:54:51+00:00

The required first dry run of the retained split, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q17 lem-sfb-dc-hom-single --no-push`, completed with exit 1. The server preflight reports exactly one reason: `route lock: lem-sfb-dc-hom-single cites ['SGA 4½']; no SGA source except SGA 5`. It reports zero new nodes and nothing pushed. The process has exited.

I confirmed the current ownership conflict directly: tools/node_fields.py places source in MAINTAINER, and tools/README.md says this field is never changed by a delivery. tools/review_split.py includes the existing source in its route-lock scan. The sandbox source is identical to the current repository source. The only differing top-level fields are blueprint, mathlib_searches, proof, proof_deps, proof_origin and split_report. Thus changing the new proof cannot remove this diagnostic; a maintainer must correct the inherited metadata or the tool owner must repair the gate. No protected field or launcher script was modified.

The matching Sheaf theorem at BoundedConstructibleHomSingle.lean:45 still has `by sorry`; the upstream preservation theorem calls it, so it cannot justify ATTACH. I retained all prior work and searches, checked the exact twenty step/node citation pairs against current statements, verified every quotation is verbatim and proof_deps equals the union of uses, and confirmed the five step lengths are 862, 995, 759, 671 and 1144 characters. No repair note exists for this item. No compiler, Lake, git command, agent launch or repository write was performed. Delivery is BLOCKED by the unchanged server preflight failure; no push was attempted.

## Dispatcher retry validation — 2026-10-24T03:59:16.273856+00:00

The required initial dry run of the retained split completed with exit 1. The sole server preflight reason is still `route lock: lem-sfb-dc-hom-single cites ['SGA 4½']; no SGA source except SGA 5`. The delivery process exited; nothing was pushed.

I rechecked tools/node_fields.py and tools/README.md: source remains maintainer-owned and is never changed by a delivery. tools/review_split.py still scans that source in its route-lock check, and the sandbox source equals the current repository source. Only blueprint, mathlib_searches, proof, proof_deps, proof_origin and split_report differ from live. This diagnostic cannot be repaired through the permitted split fields; the maintainer must correct the inherited source metadata or the tool owner must repair the check. No gate or protected field was modified.

The matching Sheaf declaration still ends in `by sorry`, and the upstream preservation theorem uses it, so there is no attachment. No repair note exists. All twenty citations still cover exactly the proof-step uses and are verbatim in current statements; proof_deps is their union. The five steps remain below 2000 characters. Existing searches and all mathematical work were retained. No repository write, launcher edit, git command, compiler, Lake invocation or agent launch was performed. Delivery remains BLOCKED by this tool/protected-metadata conflict.


## Dispatcher retry validation — 2026-10-24T04:03:43.448035+00:00

The required first dry run of the retained item and report exited 1. Its only preflight failure remains `route lock: lem-sfb-dc-hom-single cites ['SGA 4½']; no SGA source except SGA 5`. The command has exited and nothing was pushed.

I independently read tools/node_fields.py and tools/README.md: source is still maintainer-owned and explicitly never changed by a delivery. tools/review_split.py lines 175–186 still scan that unchanged source. The live and sandbox source objects are identical, including the prohibited legacy reference in source.place. Only blueprint, mathlib_searches, proof, proof_deps, proof_origin and split_report differ. No repair note exists and the live item has no reviewed record. This diagnostic requires a maintainer correction of the inherited source metadata or a tool-owner repair; editing the permitted proof fields cannot remove it. No protected field or gate was changed.

The project theorem boundedConstructible_hom_single at lean/Sheaf/AlgebraicGeometry/BoundedConstructibleHomSingle.lean:45 still ends in `by sorry`; the upstream preservation theorem calls it at WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean:490. Thus neither supplies an attachment. I verified all twenty retained citations against current node statements, their exact coverage of step/node uses, and proof_deps as the union of uses. Step lengths remain 862, 995, 759, 671 and 1144 characters. All prior proof, citations and actual searches are retained. Only this sandbox report was written; no repository write, launcher edit, git command, compiler, Lake invocation or agent launch was performed.


## Dispatcher retry validation — 2026-10-24T04:09:26.265358+00:00

The required initial dry run of the retained split exited 1 with exactly one server preflight reason: `route lock: lem-sfb-dc-hom-single cites ['SGA 4½']; no SGA source except SGA 5`. The command has exited and nothing was pushed.

I read the current tools/node_fields.py and tools/review_split.py. The former explicitly places source in MAINTAINER and excludes it from SPLIT_OWNS; the latter scans the inherited source as well as proof-step sources. The sandbox source equals the live source, whose place includes the legacy SGA reference. Only blueprint, mathlib_searches, proof, proof_deps, proof_origin and split_report differ from live. Thus repairing the one remaining diagnostic requires a maintainer metadata correction or a tool-owner gate repair; no permitted worker-field change resolves it. I did not modify protected metadata or any tool.

The live item remains split without a reviewed record, and no repair note exists. I reread the matching theorem at lean/Sheaf/AlgebraicGeometry/BoundedConstructibleHomSingle.lean:45: its proof is still `by sorry`. The upstream preservation theorem calls it, so there is no finished attachment. All twenty citations were checked verbatim against the current cited statements, with exact step/use coverage and proof_deps equal to their union. Step lengths remain 862, 995, 759, 671 and 1144 characters. Existing proof work and all thirteen actual search-log records were retained. Only this sandbox report was written; no repository write, launcher modification, git command, compiler, Lake invocation or agent launch was performed.


## Dispatcher retry validation — 2026-10-24T04:17:36.972787+00:00

The required first dry run of the retained split completed with exit 1. Its sole server preflight failure remains `route lock: lem-sfb-dc-hom-single cites ['SGA 4½']; no SGA source except SGA 5`. The delivery process has exited; nothing was pushed.

I independently read the current ownership rule in tools/node_fields.py and tools/README.md, and the route-lock scan in tools/review_split.py. The scan includes source.place, whereas source is explicitly maintainer-owned and never changed by a delivery. The sandbox and live source objects are identical, including that inherited reference. Only blueprint, mathlib_searches, proof, proof_deps, proof_origin and split_report differ from live. This failure needs a maintainer correction of inherited source metadata or a tool-owner gate repair; no permitted worker-field change removes it. No protected field or tool was edited.

The matching project theorem boundedConstructible_hom_single at lean/Sheaf/AlgebraicGeometry/BoundedConstructibleHomSingle.lean:45 still has `by sorry`, and the upstream preservation theorem calls it at lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean:490, so neither is attachment evidence. There is no repair note; the live item is split without a reviewed record. I checked all twenty retained citation quotes against current node statements, their exact step/use coverage, and proof_deps as the union of uses. Step lengths remain 862, 995, 759, 671 and 1144 characters. I read and retained all thirteen actual search-log records without repeating the unchanged search questions. All previous proof, report and citations remain intact. Only this sandbox report was written; no repository write, git command, launcher modification, compiler, Lake invocation or agent launch was performed.


## Dispatcher retry validation — 2026-10-24T04:21:39.690318+00:00

The required initial dry run of the retained split exited 1. Its only server preflight failure is still `route lock: lem-sfb-dc-hom-single cites ['SGA 4½']; no SGA source except SGA 5`. The process exited; nothing was pushed.

I independently verified the conflict in current tools/node_fields.py, tools/README.md and tools/review_split.py: source is maintainer-owned and must remain unchanged by a delivery, while the route-lock check scans that source. The sandbox source is identical to live and contains the inherited SGA reference in source.place. The only changed top-level fields are blueprint, proof_origin, proof_deps, mathlib_searches, split_report and proof. A maintainer metadata correction or tool-owner gate repair is required; changing the permitted proof fields cannot repair this diagnostic. No protected field or tool was modified.

The matching Sheaf theorem at BoundedConstructibleHomSingle.lean:45 still ends in `by sorry`, and the upstream preservation theorem calls it at BoundedConstructible.lean:490. There is no finished attachment. The live item has no reviewed record and no repair note. I verified all twenty retained citation entries verbatim against current node statements, exact step/use coverage and proof_deps as the union of uses. Step lengths remain 862, 995, 759, 671 and 1144 characters. I retained the proof, prior report, quotations and all thirteen actual search records, without repeating unchanged search questions. Only this sandbox report was written; no repository write, launcher modification, git command, compiler, Lake invocation or agent launch was performed.


## Dispatcher retry validation — 2026-10-24T04:26:20.838438+00:00

The required initial dry run of the retained item and report completed with exit 1. Its sole preflight failure is `route lock: lem-sfb-dc-hom-single cites ['SGA 4½']; no SGA source except SGA 5`. The delivery process has exited; nothing was pushed.

I independently verified the current ownership conflict in tools/node_fields.py and tools/README.md: source is maintainer-owned and never changed by a delivery. The route-lock scan in tools/review_split.py nevertheless includes source.place. The retained and live source objects are identical. Only blueprint, mathlib_searches, split_report, proof_origin, proof_deps and proof differ from live, all split-owned fields. Consequently a maintainer correction of the inherited source metadata or a tool-owner repair is required; changing the permitted proof fields cannot resolve this diagnostic. No protected field or tool was modified.

The exact assigned theorem at lean/Sheaf/AlgebraicGeometry/BoundedConstructibleHomSingle.lean:45 still ends in `by sorry`. The project-library search finds its use at lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean:490, not a finished proof of the item. No repair note exists and the live item has no reviewed record. All twenty retained citation entries are verbatim in current cited statements, cover exactly the step/node uses, and proof_deps equals their union. Step lengths remain 862, 995, 759, 671 and 1144 characters. The thirteen actual search-log records and all earlier proof, report and citations are retained without repeating unchanged search questions. Only this sandbox report was written; no repository write, git command, launcher modification, compiler, Lake invocation or agent launch was performed.


## Dispatcher retry validation — 2026-10-24T04:33:25.748640+00:00

The required initial dry run of the retained item and report exited 1. Its only server preflight failure is `route lock: lem-sfb-dc-hom-single cites ['SGA 4½']; no SGA source except SGA 5`. The delivery process has exited and nothing was pushed.

I compared the retained node with the current repository. The source objects are identical; only blueprint, mathlib_searches, proof, proof_deps, proof_origin and split_report differ. tools/node_fields.py places source in MAINTAINER, and tools/README.md line 138 explicitly says it is never changed by a delivery. tools/review_split.py lines 177–186 scan that inherited source. The remaining diagnostic therefore requires a maintainer correction of source.place or a tool-owner gate repair. Editing permitted proof fields cannot remove it, and no protected field or gate was modified.

The live item has no reviewed record and no repair note. The matching Sheaf theorem at BoundedConstructibleHomSingle.lean:45 still ends in `by sorry`; the project preservation theorem at WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean:490 invokes it, so it supplies no attachment. All twenty retained quotations still match the current cited statements verbatim and cover exactly the step/node uses. proof_deps equals their union; step lengths are 862, 995, 759, 671 and 1144 characters. All previous proof work and thirteen logged searches were retained. Only this sandbox report was written; no repository or launcher write, git command, compiler, Lake invocation or agent launch was performed.


## Dispatcher retry validation — 2026-10-24T04:39:31.965888+00:00

The required initial dry run of the retained split exited 1. The only preflight failure is the route-lock rejection of SGA 4½ in the inherited source.place. The delivery process has exited and nothing was pushed.

I read the current worker contract, stage-1 instructions, SETUP three-level rules, GOAL, chapter and unit records, and delivery-errors B–E. I confirmed tools/node_fields.py still puts source in MAINTAINER, and tools/README.md explicitly says this field is never changed by a delivery. tools/review_split.py lines 175–186 still scan that inherited source. The source objects in the sandbox and current repository are identical. Only proof, blueprint, proof_deps, mathlib_searches, split_report and proof_origin differ. Thus there is no authorized worker-field repair for this diagnostic: the maintainer must correct source.place or the tool owner must repair the check.

The current project search finds the matching declaration in Sheaf/AlgebraicGeometry/BoundedConstructibleHomSingle.lean:45, still ending in by sorry; the WeilConjectures preservation proof calls it at line 490. There is no attachment from these declarations, no reviewed record and no repair note. I checked all twenty retained quotation entries against current node statements and their exact step/node coverage; proof_deps equals the union of uses. Step lengths are 862, 995, 759, 671 and 1144 characters. All existing proof work and thirteen logged search records remain intact. Only this sandbox report was changed; no repository write, launcher modification, git command, compiler, Lake invocation or agent launch was used.


## Dispatcher retry validation — 2026-10-24T04:45:52.414423+00:00

The required initial dry run of the preserved item and report exited 1. Its sole preflight failure is `route lock: lem-sfb-dc-hom-single cites ['SGA 4½']; no SGA source except SGA 5`. The delivery process exited; nothing was pushed.

I independently checked tools/node_fields.py, tools/README.md and tools/review_split.py. Source is maintainer-owned and must remain unchanged by a stage-1 delivery, but the route-lock scan includes it. The sandbox source equals the live source and contains the inherited prohibited reference in source.place. Only blueprint, mathlib_searches, proof, proof_deps, proof_origin and split_report differ from live. No permitted worker-field repair can resolve this diagnostic. It requires a maintainer correction of inherited source metadata or a tool-owner gate repair; neither protected metadata nor a tool was changed.

The live node has no reviewed record and no repair note exists. The matching Sheaf theorem at BoundedConstructibleHomSingle.lean:45 still ends in `by sorry`; the upstream preservation proof invokes it at WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean:490. These do not supply a finished attachment. I verified all twenty retained quotation entries verbatim against current cited statements, exact step/node coverage, and proof_deps as the union of uses. The five step lengths remain 862, 995, 759, 671 and 1144 characters. All earlier proof, report, quotations and thirteen logged search records were retained, without repeating unchanged search questions. Only this sandbox report was written; no repository write, launcher edit, git command, compiler, Lake invocation or agent launch was performed.


## Dispatcher retry validation — 2026-10-24T04:51:33.021155+00:00

The required first dry run of the retained item and report exited 1. Its single preflight failure remains: `route lock: lem-sfb-dc-hom-single cites ['SGA 4½']; no SGA source except SGA 5`. The delivery process has exited, and nothing was pushed.

I compared the sandbox item with the current repository: source is identical, including the legacy reference in source.place. Only blueprint, mathlib_searches, proof, proof_deps, proof_origin and split_report differ. I read tools/node_fields.py, tools/README.md's field-ownership section, and tools/review_split.py's route-lock implementation. Source remains maintainer-owned and never changed by a delivery; the gate nevertheless scans it. An authorized worker-field repair cannot resolve this error. A maintainer must correct the inherited metadata or the tool owner must repair the check. Neither protected fields nor tools were changed.

The live item has no reviewed record or repair note. The matching Sheaf theorem at BoundedConstructibleHomSingle.lean:45 still ends in `by sorry`; the upstream project search finds its invocation, not an independent finished declaration. I verified all twenty retained citation quotations against current statements, their exact step/node coverage, and proof_deps as the union of uses. The five step lengths remain 862, 995, 759, 671 and 1144 characters. All retained proof, report, citations and search records remain intact. Only this sandbox report was written; no repository write, git command, launcher edit, compiler, Lake invocation or agent launch was performed.


## Resumed review by Q17 — current sources, 2026-10-24

I retained the complete proof, earlier report, twenty quotation entries and thirteen actual search-log records. The first required dry run exited successfully: `OK (not pushed) deliver/Q17/lem-sfb-dc-hom-single at e14d964180a: preflight passed`. The live source.place now omits the prohibited inherited reference. I refreshed the sandbox source from that live value without proposing any protected-field change. The previous blocker is resolved upstream; all earlier failed-validation entries are historical.

I reread the five proof steps and every current cited statement. In step 1 the realization theorem preserves the general-lfp predicate, the scalar comparison supplies the tensor isomorphism under exact scalar extension, and the displayed natural adjunction bijections identify the transported Hom. Step 2 supplies Noetherianity, finite dimension and invertibility before applying the integral bridge; the coefficient-limit theorem identifies the coefficient ring rather than completing inputs. Step 3 uses the arbitrary-field conclusion of lem-per-adic-closed-constructible, the module-object Hom comparison, and the reverse bridge implication on the same Hom object. In step 4 the rationalization equivalence supplies bounded integral representatives; the inversion theorem's constructibility and lower-bound hypotheses hold even though those representatives need not be concentrated in degree zero. In step 5 predicate comparison supplies precisely the finite-model inputs required by descent and continuity, and continuity supplies the small filtered diagram property assumed by the closure comparison. A compositum brings the two finite models to one coefficient field. Extension preservation supplies the final conclusion.

I reread Bhatt–Scholze Proposition 6.6.11, Lemma 6.7.13, Proposition 6.8.11(3), Lemmas 6.8.12–13, Proposition 6.8.14 and Remark 6.8.15 in the retained PDF extraction, and the latest blueprint proof of lem-sfb-dc-hom-preserves. The blueprint's integral, inversion and finite-stage descent route is unchanged; the proof cites existing allowed tools instead of the blueprint's prohibited external reference. The arbitrary-field theorem is used through its stated hypotheses, not by silently importing the source's positive-characteristic-only formulation. No new node is necessary.

All twenty step/node quotations remain verbatim in current statements and cover exactly the uses; proof_deps is their union. All five steps remain below 2000 characters. Empty schemes, zero inputs, characteristic zero with ell=2 and torsion integral inputs are covered by the same stated tools. Primality comes from the coefficient certificate. The assigned Sheaf theorem still has `by sorry`, while the upstream preservation proof invokes it, so neither is an attachment. There is no stage-1 reviewed record or repair note superseding this work. The retained Mathlib results supply only generic category and condensed structure or constructible-image facts. No search was invented or repeated. No Lean was written or compiled, no agent was started, and no repository, launcher or tool file was changed.
