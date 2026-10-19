# def-sfb-dc-tensor — Q54 stage-1 report

## 1. Files written

- `dag/nodes/sec-six-functors-basics/def-sfb-dc-tensor.json`: the existing definition, a Mathlib leaf by the product-category specialization of `CategoryTheory.ObjectProperty.lift`, `Mathlib/CategoryTheory/ObjectProperty/FullSubcategory.lean:159`, with `CategoryTheory.ObjectProperty.liftCompιIso` in the same file at line 165 for fixed-K compatibility. Zero new nodes; one Mathlib leaf, the item itself.
- `citations.json`: `[]`; the definition leaf has no proof steps or proof dependencies.
- `searches.jsonl`: actual search-command log, preserving earlier runs and the four searches independently repeated in this retry.
- `report.md` and `dry-run-current.log`: review and current validation record.

The statement, source, import flags and main-20261015 blueprint snapshot are unchanged. Seven statement dependencies name the setting, coefficient notions, pulled-back ring, bounded constructible full subcategory, ambient relative tensor and preservation theorem. `blueprint.same_as` is `[]`; the imported item's `blueprint.from` is null, not an unspecified ancestor place.

## 2. Attachments

None. No exact project declaration was found under slopmaster2. The finite-coefficient tensor result there uses a different coefficient category and finite Tor amplitude. The corresponding upstream-master restriction definition is reference material only, and its preservation input is sorry.

## 3. WANTED

None. The source is the current blueprint definition and unit together with the pinned Mathlib full-subcategory construction. No external document needs downloading and no SGA source is used.

## 4. Problems found and disposition

The original import omitted the explicit setting, full-subcategory and coefficient dependencies and lacked Mathlib searches. The saved attempt had repaired these and supplied a valid generic lift match; this retry independently checked and retained those repairs. There is no statement correction: arbitrary Lambda carries the explicit preservation hypothesis, while the three stated coefficient examples use lem-sfb-dc-tensor-preserves. In particular, no derived-completeness or finite-Tor condition is added.

The imported node has no `chapter`, `unit` or `lean_audit` field. Matching chapter/unit JSON records are absent from dag/chapters and dag/units, so their main-20261015 `_section.md` files were read directly. This is a child definition, not the unit's key node; no maintainer metadata or unit realization is invented.

## 5. What remains

The required delivery-tool validation has passed. A fresh second reader must now inspect this sandbox and deliver it. This worker does not push. Earlier attempts failed before preflight because the default worktree-slot pool was full; the old traceback is retained in dry-run.log. It is not evidence of the current result.

## Not duplicates

No new nodes are created. Searches of the whole blueprint and DAG find this specific definition, its preservation theorem, its adjunction sibling, the enclosing unit, and unrelated generic lift constructions. The preservation theorem is not a definition, the sibling states an adjunction, and the enclosing unit cites this item and cannot be used as its dependency. No other blueprint node defines exactly this restriction, so same_as is empty.

## Review by Q54

This retry independently reopened the main-20261015 chapter, restricted-functor unit, item, and all seven statement dependencies. The current shared item is still imported, with no reviewed/finished status superseding this work. The preservation dependency is now split; its statement still gives exactly the three coefficient cases used here. No node file requires a mathematical repair.

I repeated the exact blueprint-id and boundedConstructibleTensor searches under the read-only slopmaster2 project: neither found a declaration. The broader bounded-constructible searches locate only the different finite-coefficient/Tor-amplitude framework, not an attachment for this condensed module-object definition. I reread the master reference at BoundedConstructible.lean:319–364: its generic lift/curry construction supports the interpretation of the definition, while its preservation theorem is sorry and is not used as finished evidence.

I also repeated whole-blueprint searches `dc-tensor` and `restricted tensor`, and DAG searches for `restriction in both variables` and `ObjectProperty.lift`. The former finds this item, its preservation theorem and the distinct adjunction sibling; the latter finds generic lifts used in unrelated constructions. None is a second node defining this specific restriction. No new node is created and no Stacks tag or SGA source is needed for a generic full-subcategory lift.

The Mathlib source at FullSubcategory.lean:153–171 was reopened. Its only inputs are two categories, an object predicate P, a functor F, and a witness that every image object satisfies P. With source P.FullSubcategory × P.FullSubcategory, F the product inclusion followed by the ambient relative tensor, and the item's preservation hypothesis h, `P.lift F (fun KL => h KL.1.property KL.2.property)` is exactly the requested bifunctor. For fixed K the same construction applied to F_K gives the compatibility isomorphism `liftCompιIso`; both object and map equalities are definitionally true. No finite Tor amplitude, derived completeness, small-index colimit, geometric finiteness theorem or coefficient-category equivalence is inferred from Mathlib.

For C1/C4 I read the actual statements of sk-def-sfb-dc-setting, sk-def-sfb-condensed-ring, sk-def-sfb-qlbar-condensed, sk-def-sfb-pulled-back-coefficients, sk-def-sfb-bounded-constructible, sk-def-sfb-derived-tensor-hom and lem-sfb-dc-tensor-preserves. They supply respectively the setting, ordinary condensed coefficients, the specified finite-subextension Qbar ring, Lambda_X, the full subcategory with ambient morphisms, the relative ambient tensor, and precisely the preservation assertion for the displayed examples. The coefficient examples are not an unconditional assertion for all Lambda. The unchanged item is a definition leaf, so it has no proof-step citations and its empty citations.json is correct. In particular, the unit itself is not cited back, avoiding a cycle.

I checked B–E again: no new statement-only obligations, duplicate or elementary node, missing source-tag identification, moved clause, false induction or hidden non-elementary step was introduced. The recorded Mathlib file and lines cover both clauses. Identity maps and composites remain the same ambient maps, zero in either argument and the empty scheme cause no problem, and an empty full subcategory still admits the lift from its empty product source. Without preservation the hypothesis is unavailable, rather than a false unrestricted construction being asserted. No statement dispute is needed.

This retry ran msearch.py with the existing exact queries for LeanFinder (direct predicate-lift wording), Loogle (CategoryTheory.ObjectProperty.lift), grep (the lift/liftCompιIso pattern under CategoryTheory/ObjectProperty), and LeanSearch (specialized derived-tensor wording). All were available. LeanFinder returned lift as its first hit; Loogle returned lift and liftCompιIso; grep returned their actual pinned lines 159 and 165; LeanSearch returned tensor-complex and condensed-module structures, without this restriction. The commands appended their actual results to searches.jsonl; no unrun query was added to the node. The earlier alternative wordings and logs are preserved.

Previous allocator failures recorded in dry-run.log are historical, not the result of the current invocation. The current required dry run runs with default settings and --no-push. Only the sandbox report/search log and dry-run log were written during this retry; no direct git command, compiler, Lake command, Lean edit, launcher edit, shared-tree write or subagent was used. A fresh second reader must deliver after successful validation; this worker does not push.

## Current dry-run outcome

`python3 -u /home/ubuntu/weil-launcher-nt/deliver.py Q54 def-sfb-dc-tensor --no-push` exited 0 and printed `OK (not pushed) deliver/Q54/def-sfb-dc-tensor at 8fbabb7d79: preflight passed`. The output is preserved in dry-run-current.log. It acquired a default worktree slot and completed preflight without any allocator override or tool change. No push was made. The node and empty quotation certificate are exactly those accepted by this dry run; this final report update records its successful result. Final count: zero new nodes, one Mathlib leaf (the item).


## Second reading by Q54

- Item, hypothesis clause: compared with main-20261015 `def-sfb-dc-tensor.md`, its enclosing `_section.md`, and the actual statement of `lem-sfb-dc-tensor-preserves`; PASS after explicitly binding the example field E as a finite subextension of the fixed algebraic closure. The arbitrary condensed-ring clause remains conditional on preservation.
- Construction clause (no proof steps): checked `ObjectProperty.lift` at pinned `Mathlib/CategoryTheory/ObjectProperty/FullSubcategory.lean:153–161`; PASS. Set P to bounded constructibility and F to the product inclusion followed by ambient relative derived tensor. Objects are pairs `(T(K,L), h(K.property,L.property))`, and morphisms are the ambient tensor morphisms. Functor identities and composition are inherited from F.
- Fixed-K compatibility clause (no proof steps): checked `liftCompιIso` at line 165 and underlying-object/map equalities at lines 167–170; PASS after specifying `K ∈ D_cons(X,Λ)`. For every L the comparison component is the identity of T(K,L); for every g the naturality equation is `T(K,g) ≫ id = id ≫ T(K,g)`.
- Statement dependencies: read all seven actual statements; PASS. They define the field/scheme setting, condensed rings and finite coefficient extensions, the special finite-subextension Qbar ring, pulled-back coefficients, the bounded constructible full subcategory, ambient relative derived tensor, and preservation for precisely the displayed coefficient examples. No proof of a dependency is substituted for its statement.
- New nodes: none; PASS. Whole-blueprint `dc-tensor`/`restricted tensor` searches and whole-DAG restriction/lift searches find no other definition of this particular conditional tensor restriction. The unit contains this child; the preservation theorem and tensor-Hom adjunction are distinct statements, not replacement definitions.
- Mathlib leaf (the item): independently ran new LeanFinder, Loogle and grep queries through msearch.py; all available, with actual logs appended by the tool. PASS: LeanFinder leads with ObjectProperty.lift, Loogle returns liftCompιIso, and grep confirms the pinned preservation hypothesis and comparison lines. The new queries and actual results are recorded in the node.
- Project attachment audit: exact-id/tensor-name searches of read-only slopmaster2 find no exact declaration; PASS. The finite-coefficient étale tensor theorem at OpenImmersion.lean:79 requires finite Tor amplitude and uses a different category. Master `ModuleObject/Derived/BoundedConstructible.lean:319–364` confirms the lift/curry interpretation, but its preservation theorem is sorry and supplies no finished proof.
- Edge cases: zero in either variable, an empty scheme, a field coefficient, and the degree-zero tensor specialization leave the same ambient objects and maps; PASS. No division, nonemptiness, inverse or new boundedness argument occurs in the lift. An empty source full subcategory also permits the unique empty-source lift. Over a coefficient ring where preservation fails (for example a point with Z/ell² coefficients and two Z/ell complexes), the required hypothesis is absent; no unconditional restriction is asserted.
- Citation certificate and form: PASS. No proof steps and no new nodes exist, so `citations.json = []` is exact. The item names the current blueprint source; no Stacks tag or SGA source is invoked. Mathlib declaration, file and lines were read directly.

STATEMENT-DISPUTED (missing explicit binders, repaired): in the standalone imported text, E occurs in `underline O_E` and `underline E` without a binder, and “For fixed K” omits its domain. Reading the cited coefficient definition alone allows arbitrary subfields E, whereas the cited preservation lemma quantifies only finite E/Q_ell. This is a context/type check, not a claim that the generic conditional lift is false. The enclosing unit explicitly supplies the finite-extension condition and the full-subcategory domain, so those are now written in the item's statement. Also replaced “the setting” by its defining node reference. No new hypothesis is placed on the arbitrary-Lambda conditional construction, and no completeness or Tor-amplitude condition is introduced.

Changes: clarified the finite coefficient-field binder and fixed-K domain; added the setting reference, three independently executed Mathlib searches and this second-reading record. All first-worker sections, including `## Review by Q54`, are preserved. Zero new nodes; one Mathlib leaf (the item). Validation and delivery follow below.

Second-reader dry run: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q54 def-sfb-dc-tensor --no-push` exited 0 and printed `OK (not pushed) deliver/Q54/def-sfb-dc-tensor at 1cd83eb328: preflight passed`. This validates the repaired statement and second-reading record; output is preserved in dry-run-second-reading.log. The required push invocation follows.
