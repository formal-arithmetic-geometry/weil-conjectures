# Q120 stage-1 split: lem-coef-symmetric-operadic-left-horn-filling

## Files written

All paths below are relative to this item's sandbox. No shared-project files, Lean files, unit records or launcher files were changed.

- dag/nodes/sec-six-functors/lem-coef-symmetric-operadic-left-horn-filling.json: existing statement preserved; ten-step proof, status split.
- dag/nodes/sec-six-functors/lem-coef-quasicategory-simplex-join-attachment.json: statement-only lemma; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-cocartesian-inner-horn-preimage.json: statement-only lemma; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-symmetric-family-active-slice-calculus.json: statement-only lemma; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-symmetric-family-inert-cone-initiality.json: statement-only lemma; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-operadic-colimit-finite-amalgamation.json: statement-only lemma; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-operadic-colimit-active-join-boundary.json: statement-only lemma; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-cofinal-relative-join-slice-restriction.json: statement-only lemma; no Mathlib match.
- citations.json: one verbatim statement quotation per (proof step, cited node); the complete statements are quoted to retain all hypotheses.
- searches.jsonl, searches/, search_plan.json: actual search-command log, full returned results, and queries used by the preparation script. prepare_split.py is the reproducible sandbox-only writer, not a compiler or project tool.

Seven new nodes; zero Mathlib leaves.

## Attachments

None. Searched WeilConjectures/ of the read-only slopmaster2 source for the exact blueprint tag and for operadic, symmetric-operad, horn, cocartesian, join-slice and relative-colimit terminology. No project declaration states this item or the seven new claims. The upstream master is reference material, not a finished attachment. No compiler, Lean server build, Lake or git command was run.

## Literature wanted

WANTED: Lurie, Higher Algebra, September 18, 2017, Theorem 3.1.2.3(B), printed pp.330 and 334-341, for lem-coef-symmetric-operadic-left-horn-filling. Read the Harvard online PDF; do not mistake the unarchived PDF for a literature/ document. The proof is marked agent-written.

WANTED: Higher Algebra, Lemma 3.1.2.5, pp.332-333, for lem-coef-quasicategory-simplex-join-attachment, including its opposite.

WANTED: Higher Algebra, Lemma 2.4.4.6, p.307, for lem-coef-cocartesian-inner-horn-preimage.

WANTED: Higher Algebra, proof of Theorem 3.1.2.3, step (1), pp.336-337, for lem-coef-symmetric-family-active-slice-calculus.

WANTED: Higher Algebra, proof of Theorem 3.1.2.3, step (3), pp.340-341, for lem-coef-symmetric-family-inert-cone-initiality.

WANTED: Higher Algebra, Proposition 3.1.1.8, p.321, for lem-coef-operadic-colimit-finite-amalgamation; Definition 3.1.1.2 and Remark 3.1.1.5 for the mapping-space convention and invariance.

WANTED: Higher Algebra, Proposition 3.1.1.7, pp.319-320, for lem-coef-operadic-colimit-active-join-boundary.

WANTED: Higher Algebra, proof of Theorem 3.1.2.3, pp.336 and 341, and Higher Topos Theory, Theorem 4.1.3.1, Proposition 4.1.1.3(4) and Proposition 2.1.2.5, for lem-coef-cofinal-relative-join-slice-restriction. I read these HTT results online: comma contractibility gives cofinality, a cofinal monomorphism is right anodyne, and relative join-slice restriction is a trivial Kan fibration. Its two cofinality orientations are explicitly stated. No Stacks tag states these quasicategorical operadic assertions. No SGA source is used.

## Problems found and corrections

The imported item was already a faithful cocartesian-q specialization of HA 3.1.2.3(B); no statement dispute or added hypothesis was necessary. It had no proof. Its chapter, inherited unit, created metadata, source and prior search records are retained. The ancestor is prop-coef-integral-exceptional-adjoint, specifically paragraph 2 of its mapping-complex comparison, reached through the existing symmetric-operadic-extension ancestry. The current main-20261015 proof and older master ancestor text were read. This item supplies local coherent lifting infrastructure; it is not the unit's key statement, so no unit realization was changed.

The online printed proof's group labels G(2), G(3) and their primed variants interchange in several sentences. The split uses semantic names instead: neutral factorization pair and output projection pair. Inserting an inert-active factorization misses an INNER vertex; appending an output projection misses the LAST vertex. These are different lifting arguments and are never conflated.

During preparation the shared snapshot initially lacked the item. It appeared when the delivery tool refreshed its temporary worktree. The initial dry run failed because citations.json was missing, before the split had been written. That provisional missing-input report has been replaced by this report; the item and its current metadata are now present. This was not a proof failure and does not discard the searches.

I removed the first-vertex restriction assertion from the new active-slice node because the existing initial-poset-slice-restriction lemma already proves it. I also did not create the proposed generic universal-cone boundary lemma: step 2 derives it from existing join/cocone mapping formulas, the constant-target test and relative-initial boundary lifting. The nontrivial remaining inputs are the seven statement-only nodes, not fresh restatements of any clause of the item.

## Not duplicates

lem-coef-quasicategory-simplex-join-attachment vs lem-coef-infinity-relative-join-simplex-extension: the former compares an evaluated join-slice pushout with a simplex attachment to a full subcategory by a Joyal trivial cofibration; the latter extends maps on a relative join for a cocartesian family and assumes a relative colimit. They have different maps, hypotheses and conclusions.

lem-coef-quasicategory-simplex-join-attachment vs lem-coef-infinity-anodyne-cocones: a right-anodyne pushout-join criterion does not give the full-subcategory evaluation comparison, which can involve a nonembedded simplex and its degeneracies.

lem-coef-cocartesian-inner-horn-preimage vs lem-coef-cocartesian-joyal-fibration: the former makes a pulled-back inner horn a categorical equivalence given lifts of one selected edge. The latter lifts against an already known categorical equivalence under a global cocartesian-fibration hypothesis; it does not prove that the preimage is an equivalence.

lem-coef-symmetric-family-active-slice-calculus vs lem-coef-initial-poset-slice-restriction: the existing lemma handles restriction of a slice diagram to its least vertex. The new node retains only the active-subslice reflector and the output-product equivalence, neither of which follows from a least vertex. The overlapping restriction claim was removed and the existing lemma is cited separately.

lem-coef-symmetric-family-active-slice-calculus vs lem-coef-active-operad-cocartesian-concatenation: concatenation supplies the tuple operation, not the equivalence of incoming active slices or the reflector from unrestricted incoming cones.

lem-coef-symmetric-family-inert-cone-initiality vs lem-coef-relative-limit-initial-components: the existing statement assumes components already have initial objects and transfers relative limiting cones. The new statement constructs those initial objects in the extension categories from inert cocartesian lifts and states their mapping-space property.

lem-coef-operadic-colimit-finite-amalgamation vs lem-coef-active-operad-cocartesian-concatenation: existence and cocartesian compatibility of concatenation do not assert its relative operadic universal property for a product of indexing shapes.

lem-coef-operadic-colimit-active-join-boundary vs lem-coef-infinity-relative-join-simplex-extension: the new statement tests a single operadic-colimit cone, ends at a color and requires active arrows. The existing relative-join lemma uses an ordinary colimit in a cocartesian family and has a different domain.

lem-coef-cofinal-relative-join-slice-restriction vs lem-coef-infinity-anodyne-cocones: the latter assumes a right-anodyne inclusion and gives inner-anodyne pushout joins. The new node assumes comma contractibility (in particular an active reflector) and gives strict relative slice restriction, including the dual orientation.

lem-coef-cofinal-relative-join-slice-restriction vs lem-coef-infinity-cofinal-comma-criterion: the existing node gives equivalence of coherent cocone categories and spaces and ordinary colimit invariance. It does not assert relative strict join-slice boundary lifting for an inner fibration; the new statement includes that stronger geometric assertion.

lem-coef-cofinal-relative-join-slice-restriction vs lem-coef-infinity-relative-cone-equivalence: the latter preserves universal cones under equivalences and gives exact existence for equivalent index categories. The new statement is restriction of all relative slices for non-equivalent cofinal full inclusions, not a universal-cone invariance theorem.

Before creation I searched the entire DAG by these notions and HA reference numbers and the whole blueprint with blueprint_refs.py (operadic; horn; operadic colimit; join simplex; cofinal; cocartesian horn; relative boundary; amalgamation). None states these new lemmas. There is no shared Stacks tag requiring an additional same-tag pair justification.

## Review by Q120

I read HA 3.1.2.3(B) and the full construction on pp.334-341, not only the theorem statement. The proof uses exactly the first correspondence; its n=1 branch is not needed here. I checked each proposed node against its specific source: the comparison is the actual trivial cofibration of 3.1.2.5, not a homotopy-pushout slogan; 2.4.4.6 needs cocartesian lifts of only the edge immediately before an inner missing vertex; the active reflector and the product of active input slices are the two genuine geometric claims on pp.336-337; the extension categories on pp.340-341 have initial objects represented by inert cocartesian extensions; 3.1.1.8 gives finite amalgamation; and 3.1.1.7 gives an active join-boundary filler ending at a color. The cofinal restriction statement records both slice orientations, rather than inferring either from an unrelated ordinary final-functor theorem.

For step 1 I opened the categorical-fibration and Joyal statements: they explicitly give strict lifts against injective categorical equivalences. The family definition says inert edges have equivalence edges in the simplex, so every inert edge is indeed already in the horn. Pushout and union lifting are written out, rather than treating weak equivalences as stable under arbitrary pullback.

For step 2 I opened the relative coslice left-fibration statement, the fixed-boundary join-cone mapping formula, the join-slice cocone comparison, the constant-target homotopy-pullback test, the positive-dimensional relative-initial boundary theorem and the opposite-cone statement. The mapping-fiber calculation explains exactly why a universal cone is a relative initial/final object of its slice. For the separate final-apex variant I wrote the join-boundary simplex filtration explicitly, rather than assuming that relative-final objects remain final in all coherent diagram categories. It makes no zero-dimensional existence assertion. The off-unit coslice theorem is declared as a generic tool use; it does not change the unit's mathematical route.

For step 3 the active-slice statement includes the coherent source tuples and canonical cocones, not merely a product of objects. Finite amalgamation therefore applies to the actual cone. The original colorwise condition supplies precisely its color hypotheses at coordinate 1. The empty output product is a point and is included in the finite-amalgamation statement.

Step 4 writes out the finite-pointed-map factorization and the matching, rather than putting the theorem's whole conclusion in a new lemma. The base filtration includes all lower-dimensional simplices and current-dimensional longer partners. I checked the smallest case m=2: there is no new zero-simplex, and any new actual positive-coordinate simplex has dimension at least one. A zero initial block and a zero final output set are allowed.

For step 5 the simplex-attachment node gives the categorical comparison, the reflector gives the correct cofinal direction, and the existing initial-poset lemma applies in the ACTIVE quasicategory, with its full coordinate-zero subcategory and least vertex 0. The all-monomorphism lifting in that existing statement makes the restriction a trivial Joyal fibration, and the Joyal quasicategory characterization supplies its coherent inverse. The active join-boundary lemma's final arity-one condition is supplied by closedness; its first cone comes from step 3; r>0 comes from m>=2. I checked the no-input slice and nontrivial indexing-shape cases: no terminal-active-slice hypothesis is introduced.

For step 6 I used the empty-output Segal square in both operads. The two maps to the finite-pointed mapping space are equivalences, hence the map induced by q is an equivalence. This supplies a q-final object and the last-apex boundary test of step 2; a zero-output seed cannot be treated as if it had one color projection.

For steps 7 and 8 I checked which face is missing. A neutral factorization inserts an INNER vertex; the preceding edge is strongly inert with constant simplex coordinate. The preimage lemma is applied only after pulling the family back to a full simplex, so its total category is a quasicategory. The displayed join identity keeps the missing index inner after an arbitrary initial simplex is attached. This avoids the invalid inference that categorical equivalences survive all base changes. The rank check lists deletion, composition and factor-normalization cases before using a lift.

On rereading pp.340-341 I corrected the output-pair enumeration to include actual simplices with an initial coordinate-zero block, not only simplices entirely over positive coordinates. Otherwise mixed simplices would be missed. For step 9 the inert-extension node supplies actual initial objects in each component J_i. The relative-limit-initial-components statement applies to an already specified cone, not just an unspecified existence class. The cone on the selected initial objects is made of inherited inert edges in the last vertex fiber, so both E and O output-Segal tests apply. The homotopy-pullback pasting node and the constant-source limit test give exactly the displayed q-limit square. This is a specified relative limit, not an assumption of completeness. Again r>0 is checked before the boundary test. Arity zero was removed in step 6, so the positive-output and nullary cases do not conflict.

Step 10 takes unions of maps agreeing exactly on their prior domains. It consequently retains the given base g and original horn map as literal equalities; it does not replace either by an equivalent diagram. The inert-edge test of step 1 then supplies the family-map requirement.

I read every cited node's statement when matching it to a use and copied those statements verbatim into citations.json. I tested empty joins, r=0 in the ATTACHMENT lemma (not in the universal boundary theorem), the least positive simplex dimension, zero output arity, one output, multiple outputs and a nonempty initial zero-block. No new statement restates this item or one of its clauses. Ordinary-category finality, ordinary coproduct colimits, strict Segal spines and Kan-fibration horn fillers in the search hits have the wrong kind of objects; their source files were read before recording no match. Every new node has a first phrasing, a second phrasing, a Loogle query, an actual grep and a LeanSearch result saved exactly as returned. There are no invented or retrospectively changed query records.

## Unfinished work and validation

The seven new statements are deliberately unsplit stage-1 children. No mathematical gap is postponed inside the parent proof beyond those named inputs. No attachment or Mathlib leaf was claimed. Required server validation command: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q120 lem-coef-symmetric-operadic-left-horn-filling --no-push .`. A final READY answer is given only after this command prints OK; its diagnostics are retained in the dispatcher transcript. A second reader must perform the independent source review and delivery; this worker does not push.

## Second reading by Q120

- Item statement: checked HA Theorem 3.1.2.3(B), pp.329–330, hypothesis by hypothesis; verdict faithful for (m>1), with the cocartesian-(q) specialization and exact horn restriction retained.
- Step 1: checked HA pp.334–335 against `lem-coef-cocartesian-joyal-fibration`, `lem-coef-joyal-model-structure`, and the family definition; verdict strict categorical-equivalence lifting and the inert-edge reduction are stated and used correctly.
- Step 2: checked HA pp.336–338 and 341 against the cited relative coslice, join-cone, homotopy-pullback, relative-boundary, and opposite-cone statements; verdict the mapping-fiber argument and both join orientations are explicit, including the (r>0) restriction.
- Step 3: checked HA pp.336–337 and Proposition 3.1.1.8 against the active-slice and finite-amalgamation statements; verdict the aritywise product, coherent cocones, and nullary product are correctly transferred.
- Step 4: checked HA pp.333–335, especially G(1), G(2), G(3) and their associates; verdict the semantic neutral/output matching, strong inert factorization, face exhaustion, and (M(0)=M_{Lambda^m_0}) agree, including (m=2).
- Step 5: checked HA pp.335–337 and Lemma 3.1.2.5 against the active reflector, cofinal restriction, initial-poset slice, Joyal, and active-boundary nodes; verdict active seeds attach with the required arity-one and positive-dimension hypotheses.
- Step 6: checked HA pp.337–338 against the empty-output Segal mapping square and the cited pasting and cocartesian lifting statements; verdict nullary seeds use the empty product correctly and require no color projection.
- Step 7: checked HA pp.338–339 against the rank ordering and all face cases; verdict matched neutral/output attachments have only the named exceptional faces and the stated lexicographic decrease.
- Step 8: checked HA pp.339–340 and Lemma 2.4.4.6; verdict the pulled-back missing index remains inner after each initial-block attachment, and only the preceding strongly inert edge is used.
- Step 9: checked HA pp.339–341 against the inert-extension, join-attachment, relative-limit, homotopy-pasting, and family-Segal statements; verdict output cones are already prescribed on the partial domain, preserve inherited inert edges, and give the required relative limit. The wording was corrected to say “previously constructed domain” rather than incorrectly calling this map the original (f_0).
- Step 10: checked HA pp.334–341 for compatible transfinite unions and the family-map conclusion; verdict exact overlap agreement gives the claimed global (f).
- `lem-coef-quasicategory-simplex-join-attachment`: checked HA Lemma 3.1.2.5 pp.332–333 and its opposite; verdict self-contained statement-only node, including (r=0) and empty slice.
- `lem-coef-cocartesian-inner-horn-preimage`: checked HA Lemma 2.4.4.6 p.307 and pp.339–340; verdict self-contained inner-fibration hypothesis with only the preceding cocartesian lifts.
- `lem-coef-symmetric-family-active-slice-calculus`: checked HA pp.336–337 and the family definition; verdict active reflector, aritywise slice product, coherent tuples, and (s=0) case are stated.
- `lem-coef-symmetric-family-inert-cone-initiality`: checked HA pp.340–341 and the family inert-lift axiom; verdict each component initial object and the (s=0) empty extension category are stated without extra limits.
- `lem-coef-operadic-colimit-finite-amalgamation`: checked HA Proposition 3.1.1.8 p.321 and Definition 3.1.1.2; verdict finite (including empty) product amalgamation is stated with the relative mapping-space meaning.
- `lem-coef-operadic-colimit-active-join-boundary`: checked HA Proposition 3.1.1.7 pp.319–320; verdict active join-boundary filler has the exact first-cone and arity-one hypotheses and (r>0).
- `lem-coef-cofinal-relative-join-slice-restriction`: checked HA p.336, p.341 and HTT 4.1.3.1, 4.1.1.3(4), 2.1.2.5; verdict both comma orientations and exact relative boundary lifting are included.
- New-node form: all seven nodes are statement-only, self-contained, definition-linked, TeX-escaped, source-linked, and carry five recorded searches with actual outputs; no Mathlib declaration or duplicate DAG node matches.
- Changes made: corrected the parent node’s `created.item` and group from the neighboring Q20 item to this Q120 item; corrected step 9’s partial-map wording to match the source construction; synchronized this report with those repairs. No statement was weakened or changed.
