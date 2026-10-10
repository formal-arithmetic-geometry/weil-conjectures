# Worker report: lem-pc-module-pullback-adjunction

## Files written

- `dag/nodes/sec-abelian-varieties/lem-pc-module-pullback-adjunction.json`: split into the two Hom bijections of Stacks 0096 and the calculation identifying the resulting pushforward module action with restriction along `g^sharp`.
- `dag/nodes/sec-abelian-varieties/lem-pc-module-change-of-rings-adjunction.json`: new unsplit statement, Stacks 008A; no exact Mathlib match for the sheafified tensor formula. Mathlib's single-ring `ModuleCat.extendRestrictScalarsAdj` is at `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:880`; `SheafOfModules.restrictScalars` at `Mathlib/Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean:35` supplies only restriction.
- `dag/nodes/sec-abelian-varieties/lem-pc-module-inverse-image-adjunction.json`: new unsplit statement, Stacks 008Y with 008X; no exact Mathlib match for the inverse-image module structure. `SheafOfModules.pullback` and its abstract adjunction are at `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:53,60`; the sheafification construction is at line 79.
- This report.

## Attachments

None. Exact `grep -rn '(blueprint: lem-pc-module-pullback-adjunction)' /home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and concept searches found uses of the abstract Mathlib adjunction, but no source declaration stating this tensor-formula adjunction. The item's `lean_audit.slopmaster2.state` is `none`; no sorry-map entry needed checking.

## WANTED

None. I read `/tmp/stacks-project/sheaves.tex` at `lemma-adjointness-tensor-restrict` (008A, line 1916), `lemma-pullback-module` (008X, line 2896), `lemma-adjoint-push-pull-modules` (008Y, line 2933), `definition-pushforward` (0095, line 3116), and `lemma-adjoint-pullback-pushforward-modules` (0096, line 3156). The tag-label pairs are in `/tmp/stacks-project/tags/tags`.

## Mathematical check

The item and Stacks 0096 both assume only a morphism of ringed spaces and module sheaves; the scheme assumption of the item is stronger. Step 1 applies 008A to `g^{-1} O_Y -> O_X`. Step 2 applies 008Y to the restriction of `F` to `g^{-1} O_Y`. Step 3 checks on each open `V` that the scalar action is `rho_{g^{-1}V}(eta_V(a)) s = g^sharp_V(a) s`; this is the action in 0095. Naturality follows from the naturality clauses of the two cited bijections and the sectionwise identity. For the zero module, the empty space, and the identity morphism, the same constructions and equalities apply without a flatness or quasi-coherence condition.

The children state strictly smaller general lemmas, each with self-contained objects and hypotheses, no proof sketch, the exact Stacks tag and label, definition citations, and three Mathlib search kinds. DAG and whole-blueprint searches by the tags and concepts found no identical blueprint node. The existing etale-site `lem-weil-pbc-inverse-image-module-adjunction` has a different site and cannot establish the Zariski statement as written. No statement error or omitted source hypothesis was found. The two children remain unsplit for later items.

Lead correction C4: `def-pc-scheme` alone does not state the section maps `g^sharp_V`. I added `def-weil-locally-ringed-space-morphism` to the statement and to steps 1 and 3. Its statement supplies `g^sharp : O_Y -> g_* O_X` and its component maps, and says a scheme morphism gives such a locally ringed space morphism. `def-weil-pbc-topological-inverse-image` supplies the ring-sheaf inverse-image/direct-image adjunction and its unit, so the equality `rho_{g^{-1}V} (eta_V(a)) = g^sharp_V(a)` in step 3 is the defining adjunct equation. The same inverse-image definition states the direct-image sections used there.

## Validation

- `python3 tools/review_split.py lem-pc-module-pullback-adjunction`: PASS, two new nodes. It notes the unit has no realization recorded; this item is not its key node.
- `python3 tools/check_dag.py`: 0 cycles and 0 self-loops; exit 1 for 7 existing reach and 11 existing route findings in unrelated proper-base-change nodes.
- All three edited JSON nodes parse. No Lean code was written or built; no commit or push was made.

## Review by C1

I read Stacks `sheaves.tex` Tag 0096 (`lemma-adjoint-pullback-pushforward-modules`) against the unchanged item's tensor-formula statement. The source assumes a morphism of ringed spaces; the item's scheme morphism is a specialization, with no flatness or quasi-coherence added. I also read Tag 008A (`lemma-adjointness-tensor-restrict`), Tag 008Y (`lemma-adjoint-push-pull-modules`), Tag 008X (`lemma-pullback-module`), and Definition 0095 (`definition-pushforward`). The two new unsplit nodes state 008A and 008Y separately, each with its own space, ring sheaves, module hypotheses, naturality, source tag and label. Their statements contain no proof sketch or reference to an unnamed object. The worker's DAG and blueprint searches found no identical node. The Mathlib locations in their search records concern a single-ring change of scalars and an abstract sheaf pullback adjunction; neither states the sheafified tensor formula as written, so neither child is a Mathlib leaf.

In step 1, `def-pur-sheaf-tensor-product` supplies the sheafified tensor and `lem-pc-module-change-of-rings-adjunction` supplies exactly the displayed first Hom bijection, with `rho : g^{-1} O_Y -> O_X`. I opened `def-weil-locally-ringed-space-morphism` and `def-weil-pbc-topological-inverse-image`: together they provide `g^sharp` and its inverse-image adjunct. Step 2 substitutes `g`, `O_Y`, `G`, and `F_0` into the statement of the inverse-image module adjunction, including the unit action on the pushforward. Step 3 computes that action on each open `V`; the adjunct equation `rho(eta(a)) = g^sharp_V(a)` identifies it with the pushforward action in the item statement. Naturality of the composite follows from the two cited natural bijections and the identity on the section groups. This is the actual final step of Stacks 0096, not a restatement of its conclusion.

I sent the worker back under delivery-errors C4 because the first draft cited `def-pc-scheme` alone for the section maps of `g^sharp`, which that node does not state. The corrected statement and steps cite `def-weil-locally-ringed-space-morphism`; its statement explicitly defines those maps and says scheme morphisms have that structure. I checked the zero module, empty space and identity morphism: tensor restriction and inverse-image adjunction still apply, with no hidden nonempty or finite-type hypothesis. The new nodes are strictly smaller, statement-only, and their dependency graph is acyclic. The final files and cited sources were checked against delivery-errors A-F.
