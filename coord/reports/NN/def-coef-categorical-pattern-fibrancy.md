# Stage-1 report: def-coef-categorical-pattern-fibrancy

## Files written

- `dag/nodes/sec-six-functors/def-coef-categorical-pattern-fibrancy.json`: definition, split; no full Mathlib match. Reuses all four original dependencies and adds the existing definition `def-coef-infinity-relative-cone`. No new nodes or Mathlib leaves.
- `citations.json`: `[]`, because this definition has no proof steps.
- `report.md`: this report. `searches.jsonl` was written by the required search command.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag and for categorical patterns, pattern fibrancy/fibered objects and marked simplicial sets; there was no matching project declaration. Also checked the available Comparator directory and the upstream naming index. No master sorry declaration is treated as a finished proof.

## WANTED

WANTED: Gepner–Haugseng, *Enriched infinity-categories via nonsymmetric infinity-operads*, arXiv:1312.3178, Definitions 3.2.1 and 3.2.3, Remark 3.2.2 and Theorem 3.2.5(2), for `def-coef-categorical-pattern-fibrancy`. Read the primary source at https://arxiv.org/html/1312.3178 ; no local archived copy was found in the named literature tree. The report requests archival; no literature file was changed or downloaded.

## Corrections and scope

The original mathematical definition agrees with the source. There is no STATEMENT-DISPUTED and no changed hypothesis. Its inline left-cone description and pointwise relative-limit square duplicated notions now available in `def-coef-infinity-relative-cone`; the split refers to that existing node, whose statement specifies the join degreewise and defines relative limits by an explicit mapping-space universal property. The four conditions, including the total-space relative-limit condition (iv), are retained. The redundant pointwise square was replaced by that shared relative-limit definition, rather than leaving a second convention in this node. The pointwise interpretation was checked in Gepner–Haugseng Remark 3.1.4 and against the existing constant-test lemma `lem-coef-infinity-relative-cone-constant-test`.

Made explicit the universe of pattern objects, the larger universe containing Cat-infinity, the indexing set, maps in the marked slice, degreewise pullback, and the meaning of a cocartesian section. These are unpackings of the existing definition, not new existence or model-category assertions. This node does not assert the existence of the pattern model structure: that remains `lem-coef-categorical-pattern-model-calculus`.

This is a definition: under stages/1-dag.md §3(2), its split is the list of notions it uses, with no proof, proof dependencies or proof origin. The unit's realized fields do not change because this is not its key theorem. The inherited unit/chapter and complete blueprint ancestry are preserved.

## Not duplicates

No new node was created. Whole-DAG keyword and source-place searches found the existing pattern-model calculus and operadic model-structure nodes, which are theorems using this definition, not replacement definitions. The existing relative-cone definition is reused. `tools/blueprint_refs.py search` on `categorical pattern`, `cocartesian`, and `relative limit` returned no blueprint matches; direct searches of both the current main-20261015 and slopmaster2 blueprint text found no duplicate categorical-pattern definition. The nearest blueprint ancestor command returned `prop-coef-integral-exceptional-adjoint`, as already recorded.

## Review by NN

I read the definition against the primary source, Gepner–Haugseng Definitions 3.2.1 and 3.2.3, Remark 3.2.2, the marked-object clause of Theorem 3.2.5, and the relative-limit discussion of Remark 3.1.4. The base is a quasicategory, the marking includes all degeneracies, every edge of every specified left cone lands in the base marking, and the scaling contains all 2-simplices. I did not substitute partially scaled bases or an ordinary category of fibers.

There are no proof steps to audit under C1/C4. I instead opened and read every statement dependency. `def-cbc-enhanced-diagrams-cones` supplies universes, simplicial sets, coherent diagrams and the terminal-cone meaning of limits. `def-coef-infinity-fibrations` supplies the inner-horn condition, cocartesian edges, fibers and cocartesian lift convention used in (i) and (ii). The beginning of `lem-coef-marked-point-cartesian-model` actually defines a marked simplicial set and its marking-preserving maps; I use precisely that definitional part, not its model theorem. `def-coef-infinity-relative-cone` gives the simplicial left cone and the relative-limit notion in (iv), including the empty shape. `lem-coef-cocartesian-straightening` gives the classifying functor with values the fibers, arrows cocartesian transport and a contractible space of classification choices. It applies in (iii) to the small quasicategory K-alpha-left and the cocartesian fibration required there. Thus (iii) does not depend on arbitrarily choosing data from an unproved existence statement. The uses of the two theorem nodes as conventions are declared in split_report.tool_uses.

I checked each defining condition. (i) is exactly an inner fibration. (ii) quantifies over each marked base edge and every object of its source fiber, with source rather than target fixed, and marks exactly all such cocartesian edges. (iii) takes the actual degreewise base change along each specified cone, and requires a classifying limit diagram in Cat-infinity. It does not merely require individual limit fibers. (iv) quantifies over every section preserving all cocartesian edges of that pullback and requires its composite in X to be a relative limit over the original base C; I did not replace this by a fiberwise limit or omit it as redundant. The equality q-alpha s = id and the edge condition now explicitly define such a section.

For small cases, if the family A is empty, (iii) and (iv) are vacuous and the lift/marking conditions remain. If S contains all edges and A is empty, the condition gives precisely a cocartesian fibration with its cocartesian edges marked, matching the source's Examples 3.2.11(1). If K-alpha is empty, its left cone is a point and (iii) says its fiber is terminal in Cat-infinity; (iv) still demands the appropriate relative terminal-object condition, rather than becoming vacuous. If C is empty, the only object over it has X empty and all quantified lift/section conditions are vacuous, as expected. Degenerate markings are included throughout, and the identity cocartesian arrows are not excluded. No smallness or invertibility hypothesis is imported from an unrelated theorem.

I read the current main-20261015 ancestor proof, specifically its second paragraph computing the finite mapping-complex adjunction before the derived inverse limit, and the chapter/unit records. This definition supplies general categorical-pattern terminology for the existing marked operadic route; it replaces no unit proof step. Neither the current-source instruction nor the inherited ancestry was used to justify an SGA route.

For B1–B10, there are no new statements, invented source tags, unsearched new nodes, or alleged Mathlib leaves. The TeX is written once in JSON, and all referenced objects are introduced. For C1–C8, this is a definitional split; no uncited theorem is hidden in a proof, no proof of another node is used as an interface, and the shared definitions are named explicitly. For D1–D5, no clause was moved into a new node and no new lemma restates the item. For E1–E7, the universe, base category, cone orientation, section direction, exact marking and empty cases were checked against the source as described above; no source error was found.

Mathlib searches were made only with `/home/ubuntu/weil-launcher-nt/msearch.py NN def-coef-categorical-pattern-fibrancy`, and the seven new records in the item are copied from its actual log. The first Loogle query was malformed and is explicitly recorded as an invalid query, not as evidence of absence; I immediately repeated it successfully with `SSet.InnerFibration`. Both semantic phrasings were read. The returned inner-fibration and quasicategory declarations give only ingredients; the ordinary cocartesian-arrow declarations have ordinary-category hypotheses, and general fibrant-object declarations presume a model structure. None states this definition. I inspected the source at Quasicategory/Basic.lean:40–59, InnerFibration.lean:61–99, CategoryTheory/FiberedCategory/Cocartesian.lean:46–74, SimplicialSet/CategoryWithFibrations.lean:44–79, ModelCategory/IsCofibrant.lean:78–87, StrictBicategory.lean:48–61 and SimplicialSet/Coskeletal.lean:61–79 to verify those mismatches.

## Unfinished work

No mathematical part of this one-level definitional split remains. Existing dependency nodes retain their own work states. The server-side srvcheck review_split run returned `PASS; 0 new nodes`. Full validation uses `python3 /home/ubuntu/weil-launcher-nt/deliver.py NN def-coef-categorical-pattern-fibrancy --no-push .`; only an OK dry run authorizes the READY handoff. No delivery push is requested or performed.

## Second reading by NN

- Item statement, categorical-pattern data: checked against Gepner–Haugseng Definition 3.2.1 (the infinity-category base, degenerate-inclusive marking, cone family, and marked edges); verdict: agrees clause by clause.
- Item statement, scaling convention: checked against Remark 3.2.2 (the restricted convention scales every 2-simplex); verdict: the explicit all-2-simplices convention is faithful.
- Item statement, fibrancy condition (i): checked against Definition 3.2.3(1) and `def-coef-infinity-fibrations`; verdict: inner-fibration condition is present with the stated base and total map.
- Item statement, fibrancy condition (ii): checked against Definition 3.2.3(2) and Theorem 3.2.5(2); verdict: lifts over every marked base edge and the exact marked-edge characterization are both present.
- Item statement, fibrancy condition (iii): checked against Definition 3.2.3(3), `def-coef-infinity-relative-cone`, and `lem-coef-cocartesian-straightening`; verdict: degreewise pullback, cocartesian fibration, classifying functor, and limit-diagram requirement agree.
- Item statement, fibrancy condition (iv): checked against Definition 3.2.3(4) and the relative-limit definition; verdict: every cocartesian section and its composite into the total space are required to be relative limit diagrams.
- Item statement, morphisms and size conventions: checked against the marked slice described before Definition 3.2.1 and the project universe conventions; verdict: all objects and maps used are introduced self-containedly.
- Small cases (empty index family, empty cone shape, empty base, and degenerate markings): checked directly; verdict: no clause becomes incorrectly stronger or vacuous.
- New nodes: none; the file is the item definition itself, so there are no new-node statements or proof steps to audit.
- Existing dependencies: opened and checked `def-cbc-enhanced-diagrams-cones`, `def-coef-infinity-fibrations`, `lem-coef-marked-point-cartesian-model`, `def-coef-infinity-relative-cone`, and `lem-coef-cocartesian-straightening`; verdict: each cited notion is supplied by its statement and no dependency proof is being used.
- Duplicate and Mathlib searches: repeated whole-DAG/blueprint searches and the recorded LeanSearch, LeanFinder, Loogle, and grep searches; verdict: no duplicate categorical-pattern definition or full Mathlib match.

Changes made during this second reading: none. The definition already matches the source and its dependency interfaces; the delivery report now records each clause-level check explicitly.
