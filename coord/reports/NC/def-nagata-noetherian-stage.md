1. Files written:

- `dag/nodes/sec-nagata-compactification/def-nagata-noetherian-stage.json` — definition, no new Mathlib leaves.

2. Attachments: none.

3. WANTED: none.

4. The imported node is a definition-only item whose blueprint status explicitly says that this stage-by-stage bookkeeping is bypassed by the direct Noetherian approximation and finite-presentation descent route. I retained the statement and its existing dependency on `def-nagata-affine-gluing-valid-stage`, set the node to `split`, and added the required blueprint and split-report metadata. The source statement has no Lean module/declaration to attach.

5. What I could not finish: no mathematical proof or Lean implementation is supplied because the blueprint marks this construction as bypassed; no additional DAG node is required.

## Review by NC

I read the item node, its blueprint source `literature/blueprint/master/blueprint/sec-nagata-compactification/sk-prop-nagata-sketch-approximation/def-nagata-noetherian-stage.md`, the unit `sk-prop-nagata-sketch-approximation`, the chapter record, and the cited `def-nagata-affine-gluing-valid-stage` node. The cited dependency supplies the finite stage and the gluing datum named by the definition. I searched the whole Lean source for the item tag and its defining concepts; no declaration under `WeilConjectures/` defines this custom `S_{\\lambda}` stage. The source instead contains the replacement declarations `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation` and `AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`, matching the blueprint bypass note. I also searched the blueprint for duplicate statements and found none. Since this definition has no proof steps and creates no new node, there are no step citations requiring `citations.json`; the only dependency is recorded in `stmt_deps` as imported.


## Second reading by NC

- Item statement: compared both sentences of blueprint order 338, its unit's finite-cover gluing sentence, and Stacks 01JA (`section-glueing-schemes`), 01JB (`lemma-glue`), 01JC (`lemma-glue-schemes`) in `literature/stacks-project/schemes.tex`: same selected stage and all finite refinements satisfying the gluing equations; repaired the unspecified inputs and construction dependencies.
- Proof steps: none, correctly, because this item defines a scheme rather than asserting its finite-type or transition properties. Those assertions remain in `lemma-nagata-glue-noetherian-stage`; no assertion is silently built into the definition.
- Definition input `def-nagata-finite-affine-gluing-presentation`: read its full statement; it supplies the finite affine presentation and the qcqs setting. The new opening explicitly retains that presentation rather than referring to an unintroduced $S$.
- Definition input `def-nagata-affine-gluing-coefficient-stage`: read its full statement; it supplies the finite coefficient algebras, selected basic opens and raw overlap maps, not a glued scheme. Explicitly named this input.
- Definition input `def-nagata-affine-gluing-valid-stage`: read its full statement; it supplies the chosen stage and transported raw datum, not the theorem that it satisfies all gluing axioms. Kept this dependency and separated its role from validity.
- Well-definedness `lemma-nagata-affine-gluing-identities-eventually`: read its statement, not its proof; it supplies open preservation, inverse maps, identity and triple-cocycle equations at the selected stage. Added it as a statement dependency, not a new theorem or a circular property of $S_\lambda$.
- Construction `lem-weil-pbc-glue-schemes`: read its whole statement and Stacks 01JA/01JB/01JC; the charts, whole-overlap opens and transition isomorphisms satisfy precisely its input conditions. Mathlib `AlgebraicGeometry/Gluing.lean` lines 91, 129–160, 163–203 supplies the actual construction, chart maps, open cover and overlap compatibility. Added this existing Mathlib leaf; no new gluing node is warranted.
- Definition notion `def-pc-scheme`: the scheme notion used by the existing gluing leaf is now cited directly; all stage-specific notions have their defining nodes listed.
- New nodes: none; B1–B7, new-node duplicate checks and second-reader searches per new node are therefore vacuous. Independently searched all blueprint nodes with `tools/blueprint_refs.py search gluing`, and DAG occurrences of gluing, GlueData.glued, 01JA/01JC: generic gluing already has the leaf above, while no other blueprint node defines these custom coefficient stages. `same_as: []` remains correct.
- Independent Mathlib searches: ran msearch Loogle for `AlgebraicGeometry.Scheme.GlueData.glued`, grep for `def glued|abbrev glued|structure GlueData`, and LeanFinder for gluing a finite family of affine schemes along opens with cocycles. All succeeded, returning generic GlueData/glued; the actual results are in `searches.jsonl` and the item records them. This generic constructor does not define the custom coefficient-stage data, so the item itself is not relabelled a Mathlib leaf.
- Lean attachment check: searched the item id and approximation names throughout slopmaster2 `WeilConjectures/` and `Comparator/`, and read the generic gluing source. Neither replacement approximation theorem states this particular definition; no Lean attachment is made, and no master sorry declaration is treated as finished.
- Edge cases: an empty chart set glues to the empty scheme; a zero coefficient ring contributes an empty affine chart; a single chart with its identity overlap glues back to that affine scheme; for a field scheme with one selected coefficient chart this gives that chart, not necessarily the entire field scheme at a finite stage. The definition imposes no nonemptiness, nonzero-ring, separatedness or affine-intersection hypothesis. Whole overlaps are unions of basic opens and need not be affine.
- Citations: there are no proof-step citations, so `citations.json = []` is still exact; every construction dependency is cited in the definition and listed in `stmt_deps`.
- Downstream check: read `lemma-nagata-valid-refinements-directed`, `def-nagata-noetherian-inverse-system`, and `lemma-nagata-glue-noetherian-stage`. The same $S_\lambda$ is retained for every valid finite refinement; their statements are unaffected, and no edge back from the new dependencies to this item is introduced.

Changes and reasons:

1. STATEMENT-DISPUTED (construction interface): the imported definition supplies only a raw datum and free stage symbols. `Scheme.GlueData.glued` requires a `Scheme.GlueData`, whose type includes open immersions and gluing axioms; it cannot be applied to the raw datum without those proofs. Made the presentation and coefficient-stage inputs explicit, spelled out the whole-overlap axioms already intended by “the same finite equations”, and named the existing validity lemma. This repairs the typing gap without changing the intended scheme or adding a new hypothesis on $S$.
2. Named the existing scheme-gluing leaf and constructor instead of leaving “gluing” as an unrecorded operation; no arbitrary scheme is selected from a postponed existence proof. The generic constructor is used on the prescribed datum.
3. Corrected `split_report`: a blueprint bypass note is historical context, not an argument that this definition needs no gluing machinery. The split follows its unit's finite-stage route and leaves the first worker's report and `## Review by NC` intact as history.
4. Added actual independent searches and this second reading; introduced no nodes, proof steps or Lean files. The existing leaf is reused, so this delivery creates zero Mathlib leaves.

Validation: all six statement dependencies exist and are unmerged; an independent traversal found no path from them back to the item. JSON, single-escaped TeX and empty proof fields passed. Required dry run `python3 /home/ubuntu/weil-launcher-nt/deliver.py NC def-nagata-noetherian-stage --no-push` printed `OK (not pushed)` at `77efb427f6`, with preflight passed. No compiler, Lake, or Lean build was run.
