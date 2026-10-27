# Stage-1 report: lem-sfb-flat-fibre-projective-etale-cover

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-fibre-projective-etale-cover.json`: split the unchanged statement of Stacks Tag 05KW into seven steps. No new nodes, no new Mathlib leaves. The item is not a Mathlib leaf.
- `citations.json`: one verbatim statement quotation for every cited node at every proof step.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint identifier, fibre/projective/etale terminology, the Stacks label and tags found no declaration asserting this entire statement. Projective-module lifting and smooth-chart declarations address different statements; sorry declarations were not counted as finished proofs.

## WANTED

None. All source passages used are present in `literature/stacks-project/`.

## Corrections and scope

The item was statement-only; its statement agrees clause by clause with Tag 05KW, including finite presentation of the morphism and sheaf, flatness at every point of the specified fibre, an elementary base neighbourhood, affine total space and base, etaleness, coverage of the whole fibre and projectivity over the base without a rank restriction. No statement correction or target change is necessary.

The source proof chooses a finite cover from images of the whole etale charts intersected with the fibre, then asserts that coverage survives the common pointed base change. I made the intermediate opens more precise: use the images of the distinguished fibres `(Y_x)_{s_x} -> X_s`. These maps are etale by base change and cancellation, contain the selected points, and remain the identical fibre maps after refinement. This avoids assuming that other points of `S_x` over `s` survive a refinement pointed at `s_x`. This is an expansion of the intended proof, not a replacement of its route or of its statement.

The inherited `blueprint.from.node` is null. Running `python3 tools/blueprint_refs.py ancestor lem-sfb-flat-fibre-projective-etale-cover` prints `None`; its created.item chain ends at a Lean module rather than a mechanically imported node. I retained that value and the full existing explicit provenance. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its proof: the compactification/direct-image route is the inherited ancestor context. No chapter or unit changes were made.

## Searches and reuse

Before writing the split I searched the entire DAG by Stacks tags 05KW, 05ID, 057B, 05A3, 02GO, 02GW and the module/affine/coproduct/refinement concepts; I also used `tools/blueprint_refs.py search` for projectivity, etale geometry and narrower phrases (`projective etale`, `flat along`, `05KW`, `elementary etale neighbourhoods`). The narrow blueprint searches did not identify another statement of the item. The pointwise chart node `lem-sfb-flat-point-projective-etale-source-chart` already supplies exactly 05ID, so I reused it rather than creating a new pointwise input.

All new Mathlib queries were run through the required `msearch.py Q70 lem-sfb-flat-fibre-projective-etale-cover` command and recorded in `searches.jsonl`. I read the returned hits. LeanFinder returns standard smooth charts and the etale locus, not a projective affine cover of an arbitrary prescribed flat fibre. LeanSearch returns `Module.Flat.projective_of_finitePresentation`, which assumes finite presentation over the base ring; that hypothesis is absent for the section module here. The Loogle query `"IsEtale", "Projective"` and the algebraic-geometry grep returned no hits. The more algebraic LeanFinder wording returned direct sums/products of projectives, but the finite-product lifting proof is elementary and is written in Step 7. Arbitrary projective scalar extension already has a Mathlib leaf, `lem-trf-local-projective-tensor-base-change`, which is cited. Earlier Q56 searches in the item were preserved with their results and verdicts.

## Not duplicates

No new nodes. The finite elementary-neighbourhood cone, fibre-product reassociation and finite-product lifting argument are written as elementary steps from the cited definitions and results. None was turned into a new node. Existing affine base-change, coproduct and projectivity nodes are reused at their actual strength.

## Review by Q70

I read Stacks `flat.tex`, Tag 05KW (`lemma-finite-presentation-flat-along-fibre`) including its entire proof, and its pointwise input Tag 05ID (`proposition-finite-presentation-flat-at-point`). I compared the latter with the full statement of `lem-sfb-flat-point-projective-etale-source-chart`: it supplies both pointed etale maps, both affine schemes, the commuting square, the image point and the projectivity over the correct base ring. Step 1 therefore uses its statement, not any construction hidden in its proof. Finite presentation of f is stronger than its local finite presentation hypothesis; flatness is available separately at every chosen x.

For Step 2 I read the statements of the scheme etale base-change, cancellation and open-map nodes. They supply exactly the properties of `h_x` and its distinguished-fibre base change. I read `def-pc-fibre-product` and `def-pc-scheme-fibre` to check the targets and residue-field identification, then the quasi-compact base-change and quasi-compact-space nodes: f is quasi-compact by the finite-presentation hypothesis, its base change is quasi-compact, and its affine field base makes the fibre quasi-compact. This step does not assume that the fibre is affine or that X or S is separated. The distinguished point y_x proves that the open V_x contains x.

For Step 3 I read `more-morphisms.tex`, Tag 057B (`lemma-elementary-etale-neighbourhoods`) and the existing fibre-product, residue-field, spectrum, affine-basis and elementary-neighbourhood definition statements. The common finite cone is written out: finite pullbacks of the given etale maps, the point induced by the compatible maps from Spec k(s), its residue field proved equal to k(s), and an affine open containing it. The projection maps are etale by the cited base-change and composition statements, including after the affine open shrink. The elementary-neighbourhood definition is cited only for its definition; it is not used as a cofilteredness theorem. The empty index set is handled separately by an affine neighbourhood of s. No separatedness of S is needed, because the finite fibre product need not itself be affine.

For Step 4 I read `lem-sbc-finite-affine-tensor-base-change`, whose arbitrary B-algebra statement includes the singleton affine family: it identifies each Z_i with a spectrum. This is a generic tool, not a change to the unit route. I read both coproduct statements used: `lem-weil-pbc-scheme-coproduct-family` supplies disjoint open summands, covering and the universal maps; `lem-weil-pbc-finite-affine-coproduct-spectrum` makes the finite coproduct affine. The finite-etale-coproduct statement supplies etaleness of g. The base-change input is u_i, already proved etale, so no unsupported etaleness of Y_i -> S_i is assumed. Equality fg=ep is checked on summands.

For Step 5 I checked the two projections of the claimed iterated-pullback identification directly against `def-pc-fibre-product`. The pointed maps give k(s_i) = k(s') over k(s), so this identification preserves the map to X and hence really preserves the images V_i used in the finite cover. It does not assert that all of g_i(Y_i) intersected with X_s survives. This is the principal source-proof clarification made here.

For Step 6 I read `modules.tex` Tag 01BG (`lemma-pullback-quasi-coherent`), `schemes.tex` Tag 01I9 (`lemma-widetilde-pullback`), and `coherent.tex` Tag 02KG (`lemma-affine-base-change`), including its affine tensor computation. I read the entire statements of the cited pullback, quasi-coherence and affine-section nodes. In the section theorem take X=W=Y_i and W'=Z_i, with the affine S_i as its ring base; its statement expressly needs no flatness, separatedness or nonemptiness. The rings R_i are the actual rings of the S_i, not of X or Y_i. The scalar-extension leaf states projectivity for arbitrary projective modules. The source Tag 05A3 (`lemma-ascend-properties-modules`), clause (4), matches this without finite generation.

For Step 7 I checked the disjointness/covering clauses of the coproduct node and used only the sheaf gluing axiom for the product description of sections. I read the projective-module definition's lifting characterization and wrote the finite-product lifting map explicitly. This makes the finite sum argument elementary and handles the empty index set with the zero module. In the non-finite-rank test f:A^1_k -> Spec k and F=O, the ring of sections k[t] is allowed to be infinite-dimensional over k; the proof never invokes finite presentation over the base. I also checked F=0, empty fibre, a singleton chart, a nonclosed s, non-Noetherian bases and a nonseparated S. All arguments use only the stated hypotheses. Each elementary step stays below 2000 characters; no long step hides a comparison lemma. Every citation quote is copied verbatim from the exact node statement.

## Unfinished work

None in the one-level split. Its cited unsplit inputs remain their existing DAG items. No Lean was written and no compiler, Lake or build tool was run.
