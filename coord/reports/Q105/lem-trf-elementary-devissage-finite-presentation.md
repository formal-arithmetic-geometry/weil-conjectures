Files written:

- `dag/nodes/sec-trace-formula/lem-trf-elementary-devissage-finite-presentation.json` — split statement; Mathlib searches found no exact match.
- `lem-trf-finite-morphism-finite-presentation` — statement-only lemma; Mathlib searches found no exact match.
- `lem-trf-etale-module-finite-presentation-local` — statement-only lemma; Mathlib searches found no exact match.
- `lem-trf-finite-pushforward-module-finite-presentation` — statement-only lemma; Mathlib searches found no exact match.
- `lem-trf-faithfully-flat-module-finite-presentation-descent` — statement-only lemma; Mathlib searches found no exact match.
- `lem-trf-finite-extension-module-finite-presentation` — statement-only lemma; Mathlib searches found no exact match.

Attachments: none.

WANTED: none.

## Not duplicates

- `lem-trf-finite-morphism-finite-presentation` vs existing `lem-weil-pbc-proper-fp-permanence`: the new node specializes to a finite morphism and concludes finite presentation from local finite presentation; the existing node concerns properness and permanence of finite presentation under composition/base change.
- `lem-trf-etale-module-finite-presentation-local` vs existing `lem-weil-pbc-etale-morphism-open-map`: the new node transfers module finite presentation across an etale neighbourhood; the existing node only states that etale maps are open.
- `lem-trf-finite-pushforward-module-finite-presentation` vs existing `lem-pc-f3-finite-pushforward-finite-type`: the new node gives finite presentation equivalence and stalk comparison for a finite map with singleton fibre; the existing node gives only finite type of finite pushforward.
- `lem-trf-faithfully-flat-module-finite-presentation-descent` vs existing `lem-weil-pbc-faithfully-flat-descent-finite-module`: the new node descends finite presentation along a faithfully flat local ring map; the existing node descends finite generation only.
- `lem-trf-finite-extension-module-finite-presentation` vs existing `lem-weil-pbc-finite-algebra-presentation-module-presentation`: the new node compares arbitrary module finite presentation over a finite finitely presented extension in both directions; the existing node only compares the extension algebra itself as a module.

## Review by Q105

I read the imported item and the complete proof of Stacks Tag 057T in `literature/stacks-project/flat.tex`, including both neighbourhood and stalkwise assertions. I checked the source statement against every hypothesis in the node: the local finite-presentation assumption on $f$, finite presentation of $i$, finiteness and singleton marked fibre of $\pi$, and the residue-field and etale neighbourhood conditions. I also read the statements of all five new nodes and their cited Stacks passages. Step 1 uses the finite-map finite-presentation lemma and verifies that the source's composition argument supplies local finite presentation of $\pi$. Step 2 uses the etale-local module finite-presentation statement and explicitly records openness of $g$ and faithfully flat descent. Step 3 applies the finite-pushforward statement separately to $i$ and $\pi$, checking that $i$ is finite finitely presented and that $\pi^{-1}(\{y'\})=\{z'\}$. Step 4 checks the three local ring maps: the etale stalk map is faithfully flat, the closed immersion map is finite and finitely presented, and the finite singleton-fibre map is finite and finitely presented; it then applies the two ring-module comparison nodes and the stalk clause of the pushforward node. I searched the whole DAG and blueprint for each Stacks tag and for the key phrases; the duplicate distinctions above record the only nearby statements. I ran LeanFinder, Loogle, grep, and LeanSearch for the item and every new node and recorded the actual results in their search logs and JSON fields. No source error or statement correction was needed.

What was wrong or incomplete in the imported node: it had no proof split and no proof dependencies. The split now records the full Tag 057T route and isolates only the generic lemmas needed by that route.

What I could not finish: no Lean code or compiler checks were run, as required for stage 1.
- `lem-trf-etale-module-finite-presentation-local` vs `lem-trf-elementary-devissage-finite-presentation`: the new node is the generic etale-local module finite-presentation equivalence; the item additionally includes finite pushforward, stalkwise clauses, and the full elementary devissage hypotheses.
- `lem-trf-etale-module-finite-presentation-local` vs `lem-pc-flat-module-descent-affine-charts`: the new node concerns arbitrary etale neighbourhoods and module finite presentation; the existing node concerns finite affine chart data in an inverse-limit flatness argument.
- `lem-trf-etale-module-finite-presentation-local` vs `lem-pc-split-top-differential-cancellation-properties`: the new node transfers finite presentation across etale maps; the existing node concerns cancellation properties of split maps and differentials.
- `lem-trf-etale-module-finite-presentation-local` vs `lem-weil-pbc-coherent-affine-sections-finite`: the new node is etale-local; the existing node concerns finite sections on affine schemes.
- `lem-trf-etale-module-finite-presentation-local` vs `lem-weil-pbc-finite-presentation-affine-sections`: the new node is descent across etale neighbourhoods; the existing node only gives finite presentation of sections on an affine open.
- `lem-trf-etale-module-finite-presentation-local` vs `lem-weil-pbc-quasi-coherent-finite-type-affine`: the new node concerns finite presentation, while the existing node concerns finite type and quasi-coherence on affines.
- `lem-trf-etale-module-finite-presentation-local` vs `lem-sc-etale-local-ring-faithfully-flat-descent`: the new node is a sheaf neighbourhood equivalence; the existing node is a pointwise local-ring faithful-flatness statement.
- `lem-trf-etale-module-finite-presentation-local` vs `lem-galois-fpqc-descend-etale`: the new node concerns module finite presentation; the existing node descends etaleness of morphisms.
- `lem-trf-etale-module-finite-presentation-local` vs `lem-weil-pbc-fpqc-descend-flat`: the new node concerns module finite presentation; the existing node descends flatness of morphisms.
- `lem-trf-etale-module-finite-presentation-local` vs `lem-weil-pbc-faithfully-flat-descent-finite-module`: the new node descends finite presentation, while the existing node descends finite generation.
- `lem-trf-etale-module-finite-presentation-local` vs `lem-weil-pbc-formal-glueing-finite-modules`: the new node is etale-local finite presentation; the existing node is finite-module formal glueing.
- `lem-trf-etale-module-finite-presentation-local` vs `lem-trf-finite-presentation-module-descent-flat-local`: the new node is a general etale neighbourhood equivalence; the existing node is a specialized flat finite-type local theorem.
- `lem-trf-faithfully-flat-module-finite-presentation-descent` vs `lem-pc-flat-module-descent-affine-charts`: the new node is the local faithfully-flat module finite-presentation descent implication; the existing node is an inverse-limit affine-chart flatness construction.
- `lem-trf-faithfully-flat-module-finite-presentation-descent` vs `lem-pc-split-top-differential-cancellation-properties`: the new node is module descent; the existing node concerns split differential maps.
- `lem-trf-faithfully-flat-module-finite-presentation-descent` vs `lem-weil-pbc-coherent-affine-sections-finite`: the new node is faithful-flat descent; the existing node concerns coherent affine sections.
- `lem-trf-faithfully-flat-module-finite-presentation-descent` vs `lem-weil-pbc-finite-presentation-affine-sections`: the new node descends a module property; the existing node only computes affine sections.
- `lem-trf-faithfully-flat-module-finite-presentation-descent` vs `lem-weil-pbc-quasi-coherent-finite-type-affine`: the new node concerns finite presentation under a ring map; the existing node concerns finite type affine modules.
- `lem-trf-faithfully-flat-module-finite-presentation-descent` vs `lem-weil-pbc-formal-glueing-finite-modules`: the new node is a local descent criterion; the existing node is formal glueing of finite modules.
- `lem-trf-faithfully-flat-module-finite-presentation-descent` vs `lem-trf-finite-presentation-module-descent-flat-local`: the new node applies to any module under faithfully flat local base change; the existing node assumes a finite module over a finitely presented algebra and flatness at a point.
- `lem-trf-finite-extension-module-finite-presentation` vs `lem-weil-pbc-integral-finite-presentation-finite`: the new node compares arbitrary modules over a finite finitely presented extension; the existing node only turns an integral finitely presented algebra into a finite module.
- `lem-trf-finite-extension-module-finite-presentation` vs `lem-weil-pbc-zariski-pair-flat-integral-isomorphism`: the new node is a module finite-presentation equivalence; the existing node proves an integral flat ring map is an isomorphism under a Zariski-pair hypothesis.
- `lem-trf-finite-morphism-finite-presentation` vs `lem-trf-elementary-devissage-finite-presentation`: the new node is the standalone geometric implication for finite maps; the item includes it as one step among the full module equivalences.
- `lem-trf-finite-morphism-finite-presentation` vs `lem-weil-pbc-finite-coproduct-lfp-qcqs`: the new node uses finiteness plus local finite presentation; the existing node treats finite coproducts and local finite-presentation/quasi-compact hypotheses.
- `lem-trf-finite-morphism-finite-presentation` vs `lem-nagata-qc-open-basechanged-affine-chart-fp`: the new node is a global finite-map implication; the existing node concerns a quasi-compact open in a Nagata base-change chart.
- `lem-trf-finite-morphism-finite-presentation` vs `lem-weil-pbc-affine-chart-directed-ring-model`: the new node is a morphism property; the existing node constructs directed affine ring models.
- `lem-trf-finite-morphism-finite-presentation` vs `lem-weil-pbc-affine-chart-tensor-comparison`: the new node concludes finite presentation for a finite map; the existing node compares affine tensor-product charts.
- `lem-trf-finite-morphism-finite-presentation` vs `lem-weil-pbc-lfp-affine-opens-finite-presentation`: the new node adds the finite-morphism global conclusion; the existing node is the affine-open local criterion.
- `lem-trf-finite-morphism-finite-presentation` vs `lem-sbc-locally-finite-presentation-composition`: the new node uses finiteness to upgrade local finite presentation; the existing node only gives composition stability of local finite presentation.
- `lem-trf-finite-pushforward-module-finite-presentation` vs `lem-trf-elementary-devissage-finite-presentation`: the new node is the generic finite-pushforward comparison; the item combines it with etale pullback and the devissage data.
- `lem-trf-finite-pushforward-module-finite-presentation` vs `lem-weil-pbc-faithfully-flat-descent-finite-module`: the new node concerns finite presentation and singleton fibres; the existing node concerns finite generation under faithful flatness.
- `lem-trf-finite-pushforward-module-finite-presentation` vs `lem-weil-pbc-formal-glueing-finite-modules`: the new node compares sheaf finite presentation under finite pushforward; the existing node is formal glueing for finite modules.
- `lem-trf-finite-pushforward-module-finite-presentation` vs `lem-trf-finite-presentation-module-descent-flat-local`: the new node is a finite-morphism pushforward/stalk equivalence; the existing node is a flat local finite-type theorem.
- `lem-trf-finite-pushforward-module-finite-presentation` vs `lem-pc-finite-affine-cech-model-perfect`: the new node is an elementary finite-map module comparison; the existing node constructs affine Cech models for perfect objects.
- `lem-trf-finite-pushforward-module-finite-presentation` vs `lem-pc-perfect-of-open-pullbacks`: the new node concerns arbitrary quasi-coherent modules; the existing node concerns perfectness under open pullback.
- `lem-trf-finite-pushforward-module-finite-presentation` vs `lem-pc-proper-flat-affine-cech-perfect-model`: the new node is finite pushforward finite presentation; the existing node is a proper-flat Cech perfect model.
- `lem-trf-finite-pushforward-module-finite-presentation` vs `lem-pc-proper-flat-bounded-presentation-comparison-core`: the new node has a singleton-fibre finite-map hypothesis; the existing node compares bounded proper-flat presentations.
- `lem-trf-finite-pushforward-module-finite-presentation` vs `lem-pc-proper-flat-bounded-presentation-model`: the new node is a local finite-map module equivalence; the existing node constructs a bounded proper-flat model.
- `lem-trf-finite-pushforward-module-finite-presentation` vs `lem-pc-proper-flat-bounded-presentation-structural-core`: the new node is module finite presentation under finite pushforward; the existing node supplies structural proper-flat bounded-presentation data.
- `lem-trf-finite-pushforward-module-finite-presentation` vs `lem-pc-proper-flat-cech-model`: the new node is independent of properness and Cech constructions; the existing node constructs a proper-flat Cech model.
- `lem-trf-finite-pushforward-module-finite-presentation` vs `lem-pc-proper-flat-cohomology-model-properties`: the new node concerns finite pushforward and stalks; the existing node concerns cohomological properties of proper-flat models.
