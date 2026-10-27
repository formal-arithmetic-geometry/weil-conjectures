## Worker report

Repair of the re-split return dated 2026-10-22. The sandbox initially contained only .brief files, with no node, report, citations or search log to continue. I copied the current live node, including its reviewed ten-step proof, source, previous searches and Lean records. No git command ran in the shared repository. The statement is unchanged byte for byte. All writes are in this item's sandbox; no Lean was written or compiled.

## Files written

- dag/nodes/sec-six-functors-basics/det-lem-stratified-lattice-scheme.json: item, split; a short assembly of four independent lemmas and the existing pair-sheaf classification.
- lem-sfb-embedded-lattice-coefficient-comparison: statement, unsplit, no Mathlib match. Coefficient realization, localization versus tensor, embedded images and restriction-compatible pair comparison; old steps 1–2, without repeating the coset-classification theorem.
- lem-sfb-local-system-affine-descent-presentation: statement, unsplit, no Mathlib match. Finite affine fpqc refinement, local representing coproduct, clopen transitions and the scheme cocycle; old steps 3–5.
- lem-sfb-coproduct-fpqc-effectivity: statement, unsplit, no Mathlib match. Finite-component containment, the quasi-compact-intersection check for quasi-affineness and effectivity of an arbitrary coproduct datum; old step 6.
- lem-sfb-coproduct-model-represents-sheaf: statement, unsplit, no Mathlib match. Separated/étale property descent, pointwise surjectivity, mutually inverse gluing constructions and the universal representing section; old steps 7–9.
- report.md and citations.json: report, original argument allocation, review, and verbatim supporting statements for every parent citation.

All four new nodes have proof=[], proof_deps=[], proof_origin=null and status=unsplit. They are available for separate workers; their statements give the exact hypotheses and conclusions, with no proof sketches. The complete arguments being assigned to them are retained below. Their statement lengths are approximately 1760, 1960, 1190 and 1780 characters. No node receives the entire original proof, and no node alone states any of the lattice-scheme conclusions. The generic geometric lemmas mention an arbitrary sheaf or set, not the original lattice functor.

## Attachments

None. I searched WeilConjectures/ by the exact blueprint tag and by lattice/representability, and searched the relevant geometric descent vocabulary. No project declaration states the item exactly. The recorded Sheaf.Paper.StratifiedLatticeScheme.exists_stratifiedLatticeScheme theorem ends in sorry (line 181 in the read source); it is not a finished attachment. The coefficient helper definitions are real data but do not prove the theorem.

## WANTED

None. The blueprint main-20261015 statement, proof and unit; Bhatt–Scholze's Proposition 6.8.4(6); and the Stacks TeX sources used here are locally available.

## What was wrong and what changed

The returned proof had 8051 characters and kept several independent constructions in the parent. This repair spreads all of those constructions over four new statement-only lemmas, rather than shortening their substance. The parent proof is 2004 characters, below the 3000-character limit. Its original statement, coefficient conventions, size conventions, qcqs hypotheses, three conclusions, Lean record and import metadata are retained. Old step 10 remains as a short edge-case assembly, with the new statements also expressly including empty objects and rank zero.

The existing source-level corrections are preserved: the affine trivializing charts are pro-étale objects, not affine Zariski opens of X; Tag 0APK is used in its actual ind-quasi-affine form, without claiming the infinite coproduct is quasi-compact; and a universal section is obtained by evaluation on the identity. These are the same unit route, not replacements by the classicality theorem or a Noetherian-only representability theorem. The new nodes inherit sk-lem-stratified-lattice; no chapter or unit record was edited.

## Mathlib and duplicate searches

I ran all searches through batch2/msearch.py. Each new node records the exact LeanFinder, Loogle, grep and LeanSearch queries in searches.jsonl. Each natural-language question was also tried in another phrasing. All services responded in this run. I read the returned signatures and the plausible source files Proetale.lean, Representability.lean and QuasiAffine.lean. Constant-sheaf recognition on a general site does not construct the scheme datum. LocalRepresentability.isRepresentable and yonedaIsoSheaf assume big-Zariski relatively representable open charts; no one-line specialization supplies small-pro-étale fpqc descent. The quasi-affine immersion lemma and finite affine coproduct instance give only parts of the hypothesis verification. SheafOfModules localization in the Loogle hit is localization of sheafification, not inversion of the coefficient ell.

Before creating the nodes I searched the whole DAG by lattice, finite affine trivialization, coproduct/constant sheaf, ind-quasi-affine and representability/descent vocabulary, and by the Stacks tags 03YW, 0AP6, 0APK, 02KU, 02VN and 023Q. I ran blueprint_refs.py ancestor for the item and blueprint_refs.py search for trivializing, coproduct, ind-quasi-affine, representability descent, descent datum and lattice. I read the candidate statements listed below. No blueprint node states one of the new generic interfaces in full. New blueprint.from places identify exactly (1), (2) charts/transitions/effectivity, and (2)–(3) gluing/universality; same_as is empty.

## Not duplicates

lem-sfb-embedded-lattice-coefficient-comparison vs lem-weil-pbc-continuous-coefficient-realizations: that node compares ring objects; this node compares embedded lattices with continuous-coefficient module pairs, including localization and restriction compatibility.

lem-sfb-embedded-lattice-coefficient-comparison vs det-prop-sfb-qlbar-colimit-x-invert-ell: that node identifies the coefficient localization; this node identifies the lattice functors and their image normalization.

lem-sfb-embedded-lattice-coefficient-comparison vs lem-weil-pbc-lattice-pair-image-classification: that node gives the equality-of-images criterion and unique intertwining maps for sectionwise injective ring maps; this node includes condensed/continuous coefficient transport and the equivalence between localization-defined embedded lattices and rationalized pairs.

lem-sfb-embedded-lattice-coefficient-comparison vs lem-weil-pbc-lattice-sheaf-locally-constant: that node works with continuous coefficients and proves sheafness and the constant-coset classification; this node compares coefficient and embedding conventions and makes no local-constancy assertion.

lem-sfb-embedded-lattice-coefficient-comparison vs det-lem-stratified-lattice-scheme: the parent is specifically about integral lattices in a lisse rational module and asserts all three conclusions; this new lemma supplies only its indicated coefficient or generic scheme argument and cannot replace the whole parent.

lem-sfb-local-system-affine-descent-presentation vs lem-galois-constant-sheaf-sets-representable: that node represents a constant sheaf on the small étale site; this node constructs a finite affine weakly-étale fpqc chart and realizes the arbitrary transition cocycle of a pro-étale locally constant sheaf.

lem-sfb-local-system-affine-descent-presentation vs lem-weil-pbc-proetale-finite-constant-representable: that node assumes a finite label set and has no chart or descent-datum conclusion; the labels here may be infinite and vary by transitions.

lem-sfb-local-system-affine-descent-presentation vs lem-galois-coproduct-copies-morphisms-clopen: that node classifies maps into a coproduct by clopen partitions; this node also constructs the affine fpqc chart, local sheaf presentation and transition cocycle.

lem-sfb-local-system-affine-descent-presentation vs sk-def-pe-site: that node defines the site and finite refinement over an affine target; this statement constructs a global affine chart over a qcqs base together with a represented transition datum.

lem-sfb-local-system-affine-descent-presentation vs lem-trf-fppf-sheaf-representability-descent-data: that node concerns the big fppf site and supplied local representing schemes; this one concerns a small pro-étale sheaf, constructs an affine chart and explicitly realizes its arbitrary-label transitions.

lem-sfb-local-system-affine-descent-presentation vs lem-a1-universe-enlarged-etale-realization: the existing node is Large-valued etale sheaf realization over the canonically enlarged base; it does not construct both a finite affine pro-étale fpqc chart for an arbitrary locally constant set sheaf and the corresponding scheme transition cocycle.

lem-sfb-local-system-affine-descent-presentation vs def-weil-pbc-constant-group-scheme: the existing node is The constant group scheme T_E and the group law on its T-valued points; it does not construct both a finite affine pro-étale fpqc chart for an arbitrary locally constant set sheaf and the corresponding scheme transition cocycle.

lem-sfb-local-system-affine-descent-presentation vs lem-weil-pbc-constant-sheaf-sections-connected: the existing node is Global sections of a constant etale sheaf on a connected scheme; it does not construct both a finite affine pro-étale fpqc chart for an arbitrary locally constant set sheaf and the corresponding scheme transition cocycle.

lem-sfb-local-system-affine-descent-presentation vs lem-weil-pbc-constant-group-scheme-point-add-component: the existing node is Addition preserves summed component labels; it does not construct both a finite affine pro-étale fpqc chart for an arbitrary locally constant set sheaf and the corresponding scheme transition cocycle.

lem-sfb-local-system-affine-descent-presentation vs lem-weil-pbc-constant-group-scheme-morphism-clopen: the existing node is Maps to a constant group scheme are clopen decompositions; it does not construct both a finite affine pro-étale fpqc chart for an arbitrary locally constant set sheaf and the corresponding scheme transition cocycle.

lem-sfb-local-system-affine-descent-presentation vs lem-weil-pbc-constant-group-scheme-multiplication: the existing node is The multiplication of the constant group scheme: the components of T_E x_T T_E and the glued morphism; it does not construct both a finite affine pro-étale fpqc chart for an arbitrary locally constant set sheaf and the corresponding scheme transition cocycle.

lem-sfb-local-system-affine-descent-presentation vs lem-weil-pbc-constant-sheaf-sections-locally-constant: the existing node is Sections of a constant etale sheaf are locally constant maps; it does not construct both a finite affine pro-étale fpqc chart for an arbitrary locally constant set sheaf and the corresponding scheme transition cocycle.

lem-sfb-local-system-affine-descent-presentation vs det-lem-stratified-lattice-scheme: the parent is specifically about integral lattices in a lisse rational module and asserts all three conclusions; this new lemma supplies only its indicated coefficient or generic scheme argument and cannot replace the whole parent.

lem-sfb-coproduct-fpqc-effectivity vs lem-a1-ind-quasi-affine-fpqc-effective-descent: that node assumes every quasi-compact open is relatively quasi-affine; this node proves that hypothesis for arbitrary labelled coproducts, including quasi-compact intersections, and concludes effectivity for those data.

lem-sfb-coproduct-fpqc-effectivity vs lem-a1-ind-quasi-affine-permanence: that node assumes ind-quasi-affineness and proves permanence; this node verifies it for labelled coproducts and gives effective descent.

lem-sfb-coproduct-fpqc-effectivity vs lem-trf-quasi-affine-fpqc-effective-descent: that node assumes quasi-affineness of the entire morphism, including quasi-compactness; T here can be an infinite coproduct and not quasi-compact.

lem-sfb-coproduct-fpqc-effectivity vs lem-galois-fpqc-affine-descent-effective: that node assumes the descending morphism is affine; an infinite coproduct of copies of an affine scheme need not be affine.

lem-sfb-coproduct-fpqc-effectivity vs lem-a1-separated-lqf-fpqc-effective-descent: the existing node is Separated locally quasi-finite scheme descent is effective for a singleton fpqc cover; it does not state the finite-component quasi-affine-open verification and effectivity for every descent datum on an arbitrary labelled coproduct.

lem-sfb-coproduct-fpqc-effectivity vs det-lem-stratified-lattice-scheme: the parent is specifically about integral lattices in a lisse rational module and asserts all three conclusions; this new lemma supplies only its indicated coefficient or generic scheme argument and cannot replace the whole parent.

lem-sfb-coproduct-model-represents-sheaf vs lem-weil-pbc-fpqc-representable-descent: that node glues morphisms into a fixed scheme; this one constructs mutually inverse sheaf/point bijections for a descended coproduct model, descends its geometric properties and gives the universal section.

lem-sfb-coproduct-model-represents-sheaf vs lem-galois-fpqc-morphisms-descend: that node proves full faithfulness for scheme morphisms; this one identifies the original small-site sheaf with the descended model and obtains its properties and universal section.

lem-sfb-coproduct-model-represents-sheaf vs lem-galois-fpqc-descend-etale: that node descends étaleness from an fpqc cover; this statement also proves the local coproduct properties, identifies the sheaf, and gives the universal section.

lem-sfb-coproduct-model-represents-sheaf vs lem-weil-pbc-fpqc-descend-separated: that node descends separatedness; this statement includes the small-site representation and its normalization.

lem-sfb-coproduct-model-represents-sheaf vs lem-a1-proetale-local-system-representability: that node assumes locally Noetherian X and concludes a valuation lifting property; this node assumes a supplied effective coproduct model over an fpqc chart, without Noetherianity, and identifies its functor and universal section.

lem-sfb-coproduct-model-represents-sheaf vs lem-weil-pbc-continuous-etale-local-lattice: that node assumes a Noetherian underlying space and constructs an integral module on an étale cover; it does not identify an arbitrary descended model with a sheaf.

lem-sfb-coproduct-model-represents-sheaf vs lem-sbc-root-split-cover-prescribed-cyclic-charts: the existing node is Prescribed-equation cyclic charts of a root-split cover; it does not identify a supplied effective arbitrary-coproduct model with an arbitrary small-pro-étale sheaf, with the normalized representing bijections and universal section.

lem-sfb-coproduct-model-represents-sheaf vs lem-sbc-root-split-cover-away-divisor-charts: the existing node is Degree-one root charts for root-split covers away from the divisor; it does not identify a supplied effective arbitrary-coproduct model with an arbitrary small-pro-étale sheaf, with the normalized representing bijections and universal section.

lem-sfb-coproduct-model-represents-sheaf vs lem-sbc-finite-etale-descent-near-closed-point: the existing node is Etale descent from a flat Noetherian base change near a local closed point; it does not identify a supplied effective arbitrary-coproduct model with an arbitrary small-pro-étale sheaf, with the normalized representing bijections and universal section.

lem-sfb-coproduct-model-represents-sheaf vs lem-sbc-root-split-cover-on-divisor-charts: the existing node is Cyclic chart model on the divisor; it does not identify a supplied effective arbitrary-coproduct model with an arbitrary small-pro-étale sheaf, with the normalized representing bijections and universal section.

lem-sfb-coproduct-model-represents-sheaf vs lem-sbc-root-split-factor-finite-etale: the existing node is Finite etale descent from a punctured root splitting; it does not identify a supplied effective arbitrary-coproduct model with an arbitrary small-pro-étale sheaf, with the normalized representing bijections and universal section.

lem-sfb-coproduct-model-represents-sheaf vs lem-sbc-root-split-cover-ind-etale-charts: the existing node is Cyclic orbit root model over an ind-etale local limit; it does not identify a supplied effective arbitrary-coproduct model with an arbitrary small-pro-étale sheaf, with the normalized representing bijections and universal section.

lem-sfb-coproduct-model-represents-sheaf vs lem-sbc-root-split-cover-cyclic-chart-model: the existing node is Cyclic chart model before regularity bookkeeping; it does not identify a supplied effective arbitrary-coproduct model with an arbitrary small-pro-étale sheaf, with the normalized representing bijections and universal section.

lem-sfb-coproduct-model-represents-sheaf vs lem-sbc-root-split-cover-cyclic-charts: the existing node is Cyclic orbit classification for covers split by one root extension; it does not identify a supplied effective arbitrary-coproduct model with an arbitrary small-pro-étale sheaf, with the normalized representing bijections and universal section.

lem-sfb-coproduct-model-represents-sheaf vs lem-trf-etale-relation-finding-opens: the existing node is Restriction of a quotient by an fppf relation is an open subspace; it does not identify a supplied effective arbitrary-coproduct model with an arbitrary small-pro-étale sheaf, with the normalized representing bijections and universal section.

lem-sfb-coproduct-model-represents-sheaf vs lem-trf-etale-affine-quotient-representable: the existing node is Representability facts for an affine etale-relation quotient; it does not identify a supplied effective arbitrary-coproduct model with an arbitrary small-pro-étale sheaf, with the normalized representing bijections and universal section.

lem-sfb-coproduct-model-represents-sheaf vs lem-trf-polarized-scheme-etale-descent: the existing node is Effective etale descent for polarized schemes; it does not identify a supplied effective arbitrary-coproduct model with an arbitrary small-pro-étale sheaf, with the normalized representing bijections and universal section.

lem-sfb-coproduct-model-represents-sheaf vs def-trf-polarized-scheme-etale-descent-datum: the existing node is Polarized scheme etale descent data, candidate pairs and compatible isomorphisms; it does not identify a supplied effective arbitrary-coproduct model with an arbitrary small-pro-étale sheaf, with the normalized representing bijections and universal section.

lem-sfb-coproduct-model-represents-sheaf vs lem-sc-etale-faithfully-flat-local: the existing node is Etaleness at a point descends along a faithfully flat field extension; it does not identify a supplied effective arbitrary-coproduct model with an arbitrary small-pro-étale sheaf, with the normalized representing bijections and universal section.

lem-sfb-coproduct-model-represents-sheaf vs lem-sc-etale-base-change-geometric: the existing node is Pointwise etaleness is preserved and reflected by field extension; it does not identify a supplied effective arbitrary-coproduct model with an arbitrary small-pro-étale sheaf, with the normalized representing bijections and universal section.

lem-sfb-coproduct-model-represents-sheaf vs lem-weil-pbc-fpqc-descend-affine: the existing node is Being affine descends along fpqc coverings (Stacks 02L5); it does not identify a supplied effective arbitrary-coproduct model with an arbitrary small-pro-étale sheaf, with the normalized representing bijections and universal section.

lem-sfb-coproduct-model-represents-sheaf vs det-lem-stratified-lattice-scheme: the parent is specifically about integral lattices in a lisse rational module and asserts all three conclusions; this new lemma supplies only its indicated coefficient or generic scheme argument and cannot replace the whole parent.

## Review by Q42

I read the main-20261015 statement and proof (1)–(3) of det-lem-stratified-lattice-scheme, its unit sk-lem-stratified-lattice (especially the chart/cocycle and 0APK paragraphs), and the chapter's coefficient-layer conventions. I also read Bhatt–Scholze Proposition 6.8.4(6), pp. 59–60, to check the exact continuous-coefficient pair functor and the label gA^r. This source supplies the local classification, not an extra Noetherian hypothesis. The item is unchanged. For the coefficient comparison node I checked both ring comparisons on totally disconnected E and A, the commutative integral-inclusion square, the localization/tensor formulas, free-chart injectivity, uniqueness of a pair from its embedded image, and compatibility with restrictions. These are old steps 1–2. The new node does not assert the old classification again. Its proof assignment below states every map and inverse explicitly.

For the affine descent presentation node I read the exact pro-étale covering condition and the source's paragraph (2). The base must be quasi-compact to use finitely many affine base opens, and quasi-separated to make the resulting affine-source morphism quasi-compact. No claim that an affine pro-étale chart is open in X survives. I read the statements of affine-morphism permanence, weakly-étale stability, affine-scheme qcqs and qcqs-morphism permanence: they provide respectively finite affine coproducts, flatness/stability, source quasi-compactness and the required quasi-compact morphism. The statement of the clopen coproduct node gives the inverse construction on each label, and fpqc representable descent (023Q, descent.tex lemma-fpqc-universal-effective-epimorphisms) gives the sheaf property. I checked the scheme cocycle component by component on the triple overlap, not by assuming a continuous function to a group of infinite permutations. The new lemma's statement includes that cocycle and its label normalization.

For the effectivity node I read more-morphisms.tex definition-ind-quasi-affine (0AP6) and lemma-ind-quasi-affine-alternative-definition, and more-groupoids.tex lemma-ind-quasi-affine (0APK). I read lem-a1-ind-quasi-affine-fpqc-effective-descent's exact statement, which assumes quasi-affineness of K→B for every quasi-compact open K over affine B, without a finite-presentation or quasi-compactness hypothesis on T→V. A quasi-compact K meets only finitely many components. For affine B'⊂B, its inverse image is the intersection of two quasi-compact opens in the finite affine union over B; that intersection is quasi-compact because that ambient union is quasi-separated. This is the maintainer's previous correction, and is explicitly in the new statement and full argument below. It is not omitted or replaced by “quasi-affine by inspection”.

For the representing-model node I read descent.tex lemma-descending-property-separated (02KU), lemma-descending-property-etale (02VN), and lemma-fpqc-universal-effective-epimorphisms (023Q), as well as the full statements of the corresponding existing nodes. The local coproduct has identity diagonal on equal-label components and empty diagonal on different-label components, so it is separated; it is étale by its identity charts. The hypotheses include flat, surjective and quasi-compact p, as needed for the separated-descent node. Surjectivity is conditional on nonempty S, essential when S=∅ and X≠∅. For each U, base change gives the fpqc cover U×_X V→U and weakly-étale stability makes it a pro-étale cover too. The supplied datum compatibility identifies the two local classifying maps as morphisms, so 023Q glues them uniquely. The inverse construction uses the sheaf property of F. This establishes both inverse equations and naturality, not only an equality on geometric points. I read det-pe-morphisms-etale-comparison: its first clause makes Y a site object. The universal element is b_Y^{-1}(id_Y), and its component normalization is id_T; this retains old step 9, including naturality and the local lattice gA^r.

Parent step 1 uses exactly the first new node's restriction-compatible bijections and the existing lattice-sheaf-locally-constant statement's sheafness and coset formula. Parent step 2 applies the second node only after step 1 has supplied fixed-S trivializations on the rank-r covering of L. Step 3 uses exactly the third node's existence of Y and η. Step 4 uses exactly the fourth node's property and functor conclusions; the standard coset proves its nonemptiness hypothesis. Step 5 uses that node's universal-section formula and local normalization, interpreted through step 1. Step 6 is only the zero-rank/empty-base consequence of those statements and definitions. Every parent citation is supplied with an exact verbatim quote in citations.json. None takes a construction only from another node's proof. The lone off-unit proof citation in the parent, lattice-sheaf-locally-constant, is declared as the existing generic classification tool; the descent route remains in the unit.

I tested the statements on X=∅, S=∅, S a singleton, infinite S with nonempty affine V, and r=0. For S=∅ over nonempty X, the descended scheme is empty, the sheaf is initial, and no surjectivity is asserted. For singleton S, the chart's transition is the identity, the model is X and the universal element is its unique section. Infinite S confirms why T→V must not be assumed quasi-compact. Zero rank has a singleton coset set and zero universal lattice. No step uses nonempty X, positive rank or Noetherianity. I checked all new statements introduce their rings, schemes, sheaves, covers, maps, index sets and descent data, with definition dependencies rather than tags standing for meanings. Sources are allowed blueprint/Bhatt–Scholze/Stacks only. No SGA source was used.

Against B–E: the new files are statement-only; sources and labels were read; all notions have inline meanings or the actual definition-node dependencies; the source/DAG/Mathlib searches precede creation and use logged queries. No new lemma duplicates a local-classification result, restates a lattice-scheme clause, or moves the whole proof into one descendant. The parent has no step above 2000 characters. I checked every parent citation's statement, all hypotheses of the three generic geometric nodes, and the empty/infinite-label cases just described. The return has one demand, spreading the large proof: it is addressed by four independently usable unsplit arguments and a 2004-character parent assembly. No mathematical statement change or unresolved source dispute was needed.

## Preserved proof assignments

The following text preserves the original proof in full. It is the argument assigned to each new unsplit node, not proof steps in those node files. Other workers can use these assignments and the self-contained statements to carry out their independent splits. The order is also the complete map from the returned ten steps to the new DAG.

### Old step 1 → lem-sfb-embedded-lattice-coefficient-comparison

By [lem-weil-pbc-continuous-coefficient-realizations], identify the pulled-back coefficients with the continuous-function coefficient sheaves, compatibly with $A\to E$. The total-disconnectedness hypothesis holds: nonarchimedean clopen balls separate distinct points of $E$, and $A$ has the subspace topology. Module actions and inclusions transport along these ring isomorphisms. By [det-prop-sfb-qlbar-colimit-x-invert-ell], $A_X[1/\ell]=E_X$. On module sections the localization/tensor comparison is $m/\ell^n\mapsto\ell^{-n}\otimes m$, with inverse $a/\ell^n\otimes m\mapsto am/\ell^n$, interpreted locally when necessary. Thus the lattice condition is exactly the scalar-extension condition in the lattice-classification node.

Existing statements available for its future split: lem-weil-pbc-continuous-coefficient-realizations, det-prop-sfb-qlbar-colimit-x-invert-ell.

### Old step 2 → lem-sfb-embedded-lattice-coefficient-comparison

An object $(M,\alpha)$ in [lem-weil-pbc-lattice-sheaf-locally-constant] embeds in $L$ by $m\mapsto\alpha(1\otimes m)$. On free charts this is injective because $A\hookrightarrow E$ induces an injective map of continuous-function sheaves. Its image is an embedded lisse lattice. Conversely an embedded lattice gives such a pair by its scalar-extension isomorphism. Two pairs have the same image exactly when their unique isomorphism over that image intertwines $\alpha$. These constructions commute with restriction. Therefore that node's sheaf is precisely $\mathcal{L}\mathit{at}$. Its trivial-bundle classification gives clause (1), including the specified coset $g\operatorname{GL}_r(A)$ corresponding to $gA^r$.

Existing statements available for its future split: lem-weil-pbc-lattice-sheaf-locally-constant.

### Old step 3 → lem-sfb-local-system-affine-descent-presentation

Choose a finite affine open cover of the quasi-compact $X$. Over each member, the covering condition in [def-weil-pbc-proetale-site] extracts finitely many affine pieces of a trivializing pro-étale covering of $L$, whose images cover that member. Put $V$ equal to their finite disjoint union and $p:V\to X$ the induced map; on all pieces choose rank-$r$ trivializations, giving $L|_V\cong E_V^r$. By [lem-weil-pbc-affine-morphism-permanence], $V$ is affine; by [sk-lem-pe-weakly-etale-stability], $p$ is weakly étale, hence flat. The images cover $X$, so $p$ is surjective. By [lem-weil-pbc-affine-scheme-qcqs] and [lem-weil-pbc-qcqs-morphism-permanence], $p$ is quasi-compact since $X$ is quasi-separated. For every affine open $B\subset X$, its inverse image is quasi-compact and hence covered by finitely many affine opens; their images cover $B$. This verifies that $\{p\}$ is an fpqc and pro-étale covering. The pieces $V_i$ are affine pro-étale objects over $X$, not necessarily Zariski open subschemes of $X$.

Existing statements available for its future split: def-weil-pbc-proetale-site, lem-weil-pbc-affine-morphism-permanence, sk-lem-pe-weakly-etale-stability, lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-qcqs-morphism-permanence.

### Old step 4 → lem-sfb-local-system-affine-descent-presentation

Write $S=\operatorname{GL}_r(E)/\operatorname{GL}_r(A)$ and form $T=\coprod_{s\in S}V$ using [lem-weil-pbc-scheme-coproduct-family]. By [lem-galois-coproduct-copies-morphisms-clopen], $V$-morphisms $W\to T$ are exactly locally constant maps $|W|\to S$. This presheaf is a sheaf for pro-étale coverings by [lem-weil-pbc-fpqc-representable-descent]. The constant-presheaf map sends $s$ to the corresponding component section. Every morphism $W\to T$ is such a section on each of its open-and-closed inverse images of the components. Consequently its sheafification is exactly this presheaf: extend maps out of the constant presheaf by sheaf gluing on these open pieces, uniquely. Thus $T$ represents $\underline S_V$, and by step 2 represents $\mathcal{L}\mathit{at}|_V$.

Existing statements available for its future split: lem-weil-pbc-scheme-coproduct-family, lem-galois-coproduct-copies-morphisms-clopen, lem-weil-pbc-fpqc-representable-descent.

### Old step 5 → lem-sfb-local-system-affine-descent-presentation

On $R=V\times_XV$, the two trivializations identify the two pullbacks of $\mathcal{L}\mathit{at}$ with $\underline S_R$. For a fixed source label $s$, their transition sends the constant section $s$ to a section of $\underline S_R$, hence by step 4 to a clopen decomposition of $R$ indexed by target labels. By [lem-galois-coproduct-copies-morphisms-clopen], this gives a morphism from that copy of $R$ to $\coprod_S R$. The coproduct universal property assembles these component maps. Applying the inverse sheaf transition gives its inverse. On a triple overlap both composites induce the same sheaf transition; the same clopen descriptions make the scheme maps equal. Hence this is a scheme descent datum on $T/V$ over $V/X$. No continuity assertion about a varying infinite permutation is required beyond its effect on each fixed label.

Existing statements available for its future split: lem-galois-coproduct-copies-morphisms-clopen, lem-weil-pbc-scheme-coproduct-family.

### Old step 6 → lem-sfb-coproduct-fpqc-effectivity

Check the exact effectivity hypothesis of [lem-a1-ind-quasi-affine-fpqc-effective-descent]. For any affine open $B\subset V$ and quasi-compact open $K\subset T\times_V B=\coprod_S B$, finitely many components contain $K$: the intersections with components are an open covering of $K$. Thus $K$ is an open subscheme of a finite disjoint union of copies of $B$, which is affine by [lem-weil-pbc-affine-morphism-permanence]. More precisely $K\to B$ is quasi-affine: over any affine open $B'\subset B$, its inverse image $K'$ is the intersection of $K$ with the corresponding finite disjoint union $D'$ of copies of $B'$, again affine. It is open in $D'$, and quasi-compact because $K$ and $D'$ are quasi-compact opens of the affine, hence quasi-separated, finite union of copies of $B$ [lem-weil-pbc-affine-scheme-qcqs]. So $K'$ is a quasi-affine scheme. The datum of step 5 therefore satisfies every hypothesis of the cited singleton-fpqc effectivity theorem (Stacks Tag 0APK). Obtain an $X$-scheme $Y$ and $Y\times_XV\cong T$ inducing that datum. No quasi-compactness of $T\to V$ is used.

Existing statements available for its future split: lem-a1-ind-quasi-affine-fpqc-effective-descent, lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-affine-scheme-qcqs.

### Old step 7 → lem-sfb-coproduct-model-represents-sheaf

The morphism $T\to V$ is étale, since on each component it is the identity and the affine-ring definition is local on the source. Its diagonal is a closed immersion: $T\times_VT$ is covered by the pairwise components $V$ indexed by $(s,t)$; the diagonal is the identity on $s=t$ and empty on $s\ne t$, so its complement is the open union of the off-diagonal components. Thus it is separated. Apply [lem-galois-fpqc-descend-etale] and [lem-weil-pbc-fpqc-descend-separated] to $p:V\to X$ to conclude that $q:Y\to X$ is étale and separated. For each $x\in X$, choose $v\in V$ above it and the point in the copy of $V$ indexed by the standard lattice $A^r$ above $v$. Its image in $Y$ lies over $x$; hence $q$ is surjective.

Existing statements available for its future split: lem-galois-fpqc-descend-etale, lem-weil-pbc-fpqc-descend-separated, lem-weil-pbc-scheme-coproduct-family.

### Old step 8 → lem-sfb-coproduct-model-represents-sheaf

For any $U\to X$ in $X_{\mathrm{proét}}$, set $U_V=U\times_XV$. This is an fpqc covering of $U$ by [lem-galois-fpqc-covering-base-change], and weakly étale by [sk-lem-pe-weakly-etale-stability], hence a pro-étale covering. A section of $\mathcal{L}\mathit{at}(U)$ gives on $U_V$ the morphism to $T$ of step 4 and thus a morphism $U_V\to Y$ over $X$. The two maps on $U_V\times_UU_V$ agree precisely because the descent datum in step 5 was obtained from this sheaf's restrictions. By [lem-weil-pbc-fpqc-representable-descent] they glue uniquely to $U\to Y$; the structural equality over $X$ also descends uniquely. Conversely an $X$-map $U\to Y$ pulls back to a map to $T$, hence a lattice section on $U_V$; its compatibility gives a unique section on $U$ by the sheaf property proved in step 2. The constructions are inverse after the covering and therefore globally, and commute with pullbacks in $U$. Thus $Y$ represents $\mathcal{L}\mathit{at}$; define $\mathrm{Lat}(L)=Y$.

Existing statements available for its future split: lem-galois-fpqc-covering-base-change, sk-lem-pe-weakly-etale-stability, lem-weil-pbc-fpqc-representable-descent.

### Old step 9 → lem-sfb-coproduct-model-represents-sheaf

By [det-pe-morphisms-etale-comparison], $q:Y\to X$ is weakly étale, so $Y$ is itself an object of the pro-étale site (in the containing universe fixed in the statement). Evaluate the representing isomorphism of step 8 on $\mathrm{id}_Y\in\operatorname{Hom}_X(Y,Y)$. This gives a section of $\mathcal{L}\mathit{at}(Y)$, namely a lisse embedded lattice $M^{\mathrm{univ}}\subseteq L|_Y=q^*L$ with $M^{\mathrm{univ}}[1/\ell]=q^*L$. Naturality says that every $f:U\to Y$ pulls it back to the section classified by $f$, which is the universal property. On the component of $T$ labelled by $g\operatorname{GL}_r(A)$ its restriction is $gA_V^r$, so this is also the lattice described in the source's local construction. This proves clause (3).

Existing statements available for its future split: det-pe-morphisms-etale-comparison.

### Old step 10 → parent elementary edge-case step

The set $S$ is nonempty for every $r\geq0$, including $r=0$, where it is a singleton and the unique lattice is zero; the construction then gives $Y=X$. If $X$ is empty its site has only empty objects up to isomorphism and its lattice sheaf is terminal, represented by the empty $X$-scheme with the zero universal module. This also follows by using the empty trivializing family throughout. No positive-rank, nonempty-base or Noetherian hypothesis was introduced.

Existing statements available for its future split: none; elementary edge cases.

## Unfinished work

The four new lemmas are intentionally statement-only, as the return requires. There is no unresolved repair point. Server dry-run and delivery results are recorded after the checks complete.
