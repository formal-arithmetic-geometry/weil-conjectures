# Worker report: lem-sfb-space-big-small-ringed-comparison

1. Files written:
   - dag/nodes/sec-six-functors-basics/lem-sfb-space-big-small-ringed-comparison.json: item, split in eight steps; no Mathlib match.
   - dag/nodes/sec-six-functors-basics/lem-sfb-site-left-adjoint-connected-limits.json: new statement-only prerequisite, unsplit; no Mathlib match.
   - citations.json: one verbatim statement quotation for each of the 34 cited-node occurrences.
2. Attachments: none. Searched lean/WeilConjectures by the exact blueprint id, big/small-etale names and fibred-groupoid/algebraic-space concepts. No declaration there states the item or the new prerequisite.
3. WANTED: none. All mathematical sources used are present locally.
4. The original item was statement-only. Its statement and statement dependencies are retained. The proof cannot assume A times_B V is a scheme or that A_et has a terminal object. Those two traps are addressed explicitly. The imported blueprint ancestry has from.node=null; blueprint_refs.py ancestor confirms this, and its inherited place and via chain are retained. Read the current latest blueprint chapter and unit, and the current sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). This is infrastructure below the inherited direct-image route, not a replacement of its unit route; no unit realization is changed.
5. Nothing in this split remains unfinished. The one new connected-limit theorem is deliberately left statement-only for its own later stage-1 worker. No Lean was written or compiled; no repository or launcher file was changed.

## Review by Q116

I read stacks-sheaves.tex, Tag 073M (lemma-compare), Tag 073N (lemma-compare-morphism), equation-compare-big-small, Tag 076R (equation-comparison-algebraic-spaces-modules), the four assertions of Tag 075D (lemma-comparison), equation-pushforward, and the proof of Tag 075N. The item's quantified tests really may be arbitrary fibred groupoids; no algebraic-stack or quasi-coherence condition was introduced. The source calls its total sites fppf categories but explicitly allows the etale topology on those same objects and arrows. I use etale covers throughout. For the new node I read sites.tex Tags 00XR (lemma-when-shriek), assertions (1),(2), and 00XS (lemma-preserve-equalizers), including hypotheses (a)--(c) and its proof. The new statement gives precisely their set-sheaf adjunction and fibre-product/equalizer conclusion, without adding terminal-object preservation.

Step 1 uses the actual small-site definition in def-trf-algebraic-space and the covering and cocontinuity definitions. I checked the statement of lem-trf-space-representable-etale-scheme-tests: it gives scheme-source representability, scheme fibre products, etale composition/base change, and cancellation between etale scheme charts. The displayed equalizer is a base change of the diagonal V to V times_A V; both are small scheme charts, so the same cited statement makes that diagonal etale. The argument is a direct verification, with representing equivalences preserving underlying schemes, not a theorem about arbitrary stackification.

Step 2 invokes only the new node for the nontrivial connected-limit theorem. It does not invoke lem-trf-bigger-site-retraction: that theorem assumes terminal objects in both underlying sites, which are unavailable for a non-scheme space. The remaining terminal-sheaf argument is written out using an atlas and its scheme relation. The definition of algebraic space supplies the atlas, and the scheme-test statement supplies every required base-change cover. Compatible sections on the atlas and its overlap are equivalent to global families on either site by the sheaf axiom; this proves the terminal assertion rather than assuming it. Sizes are the common small presentations of def-weil-size-convention, not an unrestricted class-indexed colimit.

Step 3 uses def-weil-pbc-ringed-topos-morphism for the induced direct-image action, not as a claimed theorem about exactness. I opened lem-weil-pbc-module-sheaves-colimits-forgetful and the general-site lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective. Their statements give sectionwise kernels, faithful exact forgetting, sheafified cokernels and local lifting. Faithful exact forgetting reflects exactness because a zero underlying kernel/cokernel has zero identity morphism. Covers of an etale chart remain small charts by the scheme-test lemma. Thus restriction preserves epimorphisms, and the proof uses no false injective-module preservation claim.

Step 4 takes continuity/cocontinuity from lem-sfb-fibred-site-functor-continuity for the etale base site. The precise compatible-family and unit formulas are in the statement of lem-weil-pbc-continuous-cocontinuous-topos-adjunction, not merely its proof. The ringed module adjunction supplies tensor pullback and the structural-ring action. Identity structure rings on functors over schemes make big module pullback precomposition. The fibre-product node supplies X=A times_B V as a space. The two descriptions of the index arrows are spelled out.

Step 5 uses def-trf-space-etale-module-functors for the specified limiting cone, including its chart projections and scalar maps. I corrected an initial omission here: its indexing charts are etale over A, so I added lem-trf-space-chartwise-etale-permanence and the cancellation/composition argument identifying them with charts etale over X. The fibre-product and scheme-test statements make T times_X Q and all overlaps actual schemes. I checked that the section on T' is pulled from Q, which is etale over A, and did not wrongly evaluate RF on an arbitrary T. Only the big sheaf F is evaluated on arbitrary schemes. The inverse, its independence of atlas and its compatibility with arbitrary scheme maps are proved by the displayed cover and uniqueness of gluing.

Step 6 checks operations, coefficients and maps of tests componentwise. I corrected a second omission by citing lem-trf-space-enlarged-etale-ringed-site-model: its statement gives the extension of a set sheaf, its atlas equalizer, and the continuous fibre-product functor defining the canonical small morphism. This supplies the set-sheaf comparison needed for a geometric-morphism square, in addition to the previously explicit module comparison. The structural maps use the same regular-function pullbacks on every scheme chart. The choice of representing equivalences cannot change these normalized maps.

Step 7 applies the fibred-site and ringed adjunction statements to the arbitrary ambient E and the tests; no representability of E is used. The actual cocontinuous-unit formula is cited. The adjoint map sends m to its family of restrictions along T to V, and lem-trf-space-chart-adjunction-tensor-realization explicitly identifies the chart-unit expression with the genuine sheaf tensor pullback. This proves the requested unit-followed-by-t_u normalization, not just existence of some map with the correct endpoints.

Step 8 uses that same tensor-realization statement for composition, namely a tensor (b tensor m) mapping to a u^sharp(b) tensor m. The two compared maps are computed on these local generators; functoriality of H makes their values identical. This also checks the specified two-isomorphisms, identity, chart restriction and naturality in H. I explicitly avoided assuming all global sections are pure tensors. No long step exceeds 2000 characters; each is one construction or verification and no intermediate theorem is hidden by 'standard' or 'transport'.

For B1--B7, the new node introduces both sites, the functor, all hypotheses and both adjoints, links the definitions it needs, has no proof or proof dependencies, and uses TeX with ordinary single mathematical backslashes after JSON decoding. Its source is the exact local Stacks tag/label, not a chapter number. The DAG searches used the tags 00XR/00XS, connected-limit and equalizer terminology, and the corresponding blueprint_refs.py searches. I inspected the plausible existing connected and bigger-site candidates; the nonduplication differences are listed below. The new node is neither a clause of the algebraic-space comparison nor an elementary assertion: its proof needs the almost-filtered comma-category theorem and commutation of the associated colimits with connected finite limits, as the Stacks proof records.

I ran the mandated msearch.py tools with two phrasings, and read all returned hits. Every new search record is copied from searches.jsonl with the exact query/tool/result. Item inherited searches are retained. For the new node I read Mathlib/CategoryTheory/Sites/Pullback.lean:87--99 and 120--121: the finite-limit-preservation instances require RepresentablyFlat and Kan-extension finite-limit preservation. This does not cover the non-terminal-site statement by a one-line specialization. The other hits give sheafification exactness or adjunctions only. For the item I read Sites/Etale.lean:51 and ModuleCat/Sheaf/PushforwardContinuous.lean:139--151; these give only scheme topology and composition of already supplied continuous-site module functors. No Mathlib leaf was claimed.

For E1--E7 I checked all representability uses, the distinction between the total and small sites, and local rather than global tensor generators. The new theorem passes the empty-site test: L may carry the sole sheaf to the initial sheaf, while still preserving fibre products/equalizers. For two discrete objects mapping to the one-object site, L(X,Y)=X coproduct Y preserves these connected limits but need not preserve terminal objects. These cases explain why the terminal condition must be proved separately. For the item, empty spaces/atlases force the unique zero module sections; identity h and identity u give the identity family/tensor map; scheme spaces recover the usual big-small restriction. Non-scheme X is exactly the atlas-gluing case, and arbitrary nonflat maps were never used to preserve exactness of tensor pullback.

The off-unit tool declarations are in split_report.tool_uses, as the brief requires; no maintainer-owned top-level tool_uses field was set. They provide only generic site, chart, and tensor-adjunction infrastructure. I also followed their dependency graphs to exclude a cycle through this item. The source uses no prohibited SGA route.

## Source error

The proof of Stacks Tag 075N calls the square a square of ringed sites, whereas Tag 073N explicitly says that it is generally only a square of ringed topoi when F to G is not representable by schemes. I use only the ringed-topos commutation, exactly as the item states. In the final displayed explanation of Tag 073N, the repeated U-term should use R in the second overlap term; the proof here uses the actual Q times_X Q overlap. These are source wording/typographical issues, not changes to the item's statement.

## Not duplicates
lem-sfb-site-left-adjoint-connected-limits vs lem-per-galois-cover-module-descent: concerns Module descent along a connected finite Galois cover; it does not state preservation of fibre products and equalizers by the set-sheaf left adjoint under the new non-terminal-site hypotheses.

lem-sfb-site-left-adjoint-connected-limits vs lem-per-galois-descent-monodromy-tensor: concerns Monodromy and tensor of modules descended along a finite Galois cover; it does not state preservation of fibre products and equalizers by the set-sheaf left adjoint under the new non-terminal-site hypotheses.

lem-sfb-site-left-adjoint-connected-limits vs lem-weil-pbc-continuous-cocontinuous-topos-adjunction: gives restriction as a left exact inverse image and its RIGHT adjoint, not connected-limit preservation of the LEFT adjoint to restriction.

lem-sfb-site-left-adjoint-connected-limits vs lem-weil-pbc-etale-inverse-image-restriction: concerns Inverse image along an etale morphism is restriction; it does not state preservation of fibre products and equalizers by the set-sheaf left adjoint under the new non-terminal-site hypotheses.

lem-sfb-site-left-adjoint-connected-limits vs lem-weil-pbc-locally-constant-derived-serre: concerns Locally constant finite type sheaves form a weak Serre subcategory; it does not state preservation of fibre products and equalizers by the set-sheaf left adjoint under the new non-terminal-site hypotheses.

lem-sfb-site-left-adjoint-connected-limits vs lem-weil-pbc-site-constant-restriction: concerns Canonical restriction of constant module sheaves to a slice; it does not state preservation of fibre products and equalizers by the set-sheaf left adjoint under the new non-terminal-site hypotheses.

lem-sfb-site-left-adjoint-connected-limits vs lem-sf-open-roos-restriction-unit: concerns Restriction of the open Roos comparison through the canonical unit; it does not state preservation of fibre products and equalizers by the set-sheaf left adjoint under the new non-terminal-site hypotheses.

lem-sfb-site-left-adjoint-connected-limits vs lem-sf-prescribed-residue-cell-cone-model: concerns Cone model of a prescribed top cell over constant field coefficients; it does not state preservation of fibre products and equalizers by the set-sheaf left adjoint under the new non-terminal-site hypotheses.

lem-sfb-site-left-adjoint-connected-limits vs lem-sfb-fibred-fppf-ringed-inverse-image: treats precomposition inverse image on fibred fppf sites; it does not assert connected-limit preservation of its other left adjoint.

lem-sfb-site-left-adjoint-connected-limits vs lem-sfb-perfect-constant-derived-map-local: concerns Derived maps out of a perfect constant complex are locally algebraic; it does not state preservation of fibre products and equalizers by the set-sheaf left adjoint under the new non-terminal-site hypotheses.

lem-sfb-site-left-adjoint-connected-limits vs lem-sfb-scalar-normalized-constant-models: concerns Natural constant models from scalar-normalized module equivalences; it does not state preservation of fibre products and equalizers by the set-sheaf left adjoint under the new non-terminal-site hypotheses.

lem-sfb-site-left-adjoint-connected-limits vs lem-pur-open-small-ringed-site-coherence: concerns Coherent small open ringed-site realization and exact restriction; it does not state preservation of fibre products and equalizers by the set-sheaf left adjoint under the new non-terminal-site hypotheses.

lem-sfb-site-left-adjoint-connected-limits vs lem-pur-ring-presheaf-sheafification-localization: concerns Ring-presheaf sheafification commutes with localization of a site; it does not state preservation of fibre products and equalizers by the set-sheaf left adjoint under the new non-terminal-site hypotheses.

lem-sfb-site-left-adjoint-connected-limits vs lem-weil-proetale-weakly-etale-localization: concerns The small pro-etale site of a weakly etale X-scheme is the localization of X_proet; it does not state preservation of fibre products and equalizers by the set-sheaf left adjoint under the new non-terminal-site hypotheses.

lem-sfb-site-left-adjoint-connected-limits vs def-trf-big-small-etale-retraction-data: defines scheme retraction data; it is neither an existence theorem nor the non-terminal-site connected-limit result.

lem-sfb-site-left-adjoint-connected-limits vs lem-trf-big-small-etale-exact-retraction: is a scheme-specific exact restriction/retraction theorem, not the general connected-limit result without terminal objects.

lem-sfb-site-left-adjoint-connected-limits vs lem-trf-big-small-etale-localization-derived-pushforward: concerns Localization of big etale derived direct image and base-change compatibility; it does not state preservation of fibre products and equalizers by the set-sheaf left adjoint under the new non-terminal-site hypotheses.

lem-sfb-site-left-adjoint-connected-limits vs lem-trf-bigger-site-retraction: assumes terminal objects preserved by the inclusion; the new theorem assumes only fibre products and equalizers and concludes their preservation by the left adjoint, not a retraction.

lem-sfb-site-left-adjoint-connected-limits vs lem-trf-ringed-site-restriction-generator-data: gives exact module restriction and free-module generator Hom formulas, not connected-limit preservation of a set-sheaf left adjoint.

lem-sfb-site-left-adjoint-connected-limits vs lem-trf-site-object-derived-sections-pullback: concerns Derived sections after inverse image along a continuous cocontinuous site morphism; it does not state preservation of fibre products and equalizers by the set-sheaf left adjoint under the new non-terminal-site hypotheses.

lem-sfb-site-left-adjoint-connected-limits vs lem-trf-site-pullback-injective-evaluation-acyclic: concerns Inverse image of an injective abelian sheaf is acyclic for site-object sections; it does not state preservation of fibre products and equalizers by the set-sheaf left adjoint under the new non-terminal-site hypotheses.

lem-sfb-site-left-adjoint-connected-limits vs lem-trf-site-section-pullback-normalization: concerns Canonical site-section pullback is normalized by comparison units and replacements; it does not state preservation of fibre products and equalizers by the set-sheaf left adjoint under the new non-terminal-site hypotheses.

lem-sfb-site-left-adjoint-connected-limits vs lem-trf-topos-localization-site-presentation: concerns A small presenting site representing a prescribed topos object and its slice; it does not state preservation of fibre products and equalizers by the set-sheaf left adjoint under the new non-terminal-site hypotheses.

