# Worker report

1. Files written: `dag/nodes/sec-smooth-purity/lem-pur-clopen-finite-constructibility-bounds.json` (unchanged statement, four-step assembly); `dag/nodes/sec-smooth-purity/lem-pur-clopen-stratification-models.json` (statement, unsplit, no Mathlib match); `dag/nodes/sec-smooth-purity/lem-pur-product-tensor-test-bounds.json` (statement, unsplit, no Mathlib match). Both new nodes have no proof steps, no proof dependencies, and no proof origin. `citations.json` supplies a verbatim statement quote for every parent step use; `searches.jsonl` retains the actual command log.
2. Attachments: none. The project source search found no finished declaration for the whole item. The accepted statement in `lean/Sheaf/Paper/FiniteClopenConstructibilityBounds.lean`, `WeilConjectures.PurityFiniteSetting.finite_clopen_constructibility_bounds`, ends in `sorry`. Searches of the upstream `lean/WeilConjectures/` found no exact completed declaration for the new statements either.
3. WANTED: none.
4. Fault repaired: the human returned the 6529-character eight-step argument as too large. The sandbox initially contained only dispatcher marker files, with no retained node, report, citations or search log. I copied the current shared repository node (which has exactly the eight steps identified in the return), preserved its statement and maintainer/Lean metadata, and re-split its arguments. No target or definition changes, no statement dispute, no unit-route change, no SGA source.
5. Unfinished work: the proofs of the two new statement-only nodes intentionally belong to their future stage-1 workers. Nothing required for this repair is deferred.

## Allocation of every old argument

The new stratification/model task owns old steps 1-3 (2375 characters). This includes retrocompactness of each clopen component, constructible inverse images and images, base change of actual closed/open immersion factorizations, and restriction and union of finite stratifications with the same constant modules and trivializing covers. Its statement contains these scheme-structure and model identifications, not only the sheaf constructibility conclusion. It applies to any finite commutative coefficient ring and any scheme.

The new product tensor-test task owns the interval-detection part of old step 4 and all of steps 5-6 (2296 characters including step 4). It is a ringed-site criterion under a specified exact product decomposition and specified derived cohomology/tensor comparisons. It does not construct those comparisons, which remain in the existing module-gluing and derived-calculus siblings. It owns joint zero detection through the module equivalence, fixed cohomological support, the test by every global module, and the reverse test by every component module through zero insertion. The parent step 2 also retains the constructible-cohomology consequence of old step 4 by applying the stratification criterion to each cohomology sheaf.

The parent keeps old steps 7-8: common endpoints from finite minima/maxima; full faithfulness and essential surjectivity of the restricted equivalences; any preassigned common interval; empty components and the empty index set; the finite zero module and an empty stratification; and zero cohomology/tensor bounds for all intervals. The parent has 2280 characters of proof text, below 3000. The two extracted arguments are comparable in size, neither restates the whole item, and they are independent new proof tasks. Their extraction is the specific human request in this repair, rather than an attempt to hide ordinary elementary assembly in new nodes.

## Review by Q123

I read the current main-20261015 `def-pur-section-invariant.md` (the final invertibility assertion), its unit and chapter records, and the current `def-weil-finite-torsion-constructibility.md`. The blueprint gives the upstream reason this local argument is needed; it does not supply this entire finite-clopen proof, so the parent continues to record an agent proof. For the first new node I read Stacks topology.tex at `lemma-open-immersion-constructible-inverse-image` (005J) and `lemma-quasi-compact-open-immersion-constructible-image` (09YD), schemes.tex at `lemma-base-change-immersion` (01JY), and morphisms.tex at `lemma-base-change-closed-immersion` (01QR). For the second I read sites-cohomology.tex at `definition-tor-amplitude` (08FZ), whose quantifier is every module sheaf, and the statements of the two existing clopen algebra siblings. The second node is explicitly the agent product criterion for this definition, not a claim that 08FZ itself proves it.

In parent step 1, the new stratification/model statement supplies both actual families of immersed stratum schemes and their finite models. The cited finite-torsion definition says precisely that such a finite partition with locally constant finite stalks is constructible. The arbitrary finite ring in the new node permits specialization to A_{E,n}; the parent already fixes positive n and its finite coefficient datum. No reduced scheme structure is substituted for an existing immersed stratum. Empty strata are allowed so that intersecting strata does not spuriously change the indexing set; the empty-scheme case can use one empty stratum if the constructibility interface requires N at least one.

In parent step 2, I opened `lem-pur-clopen-ringed-module-gluing`: its statement really gives an additive exact equivalence for every commutative ring sheaf R, its exact quasi-inverse, zero insertions, and the constant-ring identifications. I opened `lem-pur-finite-product-derived-tensor-calculus`: it really gives the unbounded derived equivalence, H^m(r_iK) = r_i H^m(K), and the derived tensor comparison. These are exactly the premises of the new product tensor-test statement at R=A_X, not conclusions silently taken from the siblings' proofs. That new statement gives both fixed cohomological and Tor intervals, including arbitrary component N via e_iN; `def-weil-proetale-tor-amplitude` uses the identical all-module-sheaf degree-zero test. Applying step 1 to H^m(K) proves constructible cohomology in every degree without assuming K bounded.

In parent step 3, I read the bounded-constructible clause of `def-weil-finite-torsion-constructibility` and the finite-coefficient clause of `def-weil-finite-tor-amplitude`. They require bounded constructible cohomology and a finite Tor interval respectively; no automatic finite Tor amplitude is inferred from constructibility. With I finite and nonempty the min/max endpoints exist, enlargement of an interval preserves the defining vanishing, and step 2 supplies exactly the reverse preservation needed for the quasi-inverse. The cited derived-calculus statement supplies full faithfulness and essential surjectivity before restriction. Restricting its functors and unit/counit to the full subcategories preserves those properties. No new comparison or smallness assertion is hidden in this assembly.

In parent step 4, the statements of the module and derived siblings explicitly include zero categories and the empty partition. The finite-torsion definition accepts the finite zero model. The new product criterion explicitly includes zero objects and every ordered interval, so zero tensor vanishing is not an unsupported non-elementary citation. If I is empty the covering hypothesis forces X empty; if only some components are empty their factors are zero. No extrema of an empty family are used.

I checked B1-B10: new statements introduce all their objects and definitions, carry single-escaped TeX and exact source places, keep blueprint ancestry and empty same_as after full-blueprint searches, and have genuinely executed LeanFinder, LeanSearch, Loogle and grep records (plus a second natural-language phrasing). The hits give scheme topology, constructible subsets, cohomological t-structure results and Tor functors, not either full node. The source files for candidate matches were not claimed as leaves. DAG and blueprint searches included clopen, stratification, tensor test, tensor compatible, product decomposition, relevant Stacks tags and zero insertion. Existing stratification pullback is only one direction and does not give model transport or the union; the generic exact-monoidal derived comparison does not give interval detection.

For C1-C8, every non-elementary result in the parent has a node citation with its statement opened, and `citations.json` quotes those very statements verbatim. Uses and proof_deps agree. The only nonlocal tools used by the parent are its existing coefficient definitions; the geometric comparison lemmas remain material for the first new task, not unsupported facts in the shortened parent. The new generic task depends for meaning on the existing site-derived-tensor construction, whose statement defines the K-flat tensor on arbitrary ringed sites (the pro-etale constant-ring definition alone would not suffice for it). No new node depends on this parent, so no cycle is introduced. For D1-D4, the two separate interfaces isolate the geometry/model and tensor-test arguments; neither contains the other's argument or the parent's bounded-subcategory assembly. The human specifically required this redistribution. No new unsplit statement contains proof steps or an inline proof sketch.

For E1-E7 I checked hypotheses at their actual use. Retrocompactness uses closedness of a clopen component, not an unsupported assertion that arbitrary open subsets are quasi-compact. Immersions are actual scheme morphisms, not merely subset inclusions. The generic lemma assumes the comparison functors explicitly and does not assert an arbitrary equivalence preserves tensors. Its inverse test is e_iN in degree zero, since the exact module quasi-inverse preserves this placement. Tor testing covers all modules, including nonconstructible ones. Small cases: a singleton identity partition; two points with distinct shifts (the fixed common interval must contain both); an extra empty component; X and I both empty; the zero ring and zero module; and a nonflat residue module over O_E/varpi_E^2, which is bounded constructible but need not have finite Tor amplitude. The last case checks that the two interval notions were not conflated. No parent step is longer than 2000 characters. No Lean, compiler, build tool, repository write, direct git command or agent delegation was used.

## Not duplicates

lem-pur-clopen-stratification-models vs lem-weil-pbc-constructible-image-retrocompact-open: the existing node gives only constructibility of a subset under a retrocompact open inclusion; the new node also retains actual immersed strata, partitions and locally constant module models.

lem-pur-clopen-stratification-models vs lem-weil-pbc-constructible-in-retrocompact-open: the existing node is constructibility transitivity in a constructible subspace with a qc-open basis; it gives neither immersed scheme structures nor finite sheaf models.

lem-pur-clopen-stratification-models vs lem-weil-pbc-constructible-intersection-in-constructible: the existing node concerns the constructibility of a subset in another constructible subset; it has no strata-as-schemes or sheaf-model conclusion.

lem-pur-clopen-stratification-models vs lem-weil-pbc-constructible-open-restriction: the existing node gives only constructibility of the intersection of a subset with an open; it gives neither the scheme structure nor the union/model conclusions.

lem-pur-clopen-stratification-models vs lem-weil-pbc-etale-stratification-local-gluing-core: the existing node gives some refinement over an affine open cover; it does not retain precisely the original component strata, their scheme structures and trivializations.

lem-pur-clopen-stratification-models vs lem-weil-pbc-limit-contained-in-constructible: the existing node is eventual containment of inverse-system images in a constructible set; the new node concerns actual clopen partition strata and module models.

lem-pur-clopen-stratification-models vs lem-sf-locally-closed-closure-adjoint-realization: the existing node compares two extension factorizations through a scheme-theoretic closure and their adjoints; the new node constructs restricted and union strata with finite module models.

lem-pur-clopen-stratification-models vs lem-sf-native-adic-qcqs-stratification: the existing node globalizes a native adic lisse stratification on a qcqs scheme; the new node transports immersed strata and finite discrete models across a specified clopen partition.

lem-pur-clopen-stratification-models vs lem-pur-clopen-finite-constructibility-bounds: the parent combines finite-clopen geometry, fixed cohomological/Tor bounds and bounded-subcategory equivalences at A_{E,n}; this new node isolates only one underlying argument and is not the full parent.

lem-pur-clopen-stratification-models vs lem-sf-constructible-partition-local-closed-stratum: the existing node finds an affine neighborhood with one stratum closed; it does not transport whole stratifications and module trivializations across a clopen partition.

lem-pur-product-tensor-test-bounds vs lem-exc-intrinsic-resolution-tensor-homology: the existing node compares tensor cohomology in two fixed finite-coefficient module presentations; the new node detects all component intervals under a product equivalence on arbitrary ringed sites.

lem-pur-product-tensor-test-bounds vs lem-exc-intrinsic-tor-amplitude-transport: the existing node transports a Tor predicate through one specified intrinsic realization; it does not supply product zero detection or arbitrary component test insertion.

lem-pur-product-tensor-test-bounds vs lem-sf-complete-residue-cohomology-bounds: the existing statement concerns Cohomological bounds for a complete complex from residue Tor amplitude; it has no exact product decomposition hypothesis with zero insertions and does not give both prescribed cohomological and Tor interval equivalences for arbitrary ringed sites.

lem-pur-product-tensor-test-bounds vs thm-sf-direct-image-tor-amplitude: the existing statement concerns Direct image and finite Tor amplitude; it has no exact product decomposition hypothesis with zero insertions and does not give both prescribed cohomological and Tor interval equivalences for arbitrary ringed sites.

lem-pur-product-tensor-test-bounds vs lem-sf-finite-discrete-encoding-tensor-tor: the existing statement concerns Derived tensor and Tor under normalized coefficient encoding; it has no exact product decomposition hypothesis with zero insertions and does not give both prescribed cohomological and Tor interval equivalences for arbitrary ringed sites.

lem-pur-product-tensor-test-bounds vs lem-sf-open-tor-bound-finite-constant-tests: the existing statement concerns Finite constant-module Tor tests for an open direct image; it has no exact product decomposition hypothesis with zero insertions and does not give both prescribed cohomological and Tor interval equivalences for arbitrary ringed sites.

lem-pur-product-tensor-test-bounds vs lem-sfb-constant-field-tor-bounds: the existing statement concerns Tor bounds over a constant field sheaf; it has no exact product decomposition hypothesis with zero insertions and does not give both prescribed cohomological and Tor interval equivalences for arbitrary ringed sites.

lem-pur-product-tensor-test-bounds vs lem-sfb-proetale-tor-local-global: the existing node equates global finite Tor dimension and local finite Tor dimension on a quasi-compact scheme; it does not give the same prescribed interval through an abstract product equivalence.

lem-pur-product-tensor-test-bounds vs def-kun-tor-amplitude: the existing statement concerns Tor amplitude; it has no exact product decomposition hypothesis with zero insertions and does not give both prescribed cohomological and Tor interval equivalences for arbitrary ringed sites.

lem-pur-product-tensor-test-bounds vs def-weil-finite-tor-amplitude: the existing statement concerns Finite Tor amplitude; it has no exact product decomposition hypothesis with zero insertions and does not give both prescribed cohomological and Tor interval equivalences for arbitrary ringed sites.

lem-pur-product-tensor-test-bounds vs def-weil-proetale-tor-amplitude: the existing node defines the predicate on a constant-ring pro-etale site; it does not prove any product detection theorem.

lem-pur-product-tensor-test-bounds vs lem-sf-proetale-residue-tor-test: the existing statement concerns The residue test on the pro-étale site; it has no exact product decomposition hypothesis with zero insertions and does not give both prescribed cohomological and Tor interval equivalences for arbitrary ringed sites.

lem-pur-product-tensor-test-bounds vs lem-sp-supported-etale-tensor-origin: the existing statement concerns Bounded etale tensor origin for an open-supported finite-Tor complex; it has no exact product decomposition hypothesis with zero insertions and does not give both prescribed cohomological and Tor interval equivalences for arbitrary ringed sites.

lem-pur-product-tensor-test-bounds vs lem-sp-supported-scalar-tor-interval: the existing node concerns scalar extension and open extension with etale origin; it does not identify all component tests for a product equivalence.

lem-pur-product-tensor-test-bounds vs lem-weil-finite-ctf-triangulated: the existing statement concerns Finite-stage finite-Tor-amplitude complexes form a triangulated subcategory; it has no exact product decomposition hypothesis with zero insertions and does not give both prescribed cohomological and Tor interval equivalences for arbitrary ringed sites.

lem-pur-product-tensor-test-bounds vs lem-weil-integral-ctf-triangulated: the existing statement concerns Integral finite-Tor-amplitude complexes form a triangulated subcategory; it has no exact product decomposition hypothesis with zero insertions and does not give both prescribed cohomological and Tor interval equivalences for arbitrary ringed sites.

lem-pur-product-tensor-test-bounds vs lem-weil-proetale-tor-interval-shift: the existing node handles shifts, isomorphisms and zero tensors; it does not prove componentwise interval detection.

lem-pur-product-tensor-test-bounds vs lem-weil-proetale-tor-interval-triangle: the existing statement concerns Tensor cohomology segments and quantitative Tor bounds for a pro-etale triangle; it has no exact product decomposition hypothesis with zero insertions and does not give both prescribed cohomological and Tor interval equivalences for arbitrary ringed sites.

lem-pur-product-tensor-test-bounds vs sk-def-sp-normalized-towers: the existing statement concerns Constructible and normalized towers; it has no exact product decomposition hypothesis with zero insertions and does not give both prescribed cohomological and Tor interval equivalences for arbitrary ringed sites.

lem-pur-product-tensor-test-bounds vs sk-d-setup: the existing statement concerns Coefficients and geometric categories; it has no exact product decomposition hypothesis with zero insertions and does not give both prescribed cohomological and Tor interval equivalences for arbitrary ringed sites.

lem-pur-clopen-stratification-models vs lemma-constructible-pullback-stratification: the existing theorem only pulls back a stratification; the new node additionally assembles the exact component strata as schemes and preserves the finite local module models and covers.

lem-pur-clopen-stratification-models vs lem-fin-normal-clopen-constructible-module: the existing statement constructs a sheaf from modules constant on entire components on the etale site; it does not handle arbitrary pro-etale constructible sheaves with nontrivial component stratifications.

lem-pur-clopen-stratification-models vs lem-sf-finite-cover-ctf-locality: the existing statement gives one gluing direction for Noetherian finite open covers and bounded complexes; the new statement gives the actual strata and their original scheme structures and models on arbitrary schemes in both directions.

lem-pur-product-tensor-test-bounds vs lem-sfb-tor-interval-local-detection: the existing statement gives locality implications for a scheme cover or open/closed pair, not fixed support equivalence and reverse testing through arbitrary exact product decompositions.

lem-pur-product-tensor-test-bounds vs lem-sfb-exact-monoidal-equivalence-total-kflat: the existing statement constructs tensor comparisons and transports K-flatness; the new node assumes derived comparisons and proves interval detection by every module test.

lem-pur-product-tensor-test-bounds vs new-lem-kun-exact-monoidal-equivalence-derived: the existing statement constructs a monoidal derived equivalence; it does not assert a product interval criterion with component zero insertions.

lem-pur-product-tensor-test-bounds vs lem-pur-finite-product-derived-tensor-calculus: the existing sibling supplies the unbounded geometric derived equivalence and its comparisons, not either fixed-interval conclusion; the new generic criterion takes such comparisons as hypotheses.

## Original argument preserved verbatim

The following is the returned proof text, retained in full as the work briefs for the extracted arguments and the assembly. These are report material, not proof steps inside either unsplit node.

### Old step 1: lem-pur-clopen-stratification-models

First check the strata as subschemes, not only as point sets. Each clopen $X_i$ is retrocompact in $X$: its intersection with a quasi-compact open $W$ is closed in $W$, hence quasi-compact. A constructible stratum $S\subset X$ restricts to a constructible subset of $X_i$ by [lem-weil-pbc-constructible-open-restriction]. Write its immersion as a closed immersion $S\hookrightarrow V$ followed by an open immersion $V\hookrightarrow X$. Base change along $X_i\hookrightarrow X$ gives a closed immersion $S\times_X X_i\hookrightarrow V\times_X X_i$ and an open immersion $V\times_X X_i\hookrightarrow X_i$ by the two cited base-change lemmas. Thus the restricted stratum is an actual locally closed subscheme. Conversely, a stratum $T\hookrightarrow X_i$ factors as $T\hookrightarrow V\hookrightarrow X_i$ with the first arrow closed and the second open. The same $V$ is open in $X$ (the open subsets and restricted structure sheaves agree), so this is a locally closed immersion into $X$. Its image is constructible in $X$ by [lem-weil-pbc-constructible-image-retrocompact-open], since $X_i$ is retrocompact open. These constructions retain the original subscheme structures.

Cited nodes: def-weil-open-immersion, def-weil-closed-immersion, lem-weil-pbc-open-immersion-base-change, lem-weil-pbc-closed-immersion-base-change, lem-weil-pbc-constructible-open-restriction, lem-weil-pbc-constructible-image-retrocompact-open.

### Old step 2: lem-pur-clopen-stratification-models

Suppose $F$ is constructible. Choose its finite disjoint stratification $X=\bigsqcup_\nu S_\nu$ from [def-weil-finite-torsion-constructibility]. For fixed $i$, the strata $S_\nu\times_X X_i$ of step 1 are finite in number, disjoint and cover $X_i$. Restrict a pro-etale covering trivializing $F|_{S_\nu}$ to the open subscheme $S_\nu\times_X X_i$: by the base-change covering axiom of the site it is still a covering, with precisely the same finite constant module on each restricted trivialization. Thus the local constant finite-module models remain valid, and $F|_{X_i}$ is constructible. Empty strata may be omitted.

Cited nodes: def-weil-finite-torsion-constructibility, def-weil-pbc-proetale-site.

### Old step 3: lem-pur-clopen-stratification-models

Conversely, for each $i$ choose a finite disjoint constructibility stratification $X_i=\bigsqcup_{\nu\in J_i}S_{i,\nu}$ for $F|_{X_i}$. The finite set $\bigsqcup_{i\in I}J_i$ indexes a disjoint covering stratification of $X$; its strata are locally closed and constructible in $X$ by step 1. The restriction of $F$ to $S_{i,\nu}$ is exactly the restriction of $F|_{X_i}$ to that same subscheme. Hence the chosen locally constant finite-module model and its trivializing cover apply without change. This proves the reverse implication by [def-weil-finite-torsion-constructibility].

Cited nodes: def-weil-finite-torsion-constructibility.

### Old step 4: lem-pur-product-tensor-test-bounds (constructible-cohomology consequence stays in parent step 2)

Apply [lem-pur-clopen-ringed-module-gluing] with $R=A_X$. It identifies $R|_{X_i}$ with $A_{X_i}$ and gives the exact module restriction equivalence with zero insertions $e_i$. In particular a module sheaf is zero if all its restrictions are zero: under the displayed quasi-inverse its sections are the product of zero modules. By [lem-pur-finite-product-derived-tensor-calculus], degreewise restriction induces the unbounded derived equivalence and $H^m(r_iK)\cong r_iH^m(K)$ for every integer $m$. Consequently $H^m(K)=0$ iff every $H^m(r_iK)=0$. Apply this separately for each $m\notin[a,b]$ to get precisely the claimed fixed cohomological interval. Apply the sheaf equivalence established in steps 2 and 3 to each $H^m(K)$ to get the assertion about constructible cohomology.

Cited nodes: lem-pur-clopen-ringed-module-gluing, lem-pur-finite-product-derived-tensor-calculus.

### Old step 5: lem-pur-product-tensor-test-bounds

Assume all $r_iK$ have Tor amplitude in the same $[a,b]$. Let $M$ be any $A_X$-module sheaf in degree zero. The tensor comparison of [lem-pur-finite-product-derived-tensor-calculus] identifies
$$r_i(K\otimes_A^{\mathbf L}M)\cong r_iK\otimes_A^{\mathbf L}r_iM.$$
Exact degreewise restriction leaves $r_iM$ in degree zero. The right side therefore has zero cohomology outside $[a,b]$ by the component Tor hypothesis and [def-weil-proetale-tor-amplitude]. For every $m\notin[a,b]$, step 4 detects the vanishing of $H^m(K\otimes_A^{\mathbf L}M)$ from these component vanishings. Since $M$ was arbitrary, this is exactly Tor amplitude of $K$ in $[a,b]$.

Cited nodes: lem-pur-finite-product-derived-tensor-calculus, def-weil-proetale-tor-amplitude.

### Old step 6: lem-pur-product-tensor-test-bounds

Assume instead that $K$ has Tor amplitude in $[a,b]$. Fix $i$ and any $A_{X_i}$-module sheaf $N$ in degree zero. Use the module zero insertion $M=e_iN$ from [lem-pur-clopen-ringed-module-gluing], also placed in degree zero. Its $i$th restriction is $N$, and its other restrictions are zero. The global Tor hypothesis says $K\otimes_A^{\mathbf L}M$ has cohomology only in $[a,b]$. Restricting this complex and using the cohomology and tensor comparisons of [lem-pur-finite-product-derived-tensor-calculus] gives
$$r_i(K\otimes_A^{\mathbf L}e_iN)\cong r_iK\otimes_A^{\mathbf L}N,$$
again concentrated in $[a,b]$. Because every $N$ was permitted, [def-weil-proetale-tor-amplitude] gives the required Tor interval for $r_iK$. This proves the other implication without assuming that an arbitrary component test object was originally the restriction of a globally given one.

Cited nodes: lem-pur-clopen-ringed-module-gluing, lem-pur-finite-product-derived-tensor-calculus, def-weil-proetale-tor-amplitude.

### Old step 7: parent assembly

The equivalence of [lem-pur-finite-product-derived-tensor-calculus] is fully faithful on all objects and essentially surjective on tuples. By step 4 and [def-weil-finite-torsion-constructibility], a complex is bounded constructible exactly when all its component complexes are: in the reverse direction choose component cohomological intervals $[c_i,d_i]$ and, for nonempty finite $I$, use $c=\min_i c_i$, $d=\max_i d_i$. Vanishing outside $[c_i,d_i]$ implies vanishing outside $[c,d]$, so step 4 applies to any inverse image of the tuple. Likewise, for a tuple in $D^b_{ctf}$, choose component Tor intervals $[u_i,v_i]$ as in [def-weil-finite-tor-amplitude], enlarge them to $[\min_i u_i,\max_i v_i]$, and apply step 5. Step 6 proves preservation in the forward direction. Thus this equivalence restricts to both asserted full subcategories. The same argument uses any preassigned common cohomological or Tor interval, proving the final assertion about bounds, not just the existence of some bounds.

Cited nodes: lem-pur-finite-product-derived-tensor-calculus, def-weil-finite-torsion-constructibility, def-weil-finite-tor-amplitude.

### Old step 8: parent assembly

The empty cases require no minimum or maximum. Empty components have zero module categories by [lem-pur-clopen-ringed-module-gluing] and zero derived categories by [lem-pur-finite-product-derived-tensor-calculus]. If $I$ is empty the covering condition forces $X$ empty, so the unique derived object is zero. The zero sheaf is locally constant with the finite zero module as its model, hence constructible by [def-weil-finite-torsion-constructibility]; on the empty scheme one can use the empty stratification. Its cohomology in every degree is zero. Tensoring its zero complex with any complex gives the zero complex, so [def-weil-proetale-tor-amplitude] holds for every interval $[a,b]$. Thus all the assertions, including the subcategory equivalences and arbitrary common bounds, hold also for empty $X$, empty $I$, and covers containing empty components.

Cited nodes: lem-pur-clopen-ringed-module-gluing, lem-pur-finite-product-derived-tensor-calculus, def-weil-finite-torsion-constructibility, def-weil-proetale-tor-amplitude.

