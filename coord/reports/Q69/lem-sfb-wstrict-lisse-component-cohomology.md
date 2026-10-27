# Stage-1 repair: lem-sfb-wstrict-lisse-component-cohomology

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-wstrict-lisse-component-cohomology.json`: unchanged statement, six-step assembly, 2456 proof-text characters.
- `dag/nodes/sec-six-functors-basics/lem-sfb-wstrict-common-component-hypercovers.json`: statement-only unsplit geometry argument; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-component-lift-lisse-section-comparison.json`: statement-only unsplit section-comparison argument; no Mathlib match.
- `citations.json`: exact quotation for every assembly-step citation.

## Attachments

None. Read `lean/Sheaf/Paper/WStrictLisseComponentCohomology.lean`: the main theorem at line 182 and composition theorem at line 131 have `sorry`. The declaration search in `lean/WeilConjectures/` found no theorem with the item's tag or the component-lisse cohomology conclusion. No Lean was edited or compiled.

## WANTED

None. HRS and Bhatt–Scholze PDFs and Stacks sources are present.

## Return repaired

The returned nine-step proof has 8376 characters. This is a distribution of work, not a shortened replacement proof. Old steps 2-3 (2618 characters) become `lem-sfb-wstrict-common-component-hypercovers`. Old steps 4-6 (3015 characters) become `lem-sfb-component-lift-lisse-section-comparison`, with the existing contractible-derived-sections assertion still explicitly cited in parent step 3. These are comparable arguments, and both new nodes are unsplit with empty proof and proof_deps. Old steps 1, 7, 8, 9 remain parent assembly steps 1, 4, 5, 6. Parent steps 2 and 3 apply the newly exposed interfaces. The item statement, coefficient categories, geometric hypotheses, map and naturality clauses are unchanged. No unit/chapter route change or statement dispute is involved.

The sandbox initially contained only dispatcher marker files, not a prior report, citations, search log or node. The item was copied from the live read repository. Its current proof matches the return's nine steps and lengths; maintainer-owned Lean and review metadata were retained untouched.

## Searches and duplicate audit

Searched DAG statements globally for component/hypercover/Stonean/lisse/section concepts; searched the Lean library for the same concepts and the exact item tag. Ran blueprint_refs ancestor (returns None) and whole-blueprint searches `component hypercover`, `lisse evaluation`, `w-strictly local`, `w-contractible`, `Stonean`, `component`, `component-lift`, and `lisse condensed`. No blueprint node states either combined interface. New blueprint references preserve the null nearest ancestor and prepend this item to the existing via chain.

Each new node has two differently phrased LeanFinder searches, a Loogle search, a Mathlib-source grep, and a LeanSearch attempt, all run using msearch.py and retained in searches.jsonl. LeanSearch returned a rate-limit error and is recorded unavailable. LeanFinder geometry hits concern affine transition limits, with no common Stonean hypercover. Section hits give generic free-module pullback and unitHomEquiv APIs; they lack the component equivalence and its derived normalization. Read Mathlib's ModuleCat/Sheaf/PullbackFree and Sites/Hypercover/Zero sources to check this distinction. Neither new node is a one-line specialization of those hits.

## Not duplicates

lem-sfb-wstrict-common-component-hypercovers vs lem-zl-component-relative-profinite-site: the existing node constructs a single relative lift and preserves limits/covers; the new node constructs a common simplicial Stonean hypercover, proves its weak contractibility for both bases, identifies its explicit second-stage ring, and supplies the maps over h.
lem-sfb-wstrict-common-component-hypercovers vs det-pe-wc-cover-second-stage: a single ring constructed from one Stonean surjection is not a compatible simplicial hypercover over two schemes.
lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-proetale-affine-acyclic-hypercover-geometry: that theorem constructs one arbitrary affine hypercover; it does not make corresponding terms share component spaces or provide lifts of the same profinite simplicial object over h.
lem-sfb-wstrict-common-component-hypercovers vs det-pe-hypercover-formal-wcontractible: formal families over one scheme do not supply common component lifts and their natural maps over h.
lem-sfb-component-lift-lisse-section-comparison vs lem-zl-condensed-wcontractible-lisse-evaluation: the existing objectwise equivalences do not state the comparison between two different component lifts, the canonical pullback Hom square, or evaluation-on-1 normalization of the section map.
lem-sfb-component-lift-lisse-section-comparison vs lem-zl-condensed-component-pullback-compatibility: that theorem factors the fixed relative test and point inverse images for one T; it does not identify pullback between two schemes with identity on the common component Hom group.
lem-sfb-component-lift-lisse-section-comparison vs lem-proetale-finite-projective-dualizable: ordinary module duality alone does not state the derived K-flat comparison, component functor naturality or actual section-map bijection.
lem-sfb-component-lift-lisse-section-comparison vs lem-sfb-wstrict-lisse-component-cohomology: the new node proves a local Hom/underived-section comparison on w-contractible terms and its functor normalization; the item concerns ordinary derived sections on arbitrary w-strictly local affines and still needs the independent compatible hypercover construction and descent.
lem-sfb-wstrict-common-component-hypercovers vs def-weil-pbc-finite-split-hypercover-base-change: common source tag 0DAV; The existing statement concerns Base change of finite split étale hypercovers. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs def-weil-pbc-finite-split-hypercover-finite-truncation: common source tag 0DAV; The existing statement concerns Finite truncation retaining splitting and matching data. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs def-weil-pbc-finite-split-local-replacement-stage: common source tag 0DAV; The existing statement concerns Finite cofans solving covering sieves on a replacement stage. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs def-weil-pbc-finite-split-replacement-attachment-construction: common source tag 0DAV; The existing statement concerns Explicit simplicial attachment and refinement. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs def-weil-pbc-finite-split-replacement-stage: common source tag 0DAV; The existing statement concerns Finite replacement stages and their next boundary. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs def-weil-pbc-grothendieck-hypercover-pullback: common source tag 0DAV; The existing statement concerns Pullback on actual hypercover cohomology. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs def-weil-pbc-grothendieck-hypercover-stage-maps: common source tag 0DAV; The existing statement concerns Canonical stage, cone and tail comparison maps. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs def-weil-pbc-site-split-attachment-data: common source tag 0DAV; The existing statement concerns Shared split-attachment data and normalization. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs def-weil-pbc-site-split-attachment-operators: common source tag 0DAV; The existing statement concerns Explicit split-attachment operators and image-factorization identities. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-finite-etale-sieve-cover: common source tag 0DAV; The existing statement concerns Finite affine relative covers with prescribed sieve membership. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-finite-hypercover-map-extension: common source tag 0DAV; The existing statement concerns Extend a finite simplicial map after refinement. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-finite-split-hypercover-extension: common source tag 0DAV; The existing statement concerns Extend any finite split hypercover skeleton. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-finite-split-hypercover-skeleton-descent: common source tag 0DAV; The existing statement concerns Descend a finite hypercover skeleton and extend at a stage. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-finite-split-local-replacement-assembly: common source tag 0DAV; The existing statement concerns Assembly of replacement stages retaining their solving cofans. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-finite-split-local-replacement-extension: common source tag 0DAV; The existing statement concerns Successor replacement stage preserving simplicially stable sieves. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-finite-split-local-replacement-zero: common source tag 0DAV; The existing statement concerns Initial replacement stage with prescribed degree-zero sieve. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-finite-split-replacement-attachment-structure: common source tag 0DAV; The existing statement concerns Finite split and matching data on the explicit attachment. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-finite-split-replacement-boundary-attachment: common source tag 0DAV; The existing statement concerns Split simplicial attachment of a given relative boundary cover. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-finite-split-replacement-boundary-matching: common source tag 0DAV; The existing statement concerns Qcqs matching scheme for the next finite degree. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-finite-split-replacement-stage-assembly: common source tag 0DAV; The existing statement concerns Assembly of a compatible tower of replacement stages. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-finite-split-replacement-stage-extension: common source tag 0DAV; The existing statement concerns One-step finite replacement extension. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-finite-split-replacement-stage-zero: common source tag 0DAV; The existing statement concerns Initial finite replacement stage. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-hypercover-colimit-finite-refinement: common source tag 0DAV; The existing statement concerns Finite refinements give the hypercover-colimit relation. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-hypercover-stage-tower-truncation: common source tag 0DAV; The existing statement concerns Assemble a stage tower while retaining every truncation. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-replacement-stage-extension-with-truncation: common source tag 0DAV; The existing statement concerns Extend a replacement stage with its prescribed finite map. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-site-finite-basis-hypercover-existence: common source tag 0DAV; The existing statement concerns Finite-basis hypercover existence on a site with fibre products. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-site-finite-basis-hypercover-step: common source tag 0DAV; The existing statement concerns One-degree extension of a finite split basis hypercover truncation. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-site-hypercover-finite-extension: common source tag 0DAV; The existing statement concerns Attach a finite family of nondegenerate simplices to a split truncation. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-site-split-attachment-composition: common source tag 0DAV; The existing statement concerns Contravariant composition of all attachment operators. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-site-split-attachment-operators: common source tag 0DAV; The existing statement concerns Realize compatible faces by a split-attachment functor. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-wstrict-common-component-hypercovers vs lem-weil-pbc-site-split-attachment-split: common source tag 0DAV; The existing statement concerns Splitness and the new nondegenerate set from top degeneracies. It does not assert simultaneous component-controlled hypercovers over two w-strictly local affines or the explicit second-stage ring identification.

lem-sfb-component-lift-lisse-section-comparison vs lem-fix-ringed-site-perfect-duality-for-model: common source tag 08JJ; The existing statement concerns Perfect duality in a specified normalized coefficient presentation. It does not assert the coefficient-unit-normalized comparison for g between two w-contractible component lifts, including actual section pullback bijectivity and compatibility with their component equivalences.

lem-sfb-component-lift-lisse-section-comparison vs lem-fix-site-perfect-scalar-hom: common source tag 08JJ; The existing statement concerns Evaluation-normalized scalar Hom comparison for a site-perfect first variable. It does not assert the coefficient-unit-normalized comparison for g between two w-contractible component lifts, including actual section pullback bijectivity and compatibility with their component equivalences.

lem-sfb-component-lift-lisse-section-comparison vs lem-pur-completed-line-complete: common source tag 08JJ; The existing statement concerns A locally free completed coefficient line is derived complete. It does not assert the coefficient-unit-normalized comparison for g between two w-contractible component lifts, including actual section pullback bijectivity and compatibility with their component equivalences.

lem-sfb-component-lift-lisse-section-comparison vs lem-sfb-ringed-site-bounded-dual-components: common source tag 08JJ; The existing statement concerns Components and signs of the ordinary bounded dual and bidual. It does not assert the coefficient-unit-normalized comparison for g between two w-contractible component lifts, including actual section pullback bijectivity and compatibility with their component equivalences.

lem-sfb-component-lift-lisse-section-comparison vs lem-sfb-ringed-site-bounded-evaluation-assembly: common source tag 08JJ; The existing statement concerns Finite-support assembly of ordinary tensor-Hom evaluation on a ringed site. It does not assert the coefficient-unit-normalized comparison for g between two w-contractible component lifts, including actual section pullback bijectivity and compatibility with their component equivalences.

lem-sfb-component-lift-lisse-section-comparison vs lem-sfb-ringed-site-finite-retract-dual-exact: common source tag 08JJ; The existing statement concerns Internal dual and exact Hom of a finite-free retract sheaf. It does not assert the coefficient-unit-normalized comparison for g between two w-contractible component lifts, including actual section pullback bijectivity and compatibility with their component equivalences.

lem-sfb-component-lift-lisse-section-comparison vs lem-sfb-ringed-site-perfect-duality: common source tag 08JJ; The existing statement concerns Perfect-complex duality on a small ringed site. It does not assert the coefficient-unit-normalized comparison for g between two w-contractible component lifts, including actual section pullback bijectivity and compatibility with their component equivalences.

lem-sfb-component-lift-lisse-section-comparison vs lem-sfb-ringed-site-strict-perfect-hom: common source tag 08JJ; The existing statement concerns Ordinary Hom calculation for bounded finite-projective complexes on a ringed site. It does not assert the coefficient-unit-normalized comparison for g between two w-contractible component lifts, including actual section pullback bijectivity and compatibility with their component equivalences.

lem-sfb-component-lift-lisse-section-comparison vs lem-sfb-scalar-perfect-dual-realization: common source tag 08JJ; The existing statement concerns Scalar finite-projective dual realization on a ringed site. It does not assert the coefficient-unit-normalized comparison for g between two w-contractible component lifts, including actual section pullback bijectivity and compatibility with their component equivalences.

lem-sfb-component-lift-lisse-section-comparison vs lem-sfb-split-perfect-dual-tor-window: common source tag 08JJ; The existing statement concerns Signed dual models and Tor windows for split-perfect sheaf complexes. It does not assert the coefficient-unit-normalized comparison for g between two w-contractible component lifts, including actual section pullback bijectivity and compatibility with their component equivalences.

lem-sfb-component-lift-lisse-section-comparison vs lem-weil-pbc-condensed-finite-free-tensor-exact: common source tag 08JJ; The existing statement concerns Tensoring with a pro-etale locally finite free internal module preserves finite limits. It does not assert the coefficient-unit-normalized comparison for g between two w-contractible component lifts, including actual section pullback bijectivity and compatibility with their component equivalences.

lem-sfb-component-lift-lisse-section-comparison vs lem-weil-pbc-condensed-internal-hom-sections: common source tag 08JJ; The existing statement concerns Sections of internal Hom identify with additive module morphisms. It does not assert the coefficient-unit-normalized comparison for g between two w-contractible component lifts, including actual section pullback bijectivity and compatibility with their component equivalences.

lem-sfb-component-lift-lisse-section-comparison vs lem-weil-pbc-derived-coyoneda-evaluation: common source tag 08JJ; The existing statement concerns Derived additive coyoneda computes maps from a single complex. It does not assert the coefficient-unit-normalized comparison for g between two w-contractible component lifts, including actual section pullback bijectivity and compatibility with their component equivalences.

lem-sfb-component-lift-lisse-section-comparison vs lem-weil-pbc-ringed-site-locally-free-derived-hom: common source tag 08JJ; The existing statement concerns Derived maps from locally finite free sheaves via hypercohomology. It does not assert the coefficient-unit-normalized comparison for g between two w-contractible component lifts, including actual section pullback bijectivity and compatibility with their component equivalences.


## Review by Q69

I read HRS §4.1, especially the paragraph constructing (4.1), Lemma 4.1, the full proof of Proposition 4.3, (4.2), and Corollary 4.7. For the geometry work item I also read BS Lemma 2.2.8 (the relative right adjoint and finite-stage limit construction), Example 2.4.6 (Stonean cover), and Lemma 2.4.8 (the extremally disconnected criterion), plus Stacks 0DAV / lemma-hypercovering-object. For the section-comparison work item I read the HRS dualizable equivalence and Stacks 08JJ / lemma-dual-perfect-complex, including its global-Hom formula. The common-component extension and functorial map normalization are explicitly marked agent-formulated rather than claimed verbatim in those references. For descent I read Stacks 09A2 / lemma-compute-cohomology and its injective-resolution proof.

Parent step 1 uses the point-pullback theorem's identity/composition comparisons, exact module pullback's finite-limit/colimit clause, and internal-module transport's exact equivalences identifying the specified units and counits. I opened all three statements. They permit the conversion used here, with no discrete coefficient assumption. Step 2 uses the new geometry statement's actual augmented simplicial objects, full-site matching coverings, weak contractibility, and maps over h; it does not appeal merely to an unrelated choice of affine covers. Step 3 uses the lisse definition by a pulled-back trivializing cover and the new section-comparison statement for the weakly contractible U_n,V_n with common S_n. The existing contractible-derived-sections theorem explicitly computes derived sections termwise, so its degree-zero use is justified. I opened that theorem as well. The finite free modules may have varying ranks, including zero.

Step 4 uses only the specified pullback composition comparisons and the elementary inverse equation for a degreewise bijective cochain map. In step 5 I opened the normalization lemma: it expressly allows maps g_n over h without cartesian squares, applies to exact cartesian ring coefficients, and identifies the augmentation-normalized cochain map with the actual derived unit map. The sites are small in the containing universe, the matching maps are coverings, and both sets of terms are weakly contractible, exactly as required. Only bounded-below complexes of degree-zero modules are used. Step 6 uses the ringed-derived monoidal theorem's adjunction-compatible composition comparisons (not merely strong monoidality) and the normalization lemma's compatibility with composition. Thus the map is independent of hypercover choices and natural for both factorizations of a commutative diagram.

I tested empty P and empty sites (the empty product ring is the zero ring), point P with strictly henselian local affine bases, rank-zero modules, varying finite rank, h an identity, and a non-Stonean P such as Cantor space. The first new statement resolves a general P; it never assumes P itself extremally disconnected. Only S_n is Stonean, every S_n→P is surjective (including higher degrees via degeneracies), and the second-stage ring applies with exactly those hypotheses. No t-exactness of the scalar realization is assumed, which would contradict HRS Example 4.2. For the second new statement I checked coefficient-unit preservation, finite free duals, local tensor exactness/K-flatness, the actual Hom map rather than an abstract equal-cardinality assertion, and evaluation of 1. The projection-preserving test-object square is included explicitly so future work cannot hide its functoriality under a word such as “transport”.

Against delivery-errors B–E: both new statements introduce every object and state their hypotheses, cite their definition nodes, and have no proof sketch in their statement or proof fields; sources name exact tags and labels when Stacks is used. The Mathlib records are genuine logged searches, with unavailability separate. Duplicate and blueprint searches were performed before creation. All parent-step citations were opened, and citations.json uses verbatim statement text. Neither new node is the entire original claim or a two-line corollary: the geometry and normalized local comparison are independent substantive arguments of comparable workload. The full old proof is preserved below, with its citations, so none of its construction, finite-summand matching argument, duality, K-flatness, comparison, evaluation, descent or naturality work has disappeared. The parent's longest step is below 2000 characters and its total is below 3000. No source route prohibited by the brief is used.

## Complete argument handoff from the returned proof

The following text is handoff material for future workers, not proof steps in the two unsplit nodes. It retains every original argument and citation verbatim. Old steps 2–3 belong to the geometry work item; old steps 4–6 belong to the section-comparison work item, except the existing acyclicity theorem remains a parent citation. The other steps are the assembly.

### Old step 1 → parent assembly

Put $P=\pi_0(X)$ and identify $\pi_0(X')$ with $P$ using the given homeomorphism. If $P$ is empty, both schemes are empty, their section complexes are zero and the asserted map is the identity of zero. Otherwise work in the compatible small-site universes. The point-pullback comparisons give $h^{-1}\Lambda_X\cong\Lambda_{X'}$ with the specified identity/composition normalization. The exactness theorem makes module pullback exact, so $h^*M[0]$ is the degree-zero pullback and the ordinary derived adjunction in the statement applies. No completeness of coefficients enters here. The exact internal-to-section-module equivalences identify both pullback/direct-image adjunctions, including units and counits, so the sectionwise ringed-site computations below compute the stated internal module operations.

Uses: lem-weil-pbc-profinite-point-pullback, det-prop-sfb-module-pullback-exact-main, lem-sfb-internal-module-operations-transport

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Section 4.2, functoriality of the pro-etale topos; HRS Example 3.1 and construction (4.1).

### Old step 2 → lem-sfb-wstrict-common-component-hypercovers

On the category of profinite spaces over $P$, use finite jointly surjective families as coverings and extremally disconnected spaces as the basis. Every object has a singleton basis covering by the Stonean-cover theorem. Adjoining an additional arrow to a jointly surjective family preserves joint surjectivity. Thus the finite-basis hypercover theorem supplies a simplicial formal finite family of basis objects resolving $P$. In degree $n$, take its finite disjoint union $S_n$. It is again profinite and extremally disconnected: the closure of an open subset is the union of its closures in the finitely many clopen summands, each open. The simplicial family maps give actual maps between these unions. Finite matching limits distribute over these disjoint summands: a compatible tuple lies in precisely the tuple of summands indexed by its faces; this identifies the matching space with the disjoint union of the corresponding formal matching objects. Hence $S_\bullet\to P$ is a hypercover by actual profinite spaces, not an arbitrary triangulated diagram. Each $S_n\to P$ is surjective: $S_0\to P$ is surjective and any degeneracy from degree zero to degree $n$ lies over $P$.

Uses: det-pe-stonean-cover, lem-weil-pbc-site-finite-basis-hypercover-existence

Source: literature/stacks-project/hypercovering.tex; Tag 0DAV, label lemma-hypercovering-object, finite-basis construction, applied to profinite spaces; BS Example 2.4.6.

### Old step 3 → lem-sfb-wstrict-common-component-hypercovers

Apply the relative component construction to form $U_n=X\times_P S_n$ and $V_n=X'\times_P S_n$. Its finite-limit and covering assertions carry the matching coverings of step 2 to pro-etale matching coverings, so these are hypercovers of $X$ and $X'$. They are affine, with component spaces $S_n$. For each of the surjections $S_n\to P$, the second-stage w-contractible-cover theorem identifies the component lift over a w-strictly local affine with a w-contractible affine: its underlying space is $|X|\times_P S_n$, its local rings are those of $X$, and its closed points are $S_n$; the same applies to $X'$. Thus all $U_n,V_n$ are weakly contractible in the respective full sites. The two constructions give maps $g_n:V_n\to U_n$ over $h$. Indeed at each finite clopen stage pullback of the corresponding clopen subscheme of $X$ is that of $X'$; affine limits give the same assertion for $S_n$. The projections determine the maps uniquely, hence they commute with every face, degeneracy and augmentation. Their maps on components are the identity of $S_n$. Concretely, for a finite clopen partition of S_n its summands lie over closed subsets of P; the corresponding lift rings are the colimits of the clopen neighborhoods of those subsets in X. Taking the filtered colimit over refinements is exactly the ring D in the second-stage theorem. This identifies that theorem’s constructed cover with the relative component lift used here.

Uses: lem-zl-component-relative-profinite-site, det-pe-wc-cover-second-stage, det-pe-weak-contractible-equivalences

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Lemma 2.2.8 and Lemma 2.4.8; HRS Proposition 4.3(1), proof of w-contractibility of component lifts.

### Old step 4 → lem-sfb-component-lift-lisse-section-comparison

The pullbacks $M_n=M|_{U_n}$ are finite-rank lisse: pull back a trivializing cover and its finite free presentations; the same holds for $g_n^*M_n$. They are in particular locally retracts of finite free modules (use the identity as the retraction), so the finite-locally-projective duality theorem gives ordinary module duals. These duals are locally finite free as well. Tensoring with either module is exact: on each trivializing slice it is a finite direct sum of the identity, and exactness of sheaves is local. Consequently the degree-zero complexes of both modules are K-flat, since tensor with an acyclic complex is still acyclic. Their ordinary evaluation and coevaluation therefore define derived evaluation and coevaluation, with the same two triangle identities. In particular $M_n[0]$ and $g_n^*M_n[0]$ are dualizable objects, as required by the lisse evaluation equivalence; the sheaf-theoretic and derived meanings of lisse have not been silently identified.

Uses: def-sfb-lisse-coefficient-module, det-prop-sfb-module-pullback-exact-main, lem-proetale-finite-projective-dualizable

Source: literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf; Definition 3.3 and Lemma 4.5, finite free degree-zero case; ordinary duality lifted using local exactness of tensor.

### Old step 5 → lem-sfb-component-lift-lisse-section-comparison

Fix $n$ and write $S=S_n$, $U=U_n$, $V=V_n$, $g=g_n$. The component pullbacks $\pi_U^*$ and $\pi_V^*$ are equivalences on dualizable objects and preserve the coefficient unit. Moreover $g^*\pi_U^*\cong\pi_V^*$ with these unit identifications. To verify this last comparison, for a profinite $E\to S$ the finite-clopen-stage argument of step 3 gives $V\times_S E\cong V\times_U(U\times_S E)$ with both projections fixed. Thus restriction along the component test-object functors commutes with $g_*$; taking left adjoints gives $g^{-1}\pi_U^{-1}\cong\pi_V^{-1}$. The factorization of the point morphisms identifies the ring maps. Exact pullback and the ringed-derived comparison theorem then give the stated derived comparison, normalized by these adjunctions. Choose a dualizable $N$ and an isomorphism $\pi_U^*N\cong M_n[0]$ using essential surjectivity. Full faithfulness of both component functors now makes
$$\operatorname{Hom}_{D(U)}(\Lambda_U[0],M_n[0])\longrightarrow\operatorname{Hom}_{D(V)}(\Lambda_V[0],g^*M_n[0])$$
a bijection: under the two component equivalences it is the identity of $\operatorname{Hom}_{D(S)}(\Lambda_S[0],N)$. This is the actual pullback on morphisms, since the comparison sends $g^*\pi_U^*$ to $\pi_V^*$ with its specified unit.

Uses: lem-zl-condensed-wcontractible-lisse-evaluation, lem-zl-component-relative-profinite-site, lem-sfb-ringed-derived-monoidal-comparisons

Source: literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf; Proposition 4.3(3) and its proof; construction (4.1); explicit naturality for maps of component lifts.

### Old step 6 → lem-sfb-component-lift-lisse-section-comparison

The displayed Hom bijection is exactly the underived section pullback $M_n(U)\to(g^*M_n)(V)$. Apply the ringed-site derived-Hom formula with $P=\Lambda_U$, respectively $\Lambda_V$, $K=M_n[0]$, respectively $g^*M_n[0]$, and shift zero. The unit has rank one and its dual is itself. The evaluation normalization identifies a map from the unit with its value on $1$; pulling back a map pulls back this value, since the coefficient comparison carries $1$ to $1$. Thus the actual section pullback is bijective. Equivalently these are the degree-zero cohomology maps of derived sections. The contractible derived-sections theorem says that both derived section objects here are these section modules in degree zero, so there is no unproved higher-cohomology assertion in this reduction.

Uses: lem-weil-pbc-ringed-site-locally-free-derived-hom, lem-zl-contractible-derived-sections-tensor

Source: literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf; Lemma 4.1(1) and Proposition 4.3(3); section normalization via Stacks sites-cohomology.tex Tag 08JJ.

### Old step 7 → parent assembly

Let $C^n=M_n(U_n)$ and $C'{}^n=(g_n^*M_n)(V_n)$, with alternating face restrictions. The maps of step 6 commute with every face by the pullback composition comparisons, and hence define a map of nonnegative cochain complexes $c:C\to C'$. Every $c^n$ is bijective. Its degreewise inverses commute with the differentials by multiplying $d'c=cd$ on both sides by those inverses. Therefore $c$ is an isomorphism of complexes, including degree zero and rank zero, and remains an isomorphism in $D(\mathbf{Ab})$.

Uses: lem-weil-pbc-profinite-point-pullback

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Lemma 2.2.8 functoriality; HRS Corollary 4.7 descent, specialized to degree-zero complexes.

### Old step 8 → parent assembly

Apply the acyclic-hypercover pullback normalization theorem to the two full hypercovers of step 3, their maps $g_n$, and $M$. Its hypotheses hold: both sites are small in the containing coefficient universe, both coefficients are cartesian by step 1, every matching arrow is a cover, and every term is weakly contractible. The theorem identifies $c$ with the specific map induced by $M[0]\to Rh_*h^*M[0]$, under the augmentation-normalized comparisons $R\Gamma(X,M[0])\cong C$ and $R\Gamma(X',h^*M[0])\cong C'$. Step 7 therefore proves that specified map is an isomorphism. This uses bounded-below section complexes of degree-zero modules, so it makes no assumption about arbitrary unbounded totalizations or hypercomplete enhancements.

Uses: lem-sfb-acyclic-hypercover-pullback-normalization

Source: literature/stacks-project/proetale.tex; Tag 09A2, label lemma-compute-cohomology; functorial module-coefficient refinement recorded in the cited node.

### Old step 9 → parent assembly

The map used throughout is induced by the actual adjunction unit, so it is natural in $M$. For two composable scheme maps, the unit for the composite adjunction is $\eta_f$ followed by $Rf_*\eta_g$, under the canonical pullback and pushforward composition comparisons. The ringed-derived comparison theorem identifies precisely these adjunctions. Thus the map for a composite is the composite of the section pullbacks; identity maps give identity maps. Applying this equality to the two factorizations in a commutative diagram gives the claimed diagram naturality. The auxiliary resolution was used only to test this canonical map, so no choice of hypercover is part of the asserted isomorphism.

Uses: lem-sfb-ringed-derived-monoidal-comparisons, lem-sfb-acyclic-hypercover-pullback-normalization

Source: literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf; Corollary 4.7; canonical unit/composition normalization of derived pullbacks and direct images.

## Unfinished work

The two new nodes are deliberately statement-only work items for parallel future proof workers, as the return requires. No argument of the parent assembly remains unaccounted for. Dry-run and delivery results are recorded below.

Final citation cleanup: the section-comparison statement explicitly cites def-pc-kflat-complex and def-pc-tensor-complex-sheaves for its K-flat and total-tensor conventions; both existing statements were opened. This adds no hypothesis and changes no mathematical assertion or search question.
