# Stage-1 repair: lem-trf-derived-evaluation-finite-injective

1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-derived-evaluation-finite-injective.json`: unchanged statement and Lean records; five-step assembly (1950 characters), status split.
- `dag/nodes/sec-trace-formula/lem-trf-double-derived-hom-lower-bound.json`: new statement-only unsplit obligation; no Mathlib match. Computes the two derived Hom models and their support bounds for arbitrary bounded-below input and two bounded injective targets.
- `dag/nodes/sec-trace-formula/lem-trf-exact-comparison-connective-approximations.json`: new statement-only unsplit obligation; no Mathlib match. Detects invertibility using all approximations, uniform lower bounds for both image tails, long exact cohomology, and naturality.
- `citations.json`: verbatim excerpts of every statement cited in every parent step.

2. Attachments: none. The blueprint-tag and notion searches in `lean/WeilConjectures/` found no declaration proving the whole item. The current `lean/Sheaf/Algebra/Homology/DerivedEvaluationFiniteInjective.lean` states `DerivedCategory.isIso_finiteInjectiveEvaluation` with a whole-proof `sorry`. It is not finished. Existing proved tensor support infrastructure is already attached to `lem-sc-source-tor-amplitude-lower-tensor-bound`; that node is reused rather than copied.

3. WANTED: none. All mathematical sources for this repair are present locally.

4. The return requires distributing the 3427-character proof across at least two independent statement-only nodes, rather than abbreviating it. The sandbox initially contained only dispatcher brief markers, with no node, report or search log. I therefore copied the current repository item as instructed, read the current Q82 report and the live source, and retained all existing item metadata, citations in its unchanged statement, and Mathlib search records. The delivered repair changes its proof substantively. The previous report is preserved below, followed by the six old proof steps verbatim.

The existing tensor lower-bound node is more general than the proposed tensor extraction. It was found by searching the DAG and Lean source for Tor amplitude and the declaration `isGE_tensor_of_torAmplitudeIn`. Thus creating a third tensor-bound node would be a duplicate. The two new workloads are the original double-Hom model/support argument (old Steps 2 and 5) and the original final comparison/detection argument (old Step 6), with self-contained hypotheses and conclusions. Neither states evaluation invertibility or assumes pseudo-coherence; neither is a clause of the parent. Their proof work is comparable: a two-stage derived-Hom computation versus the two long exact sequences and all-degrees comparison. Their statements have 1063 and 1180 characters. Their proofs and proof dependencies are empty, as required for parallel work by later workers.

5. Nothing remains unfinished for the one-level repair. Two new unsplit obligations remain deliberately open. No Lean was written, no compiler or build was invoked, no repository or launcher file was edited, and no agents were started.

## Preservation of the original argument

- Old Step 1 remains verbatim as new Step 1: the canonical map and exact comparison are the existing canonical-map node's explicit statement.
- Old Step 2's bounded injective choices and truncation triangle remain in new Step 2. Its K-injectivity assertion is part of the double-Hom node's computation obligation: bounded injective complexes are bounded below and hence K-injective by the already existing `lem-weil-pbc-dplus-injective-representative` (2). The latter need not be an explicit parent dependency once this computation is moved to the new node. The original argument is retained below for its future worker.
- Old Step 3 remains verbatim as new Step 3, using exactly the existing pseudo-coherent evaluation theorem.
- Old Step 4 is now a citation of the existing general tensor bound, whose statement was read in full. Its proof uses precisely the old flat-model construction: obtain P supported in [a,b] by `lem-pc-module-tor-amplitude-flat-model`, make it K-flat by `lem-pc-module-bounded-flat-kflat`, compute Tot(P tensor B_n), and use r=i+j with i>=a and j>=n+1. The complete old argument remains below. It has not become a new unsplit duplicate.
- Old Step 5 is the double-Hom node's obligation. For C=Hom(B,J), nonzero degree-s factors require r>=q and r+s<=u, hence s<=u-q. For D=Hom(C,I), nonzero degree-t factors require s<=u-q and s+t>=v, hence t>=q+v-u. K-injectivity of both targets gives the two derived-category identifications explicitly asserted in the new node. Setting q=n+1 recovers the old bound, including the same c=max(-a,u-v), independent of n. Neither K-flatness of B nor projectivity of its terms is used.
- Old Step 6 is the exact-comparison node's obligation. Fix d, then choose n>=d+c, so both H^(d-1) and H^d of both tails vanish. In each long exact sequence the map induced by i_n has zero terms on either side and is invertible. The natural comparison square yields the displayed conjugacy identity. Thus all H^d(e_K) are invertible and the existing all-degrees detection theorem gives invertibility of e_K. These are separate uses of `lem-sf-derived-homology-long-exact`, `lem-weil-pbc-derived-cohomology-ladder`, and `lem-weil-pbc-unbounded-derived-iso-cohomology`; their statements were read. Naturality in K,L,M remains the final parent sentence, provided by the existing canonical-map theorem. No infinite-limit argument has replaced this degreewise proof.

## Review by NA

I read Stacks `more-algebra.tex` Tag 0A69, label `lemma-internal-hom-evaluate-isomorphism-technical`, in full. Its three hypotheses agree with the unchanged parent: finite injective dimension of each target, one Tor interval for RHom(L,M) on every module, and pseudo-coherence of every good upper truncation. Its proof first reduces along the truncation triangle, then invokes the pseudo-coherent case, and finishes with uniform lower vanishing of the two tails. The repair follows exactly that order. I also read Tag 0654 (`lemma-tor-amplitude`), the source of the reused tensor argument, and `derived.tex` Remark 08J5 (`remark-truncation-distinguished-triangle`), Lemmas 05RS (`lemma-cohomology-homological`) and 05RT (`lemma-acyclic`). I read the canonical-map and pseudo-coherent node statements in full: the former specifies the map, variance, exactness and connecting-map compatibility; the latter requires K pseudo-coherent, L bounded below and M finite injective. The new double-Hom node makes precise 0A69's second tail, using the actual Hom-complex formula read in `def-pur-derived-internal-hom` and `def-pur-hom-complex`. The new comparison node is the abstract form of 0A69's reduction sentence, with its cohomological argument expanded above; it is not attributed to a separate numbered Stacks lemma that states this exact abstraction.

New Step 1 takes exactness and signed triangle compatibility from the canonical-map statement, not from bare naturality. New Step 2 cites the full truncation assertion in `lem-weil-heart-short-exact-triangles` (1) and the representative characterization in `def-sbc-standard-tstructure-derived-category`; they really supply the asserted triangle and B_n zero below n+1. The choices J,I and bounds u,v are literal instances of hypothesis (i). Bounded J also implies the needed bounded-below L, without additional finiteness assumptions. New Step 3 checks every hypothesis of the pseudo-coherent theorem: (iii) for A_n, bounded J for L, and (i) for M. New Step 4 uses the exact conclusion of the reused tensor support node on R-modules (a braided closed monoidal Grothendieck abelian category with flat resolutions), and the exact conclusion of the new double-Hom node with q=n+1. The inequalities r<=n-c<n+1+a and r<=n-c<n+1+v-u verify the uniform bound. New Step 5 instantiates every hypothesis of the new comparison node: the same exact F,G,e from Step 1, all the distinguished triangles, all truncated isomorphisms, and one common c for all n. The final naturality assertion is taken from the canonical-map statement, which explicitly has the appropriate variance. Every use is in proof_deps, and every step/node pair has a verbatim quote in citations.json.

For B1--B9, both new statements introduce all categories, rings, complexes, bounds, maps and quantifiers; their proof and proof_deps are empty, their definition citations are literal existing definitions, and their source names a tag and TeX label. The model identifications in the double-Hom node are explicitly isomorphisms in D(R), not per-degree substitutes. The comparison node concludes invertibility of the actual morphism e_K. New nodes inherit the unchanged chapter/unit and carry the full blueprint ancestor chain with the parent prepended, and precise source-proof places. No chapter or unit route was changed, and no SGA source was used.

For C1--C8 and D1--D5, I searched the whole DAG for 0A69, double Hom, tensor support bounds, approximation comparisons, and the proved source names; ran blueprint_refs searches for double-Hom, tensor lower bound, derived evaluation, exact functors, finite injective, truncation comparison, double derived, connective approximations, and derived Hom lower; and read the potentially overlapping statements. The general heart-test theorem needs bounded-below source and lower-bound-preserving functors; it does not cover this unbounded argument with arbitrary exact functors and a fixed shift c. The existing finite Postnikov theorem proves a finite truncation, not the all-degrees conclusion here. The generic tensor node was reused. Sources carrying the same tag are distinguished below. No new node depends on the parent, so the extraction introduces no cycle. Neither helper restates the item. The exact-comparison argument is not a single elementary substitution: it has the all-n quantifier, two long exact sequences, conjugacy, and cohomological detection; the human return explicitly asks to separate this work. The earlier report's counterexample to single-truncation gluing remains relevant and is addressed by the new statement's uniform c and every n.

For E1--E7, I checked the zero ring, E=0, J=0, I=0, and all bounds equal to zero. Over a field, B concentrated in degree q, J in degree u and I in degree v gives C in degree u-q and D in degree q+v-u, so the support endpoint and signs are sharp. Allowing B to be unbounded above produces products in Hom but no extra nonzero terms outside the stated support. For the comparison node F=G and e=id is an immediate consistency check; taking A_n=K and E_n=0 is allowed; a nonzero fixed cone shifted into high degree fails the hypothesis for sufficiently large n, so the previous false single-cutoff argument is not admitted. Negative c and negative d are allowed: n>=d+c still kills d-1 and d. No Noetherian, coherent-ring, finite-generation or boundedness hypothesis on K was silently inserted.

The two new nodes were searched with genuine logged LeanFinder, Loogle and grep queries, with LeanSearch attempted and recorded unavailable because the service returned a rate limit. Each had a second LeanFinder phrasing. I read the returned support/K-injective infrastructure, exact-sequence and eventually-constant functor results: none gives either complete node in one specialization. `CochainComplex.isKInjective_of_injective` supplies only the K-injectivity subargument; derived support declarations supply only conversion from a support bound. These are not matches for the double-Hom model computation. `ComposableArrows.Exact.isIso_map'` supplies only the central exact-sequence step, not the family comparison and all-degrees detection. No unavailable query is recorded as evidence of absence. No proof step exceeds 2000 characters; the total parent proof is below the required 3000.

## Not duplicates

lem-trf-double-derived-hom-lower-bound vs lem-sf-dualizing-complex-bounded-duality: the new node gives only the model/support bound for double derived Hom, with no evaluation map, no Tor hypothesis, and no pseudo-coherence assumption; the existing node is "Bounded coherent duality for a dualizing complex", whose distinct full statement was checked.

lem-trf-double-derived-hom-lower-bound vs lem-trf-derived-evaluation-pseudocoherent: the new node gives only the model/support bound for double derived Hom, with no evaluation map, no Tor hypothesis, and no pseudo-coherence assumption; the existing node is "Pseudo-coherent derived evaluation isomorphism", whose distinct full statement was checked.

lem-trf-double-derived-hom-lower-bound vs lem-trf-finite-map-dualizing-transfer: the new node gives only the model/support bound for double derived Hom, with no evaluation map, no Tor hypothesis, and no pseudo-coherence assumption; the existing node is "Transfer of a dualizing complex along a finite ring map", whose distinct full statement was checked.

lem-trf-double-derived-hom-lower-bound vs lem-trf-complete-local-coherent-duality: the new node gives only the model/support bound for double derived Hom, with no evaluation map, no Tor hypothesis, and no pseudo-coherence assumption; the existing node is "Coherent biduality over a complete Noetherian local ring", whose distinct full statement was checked.

lem-trf-double-derived-hom-lower-bound vs lem-trf-derived-evaluation-finite-injective: the new node gives only the model/support bound for double derived Hom, with no evaluation map, no Tor hypothesis, and no pseudo-coherence assumption; the existing node is "Derived evaluation with two targets of finite injective dimension", whose distinct full statement was checked.

lem-trf-double-derived-hom-lower-bound vs lem-per-algebraic-dualizing-quotient: the new node gives only the model/support bound for double derived Hom, with no evaluation map, no Tor hypothesis, and no pseudo-coherence assumption; the existing node is "Normalized algebraic dualizing complexes for quotient local rings", whose distinct full statement was checked.

lem-trf-exact-comparison-connective-approximations vs lem-sf-dualizing-complex-bounded-duality: the new node concerns arbitrary exact functors and a natural comparison on a family of triangles, with no ring, dualizing object, or pseudo-coherence assumption; the existing node is "Bounded coherent duality for a dualizing complex", whose distinct full statement was checked.

lem-trf-exact-comparison-connective-approximations vs lem-trf-derived-evaluation-pseudocoherent: the new node concerns arbitrary exact functors and a natural comparison on a family of triangles, with no ring, dualizing object, or pseudo-coherence assumption; the existing node is "Pseudo-coherent derived evaluation isomorphism", whose distinct full statement was checked.

lem-trf-exact-comparison-connective-approximations vs lem-trf-finite-map-dualizing-transfer: the new node concerns arbitrary exact functors and a natural comparison on a family of triangles, with no ring, dualizing object, or pseudo-coherence assumption; the existing node is "Transfer of a dualizing complex along a finite ring map", whose distinct full statement was checked.

lem-trf-exact-comparison-connective-approximations vs lem-trf-complete-local-coherent-duality: the new node concerns arbitrary exact functors and a natural comparison on a family of triangles, with no ring, dualizing object, or pseudo-coherence assumption; the existing node is "Coherent biduality over a complete Noetherian local ring", whose distinct full statement was checked.

lem-trf-exact-comparison-connective-approximations vs lem-trf-derived-evaluation-finite-injective: the new node concerns arbitrary exact functors and a natural comparison on a family of triangles, with no ring, dualizing object, or pseudo-coherence assumption; the existing node is "Derived evaluation with two targets of finite injective dimension", whose distinct full statement was checked.

lem-trf-exact-comparison-connective-approximations vs lem-per-algebraic-dualizing-quotient: the new node concerns arbitrary exact functors and a natural comparison on a family of triangles, with no ring, dualizing object, or pseudo-coherence assumption; the existing node is "Normalized algebraic dualizing complexes for quotient local rings", whose distinct full statement was checked.

lem-trf-double-derived-hom-lower-bound vs lem-sf-double-hom-cone-comparison: the existing statement gives signed cone and shift isomorphisms for a repeated target; it has no bounded-injective support estimates for two different targets.

lem-trf-exact-comparison-connective-approximations vs lem-weil-pbc-heart-test-bounded-below: the existing theorem assumes bounded-below source and functors preserving lower bounds, and tests all heart objects; the new theorem permits unbounded K and arbitrary exact functors, with explicit all-n approximation hypotheses.

lem-trf-exact-comparison-connective-approximations vs lem-sfb-amplitude-truncation-family-comparison: the existing theorem is a single-functor, coproduct-family degree-m comparison under two-sided amplitude assumptions; the new theorem detects a natural transformation on K from all increasingly connective triangles, without coproduct assumptions.

lem-trf-double-derived-hom-lower-bound vs lem-trf-exact-comparison-connective-approximations: the former is a two-stage Hom model/support calculation; the latter is a functor comparison criterion given uniform tail bounds, and provides none of those bounds.

## Earlier report retained from the current repository

# Stage-1 report: lem-trf-derived-evaluation-finite-injective

1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-derived-evaluation-finite-injective.json`: split statement, unchanged mathematical statement, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-derived-evaluation-canonical-map.json`: new unsplit statement, no Mathlib match; construction and signed triangle compatibility of the general comparison, without an invertibility assertion.
- `dag/nodes/sec-trace-formula/lem-trf-derived-evaluation-pseudocoherent.json`: new unsplit statement, no Mathlib match; Stacks 0A68 (2).
- `citations.json`: verbatim statement excerpts for every step/node pair.

2. Attachments: none. I searched `WeilConjectures/` in the read-only slopmaster2 checkout for the blueprint tag and for derived evaluation, biduality, finite injective dimension and internal Hom. The project has ordinary sheaf biduality and homotopy internal-Hom infrastructure, but no declaration with all three hypotheses and the unbounded evaluation conclusion here. The upstream master is reference material only.

3. WANTED: none. The source used here is present locally.

4. The earlier sandbox was retained and compared against the current unsplit repository item. Its dry run rejected three semantic-query records because their text did not match the actual search log. I replaced those records with the exact logged queries, read the logged hits, and retained the prior item records and searches.jsonl. Additional genuine searches with second phrasings and LeanSearch were run and read. Unknown-identifier Loogle answers are now marked unavailable, rather than evidence of absence. The grep queries now give the actual query text; the searched directory is recorded separately in results.

The item agrees with Stacks `more-algebra.tex`, Tag 0A69 (`lemma-internal-hom-evaluate-isomorphism-technical`), including finite injective dimension of both targets, finite Tor dimension of RHom(L,M), and pseudo-coherence of every upper good truncation. No statement dispute or hypothesis correction was needed. I read Tags 0A67 (`lemma-internal-hom-evaluate`), 0A60 (`lemma-evaluate-and-more`), 0A68 (`lemma-internal-hom-evaluate-isomorphism`), 0654 (`lemma-tor-amplitude`), and 064J (`lemma-derived-tor-exact`), the injective-dimension definition, the Hom-complex definition, and `sites-cohomology.tex` Tag 08JC (`lemma-RHom-triangulated`). Tags 05RS/05RT and Remark 08J5 in `derived.tex` supply the cohomology and truncation interfaces used by the existing nodes.

The earlier tail helper quantified c after n; that is insufficient to pass to arbitrary degrees. The proof now fixes c=max(-a,u-v) before choosing n. The earlier triangle-gluing helper claimed an isomorphism from one lower vanishing range, and included proof text in an unsplit statement. For a fixed n, vanishing only below n-c does not control higher cohomology. For example take a comparison of triangles 0→V→V→0 and 0→0→0→0 with nonzero V supported above n-c: the first map is invertible and both tails vanish in the asserted range, but the middle map is not invertible. I removed this undelivered helper and wrote the degreewise argument in the item. I also removed the unnecessary tail helper: the tensor bound follows in a few lines from the existing flat-model and K-flatness nodes, and the double-Hom bound follows directly from the Hom-complex formula with bounded injective representatives. No source error is alleged: Stacks' argument requires, and admits, a uniform constant.

The original blueprint ancestry was restored on the item. Each remaining helper now has the full via chain with this item prepended. This preserves the algebraic duality subbranch serving the ancestor, and does not replace the ancestor's current contracting-correspondence proof. I searched all DAG nodes by evaluation/Hom and the Stacks tags, and ran blueprint_refs searches for evaluation, derived evaluation, internal-hom-evaluate, pseudo-coherent, finite injective dimension and truncation tail. None states either new input. Existing perfect-only and biduality-only results have a narrower comparison or additional hypotheses. The generic algebra and truncation tools from other units are declared in split_report.tool_uses.

5. Nothing remains unfinished for this one-level split. The two new nodes are statement-only obligations, not split themselves. Their searches return general exact-functor, t-structure, projective-resolution and ordinary module duality results, which do not provide these derived evaluation theorems in one line.

## Not duplicates

lem-trf-derived-evaluation-canonical-map vs lem-trf-derived-evaluation-finite-injective: the helper constructs the general map and its triangle compatibility with no finiteness assumptions and no isomorphism conclusion; the item proves its invertibility under three finiteness assumptions.

lem-trf-derived-evaluation-canonical-map vs lem-trf-complete-local-coherent-duality: the latter is coherent biduality over a complete Noetherian local ring with a dualizing complex; it does not construct the three-object evaluation comparison for an arbitrary ring.

lem-trf-derived-evaluation-pseudocoherent vs lem-trf-derived-evaluation-finite-injective: the helper assumes K itself pseudo-coherent and only L bounded below, whereas the item allows K unbounded above with all upper truncations pseudo-coherent and needs additional finite-injective and finite-Tor hypotheses to control the tail.

lem-trf-derived-evaluation-pseudocoherent vs lem-trf-complete-local-coherent-duality: the helper is the general three-object pseudo-coherent evaluation theorem of 0A68 (2); the latter concerns the dualizing-complex biduality map over a complete Noetherian local ring.

lem-trf-derived-evaluation-canonical-map vs lem-per-relative-bidual-triangles: states the same-target bidual map A→RHom(RHom(A,L),L); the new comparison has arbitrary distinct L,M and source RHom(L,M)⊗K, which cannot be obtained by simply specializing that bidual statement.

lem-trf-derived-evaluation-canonical-map vs lem-weil-pbc-ringed-complete-element-addition: states closure of a derived-completeness predicate under addition of coefficient elements; it constructs no three-object evaluation map.

lem-trf-derived-evaluation-canonical-map vs lem-weil-pbc-ringed-complete-element-multiplication: states closure of a derived-completeness predicate under multiplication by a coefficient; it has no evaluation comparison.

lem-trf-derived-evaluation-canonical-map vs lem-weil-pbc-ringed-internal-hom-exact-restriction: gives tensor-Hom currying, restriction and exactness, but does not give the three-object evaluation transformation or its compatibility on the connecting map. Those extra construction assertions are what the new node supplies.

lem-trf-derived-evaluation-canonical-map vs lem-coef-rational-bidual-triangle-compatibility: uses the coefficient-unit double dual and its scalar localization; it does not give the comparison with two arbitrary targets L,M.

lem-trf-derived-evaluation-canonical-map vs lem-sf-double-hom-cone-comparison: gives explicit cone and shift isomorphisms for Hom(-,I) iterated with the same I, without constructing the evaluation transformation with two targets and tensor source.

lem-trf-derived-evaluation-canonical-map vs lem-sf-etale-generic-hom-triangle: concerns the inverse-image internal-Hom base-change comparison on an etale site, not the tensor-to-double-Hom comparison over a ring.

lem-trf-derived-evaluation-canonical-map vs lem-sf-even-line-hom-shift: concerns a single internal-Hom comparison with a shifted rank-one line and an even shift; no double Hom with arbitrary L,M is stated.

lem-trf-derived-evaluation-canonical-map vs lem-pur-external-rhom-cone-pairing: pairs two global derived Hom objects after pullback to a product setting with bounded-flat test complexes; neither its objects nor its pairing are the arbitrary ring-module tensor-to-double-Hom comparison.

lem-trf-derived-evaluation-canonical-map vs lem-per-localization-dual-boundary-pairing: the existing node identifies a boundary transpose with a cup product and evaluation for a finite locally free sheaf on an etale open immersion with bounded Rj_*; it does not construct the arbitrary three-object tensor-to-double-Hom comparison over a ring or its triangle naturality. This node arrived between the successful dry run and the attempted push, and I opened its complete statement before recording this distinction.

## Review by Q82

I reviewed the resumed split against delivery-errors B–E with the node statements and the source open. The two new nodes are self-contained statements with empty proofs and proof dependencies. The canonical-map statement now writes the correct three-factor evaluation composite (the earlier search description had an incorrect source), introduces F and G, and explicitly includes exactness and compatibility on the connecting map. Its source is 0A67 and the signed construction of 0A60, with exactness from 064J and 08JC. This is a construction obligation, not the item's isomorphism claim. The pseudo-coherent node is exactly the commutative-ring instance of 0A68 (2): K pseudo-coherent, L bounded below, M represented by a bounded injective complex. It asserts invertibility of that same map. In particular it does not require finite injective dimension of L or finite Tor dimension of RHom(L,M), so it is not a relabelling of the item.

Step 1 takes both exact functors and the natural comparison from the canonical-map node's explicit statement; it does not infer triangle compatibility from bare naturality. Step 2 uses clause (2) of the existing bounded-below injective representative node, the standard t-structure's representative characterization, and clause (1) of the general heart/truncation theorem. Bounded complexes I,J satisfy its bounded-below condition; the latter two statements really give the truncation triangle and a representative B_n supported in degrees at least n+1. L is bounded below because J is bounded. This is an elementary instantiation of those stated facts.

Step 3 applies precisely the pseudo-coherent helper, with K=A_n and every hypothesis verified: pseudo-coherence is hypothesis (iii), bounded-below L was checked in Step 2, and finite-injective M is hypothesis (i). Step 4 cites the ring-module flat-model equivalence, rather than a scheme-only finite-Tor definition, and the ring-module bounded-flat K-flatness theorem. The first really gives P supported in [a,b]; the second really makes it K-flat. The total tensor definition then gives the support calculation r=i+j≥a+n+1. These are the needed existing statements, not facts taken from their proofs.

Step 5 uses only the actual product formula and K-injective-target computation in the derived-internal-Hom definition, with I,J already made K-injective in Step 2. It writes both index inequalities: r≥n+1 and r+s≤u force s≤u-n-1; then s+t≥v forces t≥n+1+v-u. Thus c=max(-a,u-v) works for both tails independently of n. The argument is the routine degree count on the very complexes that define these objects; no additional comparison or vanishing theorem is hidden in it.

Step 6 uses canonical-map triangle compatibility, exactness of the cohomology sequences, their naturality from the existing cohomology-ladder node, and the existing all-degrees cohomology isomorphism criterion. With d fixed and n≥d+c, the tail H^(d-1) and H^d vanish, so each horizontal map from the truncated value to the full value is an isomorphism. The commuting square conjugates H^d(e_A_n) into H^d(e_K). No all-degrees conclusion is taken from a single lower range. Naturality belongs to the same fixed canonical map throughout.

I tested zero K, zero L, zero M and the zero ring, all giving the unique map between zero objects. Over a field with L=M=R[0], the estimates reduce to both tails starting in degree n+1. Shifting L and M so that J is in degree u and I in degree v gives the expected n+1+v-u bound; this checks the signs and shift convention. Non-Noetherian rings are allowed: no finite-generation characterization of pseudo-coherence is used. Unbounded-above K is the reason n varies, and no boundedness of K was inserted. All six steps have fewer than 2000 characters. The report and citations were revised after removing the two unnecessary/incorrect undelivered helpers; previous searches remain in the append-only log.


## Original six proof steps retained verbatim

### Original step 1

Write $F(A)=T\otimes_R^{\mathbf L}A$ and $G(A)=R\operatorname{Hom}_R(R\operatorname{Hom}_R(A,L),M)$. By [lem-trf-derived-evaluation-canonical-map], these are exact functors and the evaluation-and-composition map $e_A:F(A)\to G(A)$ is a natural transformation compatible with shifts and distinguished triangles. This is exactly the map specified in the statement.

Uses: lem-trf-derived-evaluation-canonical-map

### Original step 2

Fix bounded injective complexes $J,I$ representing $L,M$ and integers $u,v$ with $J^r=0$ for $r>u$ and $I^r=0$ for $r<v$. They are K-injective by [lem-weil-pbc-dplus-injective-representative], clause (2). In particular $L$ is bounded below, since $J$ is bounded. For each integer $n$ take the standard truncation triangle $A_n=\tau_{\le n}K\to K\to E_n=\tau_{\ge n+1}K\to A_n[1]$, using [def-sbc-standard-tstructure-derived-category] and [lem-weil-heart-short-exact-triangles], clause (1). Its tail has a representative $B_n$ with $B_n^r=0$ for $r<n+1$, by the representative characterization in the standard t-structure.

Uses: lem-weil-pbc-dplus-injective-representative, def-sbc-standard-tstructure-derived-category, lem-weil-heart-short-exact-triangles

### Original step 3

Hypothesis (iii) says $A_n$ is pseudo-coherent for every $n$. Apply [lem-trf-derived-evaluation-pseudocoherent] with $K=A_n$, the bounded-below object $L$ of Step 2 and the finite-injective-dimension object $M$ of hypothesis (i). Thus $e_{A_n}$ is an isomorphism for every $n$.

Uses: lem-trf-derived-evaluation-pseudocoherent

### Original step 4

Fix once and for all the Tor-amplitude interval $[a,b]$ of hypothesis (ii). By [lem-pc-module-tor-amplitude-flat-model], $T$ has a bounded flat representative $P$ with terms supported in $[a,b]$. It is K-flat by [lem-pc-module-bounded-flat-kflat]. Hence $F(E_n)$ is represented by $\operatorname{Tot}(P\otimes_R B_n)$. By the total tensor formula [def-pc-tensor-complex-sheaves], a nonzero summand in degree $r$ requires indices $i\ge a$, $j\ge n+1$ and $i+j=r$. Thus this representative, and its cohomology, vanish in degrees $r<n+1+a$. The integer $a$ does not depend on $n$.

Uses: lem-pc-module-tor-amplitude-flat-model, lem-pc-module-bounded-flat-kflat, def-pc-tensor-complex-sheaves

### Original step 5

The Hom-complex formula in [def-pur-derived-internal-hom], using the K-injective representatives from Step 2, computes $R\operatorname{Hom}_R(E_n,L)$ by $C_n=\operatorname{Hom}^\bullet_R(B_n,J)$. Its degree-$s$ factors are $\operatorname{Hom}_R(B_n^r,J^{r+s})$. If such a factor is nonzero then $r\ge n+1$ and $r+s\le u$, so $s\le u-n-1$. Next $G(E_n)$ is represented by $\operatorname{Hom}^\bullet_R(C_n,I)$. A nonzero degree-$t$ factor requires $s\le u-n-1$ and $s+t\ge v$, whence $t\ge n+1+v-u$. Thus $G(E_n)$ has no cohomology below that bound. Set $c=\max(-a,u-v)$, independent of $n$. Steps 4 and 5 show that both tails have zero cohomology in every degree $\le n-c$.

Uses: def-pur-derived-internal-hom

### Original step 6

By [lem-trf-derived-evaluation-canonical-map], applying $F,G,e$ to the triangle of Step 2 gives two distinguished triangles and a commuting comparison. Fix a degree $d$ and choose $n\ge d+c$. Both tail objects have zero $H^{d-1}$ and $H^d$. In the exact cohomology sequences [lem-sf-derived-homology-long-exact], the maps $H^d(F(A_n))\to H^d(F(K))$ and $H^d(G(A_n))\to H^d(G(K))$ are therefore isomorphisms: each has zero term immediately before its source and after its target. The comparison square commutes by [lem-weil-pbc-derived-cohomology-ladder], so $H^d(e_K)$ is the conjugate of the isomorphism $H^d(e_{A_n})$ of Step 3 by these horizontal isomorphisms. This holds for every integer $d$. The cohomology criterion [lem-weil-pbc-unbounded-derived-iso-cohomology] gives that $e_K$ is an isomorphism. It is the same canonical map for all choices of $n$, so its naturality in $K,L,M$ is the naturality in Step 1.

Uses: lem-trf-derived-evaluation-canonical-map, lem-sf-derived-homology-long-exact, lem-weil-pbc-derived-cohomology-ladder, lem-weil-pbc-unbounded-derived-iso-cohomology

