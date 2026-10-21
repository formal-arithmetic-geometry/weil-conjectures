# Repaired stage-1 re-split: lem-sfb-bounded-bifunctor-devissage

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-bounded-bifunctor-devissage.json: unchanged statement and live Lean/review fields; three proof steps, 1888 characters total.
- dag/nodes/sec-six-functors-basics/lem-sfb-bounded-postnikov-extension-generation.json: one revised statement-only unsplit node; no proof or proof dependencies; no Mathlib match.
- citations.json: fresh verbatim quotations for every step citation. searches.jsonl retains all prior searches and the newly executed searches.

## Attachments

No exact item declaration was found under lean/WeilConjectures by its blueprint tag or bounded_bifunctor_devissage/bounded_functor_devissage names. Sheaf.CategoryTheory.DerivedCategory.BoundedBifunctorDevissage contains the already landed, sorry-free item; its metadata is preserved. The explicit latest route note requires reopening stage 1 despite this completion, and is the authorization for this repair.

DerivedCategory.iteratedExtensions_of_isGE_of_isLE and DerivedCategory.exists_iteratedExtensions_of_bounded in lean/WeilConjectures/CategoryTheory/DerivedCategory/BoundedEssentiallySmall.lean:69,107 state the OLD extracted derived-category property. I read their bodies and agree with B10: that extraction was closed work. They do not state the revised node: an ordered tower with factors the particular object's own t-cohomology, for an arbitrary triangulated category equipped with any t-structure. No equivalence with a derived category of the heart is assumed or available in general. The revised node therefore is not attached to those declarations.

## WANTED

None.

## Corrections and return points

A7: I compared the sandbox and current live node; only proof, proof_deps, proof_origin and split_report differed before repair. I used the current live node as the base of the rewritten parent, preserving statement, lean, reviewed, reviewed_lean and reviewed_proof. The supplied latest route note explicitly says this is a deliberate re-split even though the live theorem is proved; it supersedes the return's stale-assignment conclusion for this task. I do not withdraw or overwrite the landed Lean proof.

B10: I replaced the old new-node statement, not merely its prose or status. Its hypothesis is now a triangulated category with an arbitrary t-structure and an object with actual finite t-bounds. Its conclusion is a finite ordered tower, starting at zero and ending at that object, with specified own-cohomology factors and intermediate truncation identifications. It no longer states the existing iteratedExtensions_of_isGE_of_isLE theorem. The new node is a genuine structural construction from BBD, not a clause of the two-variable item. The existing id is retained because this is a repair of its unmerged statement. The archived old report below remains evidence of the previous attempt, not a claim that its old statement is being delivered.

C5 (advisory): I read lem-sfb-degreewise-bounded-devissage and its source prop_of_isGE_of_isLE_of_degreewise in full. It can shorten each image induction, as the reviewer says. It gives a property Q(K) in a derived category; it gives neither the ordered tower nor the arbitrary-t-structure assertion. The mandatory latest re-split instruction asks to expose a substantive construction as new work. I keep the two short image inductions in the item and move their shared tower construction into the revised node, rather than creating another property-propagation lemma. This keeps the old truncation route.

## Review by NA

I read Stacks derived.tex:4075-4108 (Tag 08J5, remark-truncation-distinguished-triangle) in full, the current blueprint operations proof paragraph (2), the integral-model unit and six-functors-basics chapter, and the live BoundedBifunctorDevissage.lean. I also read BBD pp.29-34 (PDF pp.30-35): Proposition 1.3.3 constructs canonical truncation triangles; 1.3.4 gives zero truncations outside bounds; 1.3.5 identifies the two orders of interval truncation; 1.3.6 defines the heart-valued cohomology and identifies it with ordinary cohomology in the derived-category example; 1.3.13 spells out the finite ordered triangle sequence. Stacks supplies the exact shifted-cohomology triangle in the standard derived case. BBD is not an SGA source. The parent remains on its finite truncation route.

The revised node's intended argument is as follows. Put L_j=tau_LE(a+j-1)K. Since K is at least a, L_0 is zero. Since K is at most a+n-1, the final truncation map is an isomorphism to K. For j<n put q=a+j. Apply the truncation triangle at q-1 to tau_LE(q)K. Commutation/idempotence of the truncations identifies its first vertex with tau_LE(q-1)K and its third with tau_GE(q)tau_LE(q)K=H_t^q(K)[-q]. These are successive distinguished triangles, not a direct-sum splitting. For n=0, the crossed bounds force id_K=0 by t-orthogonality and hence K is zero; no triangle is needed. This construction is precisely the argument removed from the parent and left for another worker; the new node has no proof steps. Restricting to the standard derived t-structure gives the factors H^q(K)[0][-q] by BBD's derived-category example. No realization equivalence is asserted.

I checked all citations against their statements, not proofs. Step 1 cites def-weil-triangulated-category for additive exact functors and their shift/triangle preservation, and def-weil-triangulated-subcategory for zero, all shifts and extension closure. The zero argument is written explicitly, and strict fullness is a hypothesis of the item. Step 2 cites the new node for the entire finite tower, both endpoints, and the ordinary-cohomology factor identification; def-sbc-standard-tstructure-derived-category supplies the t-structure and translates the given cohomological bounds into its actual bounds. The exact-functor and subcategory definitions supply the image triangle and closure. Nonzero H^r(M) uses exactly h_MB and the original pair hypothesis, while zero cohomology uses additivity. The image induction has a zero base, a single explicit extension step and an endpoint isomorphism. Step 3 uses the same statements with the other exact partial functor; step 2 supplies the needed degree-zero images when H^q(K) is nonzero. No joint exactness or exchange of variables is assumed. Each cited conclusion is quoted verbatim in citations.json.

For the revised structural statement I checked n=0, n=1, negative a, cohomological gaps and K=0. At n=1 the sole triangle is 0 -> K -> H_t^a(K)[-a]; at n=0 crossed actual bounds force zero even for a degenerate t-structure. I deliberately require actual t-bounds, not merely vanishing t-cohomology, which would fail for a degenerate t-structure. For the item, I checked K=0, M=0, acyclic inputs and empty classes: zero images are included independently of class membership. The original classes need not contain zero or be invariant under isomorphism. No target or item statement changed and no STATEMENT-DISPUTED correction was needed.

I checked B-E against the files: self-contained objects and notation, definitions cited, no proof inside the unsplit node, no proof-dependency cycle, source places read, no SGA route, and no uncited non-elementary identification in the assembly. The shared tower is strictly smaller than the bifunctor result and does not mention a bifunctor, image subcategory or membership conclusion. Each parent step is below 2000 characters and the total is below 3000. Existing closed derived-category results have been recorded as such instead of treated as unfinished.

For Mathlib I read the existing searches.jsonl and retained its results; I ran fresh leanfinder, leansearch, loogle and grep searches for the changed arbitrary-t-structure question and the ordered-tower formulation. I read the hits in TStructure/Basic.lean (exists_triangle:79 and bounded:266), TruncLTGE.lean (triangleLTGE:296 and distinguished:299), Heart.lean (heart:45), and Subcategory.lean (extensionProduct:208, extensionProductIter_succ:351 and closure:431). They give one-cut triangles, bounds, heart objects or extension closure, not the finite ordered own-cohomology tower. They are components for the next worker. The old derived-category searches are retained with their old verdicts; the new records are the actual command-log queries. No failed service is counted as absence.

## Not duplicates

lem-sfb-bounded-postnikov-extension-generation vs lem-sfb-degreewise-bounded-devissage: the latter propagates a property Q on a derived category; the former constructs ordered triangles with prescribed factors for any t-structure, without a derived realization hypothesis.

lem-sfb-bounded-postnikov-extension-generation vs lem-sfb-bounded-cohomology-cone-witness: the latter is an unordered finite construction list allowing arbitrary shifts and cones in D(A); the former gives exactly n ordered triangles of successive t-cohomology for any t-structure.

lem-sfb-bounded-postnikov-extension-generation vs lem-kun-canonical-truncation-filtration: the latter concerns termwise bounded module complexes and filtered chain homotopies; the former concerns actual t-bounded objects in an arbitrary triangulated category, without complex representatives.

lem-sfb-bounded-postnikov-extension-generation vs lem-kun-derived-canonical-filtration: the latter constructs a functor to a localized filtered category for R-modules; the former needs neither modules nor filtered derived categories and constructs a finite tower in the original category.

lem-sfb-bounded-postnikov-extension-generation vs lem-weil-pbc-truncation-triangle: the latter states one standard-derived truncation triangle, with naturality and uniqueness; the former gives the finite ordered tower and its endpoints for an arbitrary t-structure.

lem-sfb-bounded-postnikov-extension-generation vs lem-weil-pbc-truncation-descends: the latter descends ordinary complex truncations through localization; the former starts with an arbitrary t-structure and asserts finite ordered own-cohomology generation.

lem-sfb-bounded-postnikov-extension-generation vs def-weil-t-structure: a definition of the t-structure and its one-cut truncations does not state the successive-cohomology tower and its finite endpoints.

lem-sfb-bounded-postnikov-extension-generation vs lem-weil-envelope-tstructure: the latter constructs a t-structure on the Karoubi envelope, not a finite tower for an arbitrary given t-bounded object.

lem-sfb-bounded-postnikov-extension-generation vs prop-weil-heart-abelian: the latter proves the heart is abelian, not finite ordered generation by the given object's cohomology.

lem-sfb-bounded-postnikov-extension-generation vs thm-weil-karoubian-bounded-t: idempotent completeness of an entire bounded t-category is different from a finite explicit tower for an individual bounded object, including when the ambient t-structure is unbounded.

## Unfinished work

Only the intentionally statement-only new structural node is left to subsequent stage-1 work. No Lean was written, no compile/build/Lake tool was run, and no repository or launcher file was changed. The current dry run and push are reported by their actual command outputs.

## Preserved previous report (superseded extraction)

The following prior report and searches are retained as required by the repair brief. Its old quantitative derived-category statement and its old E_d assembly are superseded by the repair above; statements of successful prior checking below are historical.

# Stage-1 re-split: lem-sfb-bounded-bifunctor-devissage

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-bounded-bifunctor-devissage.json: statement unchanged; three assembly steps, 2063 characters total.
- dag/nodes/sec-six-functors-basics/lem-sfb-bounded-postnikov-extension-generation.json: one new statement-only unsplit node, no proof steps, no proof dependencies; no Mathlib match. It constructs a finite iterated-extension witness with the quantitative length d, rather than repeating the two-variable conclusion.
- report.md and citations.json; searches.jsonl is the unaltered msearch.py log. original-item.json preserves the live starting copy in the sandbox only.

## Attachments

No project declaration under lean/WeilConjectures states the bifunctor item. I searched its blueprint tag and bounded/bifunctor/devissage notions. The live Sheaf module has the item and a private helper, but the assignment explicitly reopens that stage-1 split and excludes Sheaf-only declarations as ATTACH answers.

The extracted generation fact has existing source implementations: DerivedCategory.iteratedExtensions_of_isGE_of_isLE (lean/WeilConjectures/CategoryTheory/DerivedCategory/BoundedEssentiallySmall.lean:67) gives its quantitative clause; DerivedCategory.exists_iteratedExtensions_of_bounded (same file:107) gives its bounded consequence. Their bodies contain no sorry. DerivedCategory.singleObjects at line 39 and iteratedExtensions at line 43 define the recursive classes; singleFunctor in degree n is X[0][-n] via singleFunctors.shiftIso. These declarations are available for the maintainer to attach; I deliver the new node statement-only with status unsplit as the explicit re-split instruction requires, and do not change Lean or maintainer-owned audit fields. The source file's final essentially-small conclusion is not used as a substitute for these statements.

## WANTED

None. The Stacks source and the current blueprint are present.

## Corrections and scope

This is the deliberate 2026-10-21 re-split, not an attempt to supersede the existing reviewed split. The starting live JSON already uses a private one-variable helper and cites fully proved project extension results in prose, but has no node for that non-elementary generation fact. Those direct source references are now represented by the new self-contained generation node. The parent statement, all its hypotheses, the chapter and unit, its blueprint fields and Lean metadata are retained. The obsolete tool-use requests for truncation-descends and truncation-triangle are no longer needed by the assembly: their mathematical construction belongs below the new generation node. No top-level tool_uses was changed.

I initially considered extracting a one-variable closure lemma, then found lem-sfb-degreewise-bounded-devissage and rejected that duplicate. I extracted the stronger, constructive finite iterated-extension witness with its length bound instead. I did not create nodes for inverse-image closure, zero preservation, shifted-single identifications or the elementary extension-closure induction.

## Review by NA

I read the current blueprint's sk-lem-integral-models unit and chapter and the operations proof at literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-integral-models/sk-lem-integral-models-operations.proof.md, particularly its tensor paragraph (2). This node remains the generic bounded-complex passage used by the parent's tensor argument, and no coefficient category, tensor operation or route is changed. I read Stacks derived.tex:4075-4108, Tag 08J5, label remark-truncation-distinguished-triangle, including its successive upper-truncation triangle. I also read the full source generation implementation at BoundedEssentiallySmall.lean:33-123 and the live BoundedBifunctorDevissage.lean, not merely their docstrings.

For the new node, the substantive argument is finite Postnikov induction with the exact quantitative count. At d=0, a complex with cohomology only in degree a is isomorphic to the object H^a(K) placed in degree a; invariance of P transports the cohomology identification. At d+1 let b=a+d+1 and use the standard triangle tau_<b K -> K -> tau_>=b K. The first vertex is supported in [a,a+d], and its surviving cohomology is identified with K's; the last vertex is concentrated in degree b and is isomorphic to H^b(K)[-b]. Induction puts the first vertex in E_d(P), the last in E_0(P), and the triangle gives E_(d+1)(P). For a merely bounded K choose bounds a,b, put d=max(0,b-a), enlarge the upper bound if necessary, and apply the quantitative assertion. This is the argument I read in the source theorem, which checks support, uses the long exact cohomology identifications, and transports P through isomorphisms; it is not a new proof step placed in the unsplit node. It accounts for the old proof's finite truncation construction and its endpoint identifications.

Step 1 uses exactly the additive-exact-functor definition in def-weil-triangulated-category and the zero/shift/extension closure in def-weil-triangulated-subcategory. I opened both statements. An additive functor preserves zero: the identity of G(0) is G(id_0)=G(0)=0. Functoriality transports isomorphisms; the specified shift comparisons and image distinguished triangles give the three closure properties of Q_G. Strict fullness of S is an explicit hypothesis of the item, so no isomorphism invariance of the original classes is added. P_G contains zero for the same reason.

Step 2 uses the quantitative/bounded generation assertion of the new node, together with those two definition statements. It fixes an actual F in A_0 and the exact partial functor B(F[0],-). The property P_G is isomorphism invariant even when B_0 is not. The hMB hypothesis is used only for nonzero cohomology; zero cohomology is handled by step 1, so all the hypotheses of the new generation statement hold. The proof explicitly supplies the shifted-single base and the E_j -> E_(j+1) extension step; it does not silently cite an extension-closure theorem or use the proof of another DAG node. The shifted-single comparison follows directly from the derived shift convention and exactness in this variable. It concludes the assertion for (F[0],M) for every F in A_0.

Step 3 uses the same three cited statements with the exact partial functor B(-,M). The hKA hypothesis supplies only nonzero H^q(K) in A_0; step 2 then proves the required degree-zero image membership. Zeros again use step 1. The base and successor arguments are written again, with bounded K supplying the finite length. Thus this is the second genuine induction, and it gives the required value B(K,M), without any interchange of the two variables or assumed joint exactness.

For C4 I checked every cited statement and copied the exact relevant text to citations.json. For C1 there is now a node for finite Postnikov generation; all remaining operations are explicit consequences of the cited definitions or the recursive E_d definition in that node. Both non-elementary steps are below 2000 characters (763 and 770), and the whole assembly is below the requested 3000-character bound. I reviewed B-E point by point: self-contained notation with definition links; genuine strictly smaller structural lemma; no cycle; no extra smallness, Grothendieck, bounded-amplitude, isomorphism-closure or zero-membership hypothesis on A_0/B_0; correctly oriented shifts [-n] and extension triangles. New-node proof and proof_deps are empty.

I tested d=0, a negative a, two separated nonzero degrees with gaps, K=0, M=0, both acyclic, and either original class empty. When a class is empty its admissible bounded inputs are acyclic; the associated exact partial functor takes them to zero. When a middle cohomology object is zero it enters P_G, even if the original class omits zero. The new node by itself does not claim acyclic K is in E_d(P) when P omits zero: in that case its cohomology-membership hypothesis fails. This avoids the empty-generator counterexample. There is no disputed statement or changed target.

Mathlib searches were executed with the required msearch.py command and retained in searches.jsonl, using both generation and canonical-tower phrasings. I read the returned support and representative lemmas, especially Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean:180-195. Existence of a bounded representative is not a finite extension witness. The Loogle hits extensionProduct_le_of_isTriangulatedClosed₂ (Subcategory.lean:310) and extensionProductIter_le_of_isTriangulatedClosed₂ (line 431) prove closure once factors are known; they do not express bounded K as an iterated extension or provide the bound d. I opened these bodies. That closure argument is written in each assembly step and has not become an unnecessary new node. The semantic, pattern and grep records are exactly the logged queries. No search or service failure is presented as an absence result.

## Not duplicates

lem-sfb-bounded-postnikov-extension-generation vs lem-sfb-degreewise-bounded-devissage: The existing node propagates an arbitrary extension-closed property Q; it supplies no finite extension witness or quantitative bound on the recursive E_d class. The new node constructs that witness and bound, rather than introducing another property-propagation lemma.

lem-sfb-bounded-postnikov-extension-generation vs prop-weil-pbc-integral-tstructure: The existing statement is about The standard t-structure on the integral category; it does not assert quantitative membership in the recursively defined E_d(P) for an arbitrary abelian category and arbitrary isomorphism-invariant P, which is the new statement.

lem-sfb-bounded-postnikov-extension-generation vs prop-weil-pbc-levelwise-truncations: The existing statement is about Levelwise truncations of the adic tower; it does not assert quantitative membership in the recursively defined E_d(P) for an arbitrary abelian category and arbitrary isomorphism-invariant P, which is the new statement.

lem-sfb-bounded-postnikov-extension-generation vs thm-weil-pbc-integral-truncations: The existing statement is about Truncations of the integral category; it does not assert quantitative membership in the recursively defined E_d(P) for an arbitrary abelian category and arbitrary isomorphism-invariant P, which is the new statement.

lem-sfb-bounded-postnikov-extension-generation vs lem-weil-envelope-tstructure: The existing statement is about The envelope inherits the t-structure; it does not assert quantitative membership in the recursively defined E_d(P) for an arbitrary abelian category and arbitrary isomorphism-invariant P, which is the new statement.

lem-sfb-bounded-postnikov-extension-generation vs def-weil-t-structure: The existing statement is about t-structure; it does not assert quantitative membership in the recursively defined E_d(P) for an arbitrary abelian category and arbitrary isomorphism-invariant P, which is the new statement.

lem-sfb-bounded-postnikov-extension-generation vs prop-weil-localized-tstructure: The existing statement is about The rational t-structure; it does not assert quantitative membership in the recursively defined E_d(P) for an arbitrary abelian category and arbitrary isomorphism-invariant P, which is the new statement.

lem-sfb-bounded-postnikov-extension-generation vs def-sbc-standard-tstructure-derived-category: The existing statement is about The standard t-structure on the derived category of an abelian category; it does not assert quantitative membership in the recursively defined E_d(P) for an arbitrary abelian category and arbitrary isomorphism-invariant P, which is the new statement.

lem-sfb-bounded-postnikov-extension-generation vs lem-pc-derived-lower-truncation-step-ses: The existing statement is about Successive lower truncations have a two-term kernel quasi-isomorphic to one cohomology object; it does not assert quantitative membership in the recursively defined E_d(P) for an arbitrary abelian category and arbitrary isomorphism-invariant P, which is the new statement.

lem-sfb-bounded-postnikov-extension-generation vs lem-pc-lower-truncation-transition-kernel: The existing statement is about Kernel geometry and homology of a fixed successive lower truncation transition; it does not assert quantitative membership in the recursively defined E_d(P) for an arbitrary abelian category and arbitrary isomorphism-invariant P, which is the new statement.

lem-sfb-bounded-postnikov-extension-generation vs lem-pc-natural-bounded-below-truncation-couples: The existing statement is about Individual bounded-below truncation couples with natural comparisons; it does not assert quantitative membership in the recursively defined E_d(P) for an arbitrary abelian category and arbitrary isomorphism-invariant P, which is the new statement.

lem-sfb-bounded-postnikov-extension-generation vs lem-pc-raw-truncation-couple-naturality: The existing statement is about Naturality of raw truncation maps for one derived morphism; it does not assert quantitative membership in the recursively defined E_d(P) for an arbitrary abelian category and arbitrary isomorphism-invariant P, which is the new statement.

lem-sfb-bounded-postnikov-extension-generation vs lem-sfb-bounded-bifunctor-devissage: The item asserts membership of a bifunctor value in S; the new node has no functor or S and constructs a quantitative finite extension witness from a single bounded object.

lem-sfb-bounded-postnikov-extension-generation vs lem-sfb-bounded-finite-model-generation: The existing node uses constructible local models and stratum extensions on a Noetherian scheme; the new node is abstract abelian-category cohomology generation, independent of schemes, sites and stratifications.

lem-sfb-bounded-postnikov-extension-generation vs lem-weil-pbc-truncation-step-ses: The existing statement is about The step tau_{<=q-1}K -> tau_{<=q}K of canonical truncations: short exact sequence and quasi-isomorphism of the cokernel to H^q(K)[-q]; it does not assert quantitative membership in the recursively defined E_d(P) for an arbitrary abelian category and arbitrary isomorphism-invariant P, which is the new statement.

lem-sfb-bounded-postnikov-extension-generation vs lem-weil-pbc-truncation-descends: The existing statement descends the individual truncation functors and natural maps through localization; it does not give finite iterated-extension generation or its quantitative length.

lem-sfb-bounded-postnikov-extension-generation vs lem-weil-pbc-heart-test-bounded-below: The existing statement is about A heart test for bounded-below left t-exact transformations; it does not assert quantitative membership in the recursively defined E_d(P) for an arbitrary abelian category and arbitrary isomorphism-invariant P, which is the new statement.

lem-sfb-bounded-postnikov-extension-generation vs lem-weil-pbc-upper-step-quotient-coordinates: The existing statement is about Degreewise coordinates of the cokernel of successive upper truncations; it does not assert quantitative membership in the recursively defined E_d(P) for an arbitrary abelian category and arbitrary isomorphism-invariant P, which is the new statement.

lem-sfb-bounded-postnikov-extension-generation vs lem-weil-pbc-two-term-coimage-quasiiso: The existing statement is about The cohomology projection of an arbitrary two-term coimage complex is a quasi-isomorphism; it does not assert quantitative membership in the recursively defined E_d(P) for an arbitrary abelian category and arbitrary isomorphism-invariant P, which is the new statement.

lem-sfb-bounded-postnikov-extension-generation vs lem-weil-pbc-finite-postnikov-isomorphism: The existing node propagates invertibility of a natural transformation of two functors; it gives neither an extension witness for K nor a recursive generation bound.

lem-sfb-bounded-postnikov-extension-generation vs lem-weil-pbc-truncation-triangle: The existing statement supplies one successive truncation triangle; the new statement proves finite generation with a length d from cohomological support, with no specified cut as input.

lem-sfb-bounded-postnikov-extension-generation vs lem-kun-canonical-truncation-filtration: The existing node constructs a filtered termwise bounded R-module complex, including homotopy assertions; the new node concerns arbitrary abelian categories and cohomologically bounded derived objects and asserts membership in a quantitative recursive extension class.

lem-sfb-bounded-postnikov-extension-generation vs lem-sf-derived-concentrated-single: The existing node gives only the d=0 single-degree case, while the new node handles every finite interval and constructs the recursive extension membership.

lem-sfb-bounded-postnikov-extension-generation vs lem-pur-bounded-heart-amplitude: The existing statement is about Finite cohomological amplitude from bounds on cohomology objects; it does not assert quantitative membership in the recursively defined E_d(P) for an arbitrary abelian category and arbitrary isomorphism-invariant P, which is the new statement.

lem-sfb-bounded-postnikov-extension-generation vs lem-sf-etale-origin-pushforward-amplitude: The existing statement is about Etale heart bounds control cohomological ranges on pro-etale complexes of etale origin; it does not assert quantitative membership in the recursively defined E_d(P) for an arbitrary abelian category and arbitrary isomorphism-invariant P, which is the new statement.

lem-sfb-bounded-postnikov-extension-generation vs lem-sf-derived-truncation-triangle: The existing statement is about Canonical truncation triangle in the derived category; it does not assert quantitative membership in the recursively defined E_d(P) for an arbitrary abelian category and arbitrary isomorphism-invariant P, which is the new statement.


## Preserved starting proof

The following is the complete live proof read before this repair; its finite-generation fact is now a node, and both image inductions and zero cases remain in the assembly.


1. For an exact functor G:D(C)→T, let P(X) mean S(G(X[0])) and let Q(L) mean S(G(L)). Both are closed under isomorphisms, and Q is triangulated and stable under all integer shifts, by the exactness of G and the strict fullness and triangulated closure of S. This choice of P needs no closure assumption on the original classes A₀ and B₀.


2. Use the already proved DerivedCategory.exists_iteratedExtensions_of_bounded in WeilConjectures.CategoryTheory.DerivedCategory.BoundedEssentiallySmall. For a bounded L whose cohomology objects satisfy P, it expresses L as a finite iterated extension of objects isomorphic to X concentrated in degree n, with P(X). This theorem implements finite standard-t-structure truncation induction, splitting off the top cohomology. The canonical singleFunctors.shiftIso identifies X in degree n with X[0][-n], so shift and isomorphism closure give Q on each such object. The proved DerivedCategory.iteratedExtensions_le then gives Q(L). This is the private one-variable helper bounded_functor_devissage; all library results used here are proved, with no new open lemma.


3. Apply the one-variable helper to G=B(-,M) and K. For each q, if H^q(K) is zero then its degree-zero image is zero, since both the single functor and G preserve zero objects. It belongs to S, which contains every zero object. Otherwise hKA places H^q(K) in A₀.


4. In the nonzero case of step 3 apply the helper to G=B(H^q(K)[0],-) and M. For each r, a zero H^r(M) again gives a zero image in S. A nonzero H^r(M) belongs to B₀ by hMB, and h₀ gives S(B(H^q(K)[0],H^r(M)[0])). Thus the inner helper gives S(B(H^q(K)[0],M)), and the outer helper gives S(B(K,M)). These two finite inductions cover arbitrary integer intervals, zero objects, gaps and empty classes without assuming zero belongs to A₀ or B₀.


## Unfinished work

No required stage-1 work remains after successful dry run and push. The new node deliberately has no proof steps; its source implementations and complete argument above are available to the next stage-1 reader. No Lean was written, no compiler or Lake command was run, and all worker writes were inside this sandbox.
