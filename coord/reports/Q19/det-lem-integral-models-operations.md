# Worker report: det-lem-integral-models-operations

1. Files written: the item JSON and four new statement-only JSON nodes under `dag/nodes/sec-six-functors-basics/`, plus this report and citations.json.
   - det-lem-integral-models-operations: statement unchanged, seven-step assembly replacing the returned 12149-character proof.
   - lem-sfb-scalar-model-immersion-extension: statement, unsplit; no Mathlib match for preservation of finite scalar models for arbitrary Noetherian schemes.
   - lem-sfb-flat-scalar-cyclic-resolution: statement, unsplit; ordinary-module regularity is in Mathlib, but the sheaf-algebra augmented K-flat resolution is not a one-line specialization.
   - lem-sfb-flat-dvr-scalar-tensor: statement, unsplit; no Mathlib match for finite scalar cohomology models over a flat sheaf algebra on an arbitrary site.
   - lem-sfb-bounded-bifunctor-devissage: statement, unsplit; no Mathlib match for the two-variable finite truncation induction with arbitrary prescribed heart classes.
2. Attachments: none. The required tag and concept searches in lean/WeilConjectures do not find the item. Its existing Sheaf.Paper.IntegralModelsOperations declaration is already recorded and is not a finished upstream proof to attach.
3. WANTED: none. All source material used is available in literature/.
4. The earlier report incorrectly treated the assignment as stale because the item was reviewed. The human's explicit 2026-10-21 re-split instruction supersedes that refusal. The retained draft had already shortened the parent but incorrectly split its new children. Their proofs are now retained below as report material only: each new node has status unsplit, proof [], proof_deps [], and proof_origin null. A proposed new scalar-model-pullback node duplicates lem-sfb-pullback-constant-model-constructible and was removed from the delivery; its draft is retained under retained-draft/ for recovery. The parent cites the existing node instead. The reviewed parent statement, metadata, Lean statement, import flags and blueprint fields are retained unchanged.
5. Nothing remains unfinished in the stage-1 repair. The new nodes intentionally await their own stage-1 workers. No Lean was written, no compiler was run, and neither the shared repository nor launcher scripts were changed.

## Review by Q19

I read the current main-20261015 item statement and proof, its unit sk-lem-integral-models and six-functors chapter, and compared the returned eleven-step proof with the retained sandbox draft. The parent has the same four clauses, with every scheme merely Noetherian, untwisted coefficients, ordinary uncompleted derived tensor, and arbitrary unbounded L and M in clause (4). I used the previously reviewed scalar-model cohomology route. The blueprint's assertion that a finite free complex is locally a sum of shifts is not used: already [A --pi--> A] over a DVR with pi nonunit has a nonzero differential and is not the sum of its terms in the derived category. Finite truncation induction replaces that argument. No new statement dispute of the item is introduced.

Step 1 fixes finite constant scalar-model constructibility from sk-def-sfb-constructible, whose statement explicitly defines both the models and Dbc as bounded constructible cohomology. sk-def-sfb-bounded-constructible supplies the bounded-cohomology interpretation; I do not substitute arbitrary locally finitely presented matrices for scalar matrices or impose derived completeness.

Step 2 uses lem-sfb-pullback-constant-model-constructible, whose statement gives precisely the pulled-back finite stratification, base-changed cover and identical finitely presented scalar modules. It assumes qcqs schemes: quasi-compactness is part of Noetherianity and lem-weil-pbc-locally-noetherian-quasi-separated supplies quasi-separatedness. The admissible coefficient is O_E, so the finite-primary-ring restriction of that node is irrelevant. sk-prop-sfb-cartesian-coefficients explicitly gives exact coefficient-compatible inverse image. Exactness preserves the kernels and images defining H^q, so the same finite cohomological interval works. This avoids assuming that a new base is an object of the old small site.

Step 3 uses the new sheaf-level immersion lemma, which includes exactness and constructibility of both extension functors. Apply it separately to the open u and the closed i (with their respective complementary loci), then use sk-def-sfb-derived-categories, whose Exact functors clause identifies their derived functors with termwise application. Cohomology and its bounds are therefore preserved. The new lemma is a sheaf-level finite-stratification statement, not the parent's derived composite assertion; its separate geometric content is the source/complement stratification and retention of models.

Step 4 uses lem-weil-pbc-constructible-stratification-intersection for actual fibre products of strata. The existing scalar-model pullback node supplies their restricted models. The site axioms in def-weil-pbc-sites-and-cohomology allow the common trivializing cover by base change and composition. lem-weil-pbc-ringed-topoi-derived-tensor-pullback explicitly identifies the restricted derived tensor with the derived tensor of the two models, on small sites in the coefficient universe. lem-weil-l-adic-extension-integers-dvr gives the DVR hypothesis. Only the flatness clause of det-prop-integral-criterion-constant-coefficients is used; this does not introduce a completion condition on objects. The new cyclic-resolution lemma justifies the actual two-term model for torsion factors, and the new flat-DVR tensor lemma computes its finite scalar cohomology in degrees -1,0. Finally lem-weil-pbc-noetherian-stratum-detection explicitly detects zero cohomology after the stratum-and-cover restrictions. The scalar models themselves establish constructibility by its cited definition. This step assembles the local calculation and detection without hiding another tensor or Tor theorem.

Step 5 uses lem-sfb-integral-constant-model-heart-closure for zero, kernels, cokernels and extensions of exactly the integral scalar-model sheaves, and lem-sbc-cohomology-in-weak-serre-subcategory for their bounded triangulated cohomology subcategory. The zero model is allowed by the definition. lem-weil-pbc-ringed-projection-mate-exact explicitly states exactness in both variables of derived tensor; applying it to the identity ringed topos gives that assertion here. The new bifunctor devissage lemma then applies with both heart classes the constructible sheaves and target the preceding bounded triangulated subcategory. Both inputs are bounded, so there is no convergence or infinite-truncation assumption.

Step 6 reads the actual gamma formula of lem-sf-open-tensor-normalization, which accepts arbitrary commutative ring sheaves and unbounded complexes; specialize its base-change square to the identity and take the coefficient ring on the closure. The closed formula lem-weil-proetale-closed-tensor-projection has equally unrestricted inputs, but requires a quasi-compact complementary open. That requirement follows from lem-sfb-noetherian-space-compact-subsets on each affine open of the Noetherian ambient scheme. The Cartesian coefficient statement identifies all restriction rings. Thus neither a finite coefficient theorem nor a field-base theorem is being applied to O_E.

Step 7 composes those two natural isomorphisms with N=u_!L. lem-weil-pbc-site-morphism-composition explicitly supplies successive inverse image for the composite, identifying u^*i^* with a^*. The computation is a literal composition of functors and natural isomorphisms, so is elementary relative to step 6; it does not infer an isomorphism merely from matching objects on strata.

For the new immersion node I read paragraph (3) of the current item proof and the full statements of lem-weil-pbc-proetale-ringed-open-closed, sk-prop-sfb-cartesian-coefficients and lem-sfb-noetherian-space-compact-subsets. These give exactness and the identity/zero restrictions; the retained argument below explains the finite stratification and zero models. It imposes no finite type, separatedness, dimension or invertibility condition. For the cyclic node I read sites-cohomology.tex, Tag 06YU (definition-derived-tor) and Tag 06YQ (lemma-bounded-flat-K-flat), and the exact-sheafification and flat-sheaf-module statements. Tags 06YU and 06YQ supply the derived tensor convention and bounded-flat K-flatness, respectively; the specific scalar resolution is the explicit agent construction below, not a theorem falsely attributed verbatim to either tag. For the DVR tensor node I read paragraph (2), the DVR statement, the existing lem-sfb-dvr-matrix-smith-powers statement and the cyclic resolution argument. Flatness over the constant scalar sheaf is essential; without it cancellation can fail. For bifunctor devissage I read derived.tex, Tag 08J5 (remark-truncation-distinguished-triangle), including the displayed cohomology-step triangle, and lem-weil-pbc-truncation-triangle. The new node's source is this triangle applied twice, with the two finite inductions recorded below as an agent argument; Tag 08J5 itself does not claim the bifunctor theorem.

I checked small cases for each new statement: empty scheme/site and empty strata; zero modules; identity, empty and full open/closed immersions; a unit a (the cyclic complex is acyclic and R/aR=0); nonzero nonunit a over a domain; r=s=1 giving nonzero H^{-1} and H^0; r<s and r>s giving min(r,s); a free factor and a zero presentation; zero complexes and one-degree complexes with arbitrary shifts for devissage. Flatness supplies every cancellation, and local quotient sections are lifted only after cover refinement. The generic bifunctor lemma allows empty heart classes: then acyclic complexes are zero and exactness gives zero, so its stated zero case remains valid.

I checked delivery-errors B–E against the actual node files: new nodes introduce their objects and have no proofs, bracketed notions have existing definition interfaces, proof_deps is the union of uses, every citation has its literal statement in citations.json, and all substantial residual arguments are either named new nodes or existing nodes. No proof step exceeds 2000 characters; the complete assembly is below 2600 characters. The four source tags/places and blueprint.from places are explicit. The child statements are more general and smaller than the parent's four-clause theorem. Every proposed new id was checked against whole-DAG and blueprint searches; the pullback duplicate was removed. Existing open and closed projection formulas are reused rather than recreated. All off-unit statements are declared as generic tool uses in split_report, with the exact application explained above. The old report, proofs, citations and search logs remain in the sandbox for recovery.

## Mathlib search review

I read searches.jsonl and the saved result files before reusing them. Each child retains the literal earlier leanfinder, leansearch, loogle and grep queries. There are two different natural-language phrasings for each mathematical question. LeanSearch's rate-limit response for the earlier bifunctor query remains unavailable. The malformed CategoryTheory.Triangulated Loogle query is recorded as rejected/unavailable; a valid query for IsTriangulated and ObjectProperty and a fresh LeanSearch phrasing supply useful results. Those return exactness, triangle closure and derived functor infrastructure, not the two finite induction result. The natural-language scalar-resolution hits include Module.Flat.isSMulRegular_of_nonZeroDivisors and ModuleCat.smulShortComplex. The additional logged grep locates them in RingTheory/Flat/TorsionFree.lean:79 and RingTheory/Regular/Category.lean:35,42,50; I read these sources, which concern modules over one ordinary ring and do not give the arbitrary ringed-site K-flat assertion. The tensor hits include ordinary tensor/quotient and torsion facts, not derived sheaf cohomology after flat scalar extension. The immersion hits are topological constructible images and generic exact functors, not finite scalar-model module sheaves. Consequently no new node is declared a Mathlib leaf. Existing Mathlib leaves, including locally Noetherian quasi-separatedness, are reused.

## Retained arguments for future stage-1 workers

These are recovery material, not proofs in the new statement-only nodes. Each is well below 3000 characters. Their previous detailed node citations are retained in retained-draft/ and child-citations.json; the parent uses only their statements.

### lem-sfb-scalar-model-immersion-extension

Every subset of a Noetherian space is quasi-compact by [lem-sfb-noetherian-space-compact-subsets]. Apply this to the intersections of $U$ with affine opens of $T$; thus $j$ is quasi-compact. With inverse-image coefficient rings, [lem-weil-pbc-proetale-ringed-open-closed] gives exactness of $j_!$ and $i_*$, identity on their own loci, and zero restriction to the complementary loci. These coefficient rings are $R_U,R_Z$ by [sk-prop-sfb-cartesian-coefficients].

An adapted finite stratification on $U$ or $Z$ consists of locally closed subschemes of $T$ as well: composing an open or closed immersion with a locally closed immersion is locally closed. Append the complementary closed or open locus. The resulting finite partition has constructible strata because $T$ is Noetherian. Restricting the extension to an original stratum gives precisely the original sheaf, and restricting to the added locus gives zero, by the identities just cited. Consequently the old finite scalar models and the finitely presented scalar module $0$ supply all models required by [sk-def-sfb-constructible].


### lem-sfb-flat-scalar-cyclic-resolution

The injective constant presheaf map $A\xrightarrow{a}A$ remains injective after exact sheafification [lem-weil-pbc-sheafification-exact], and becomes multiplication on $A_{\mathcal C}$ by [def-weil-pbc-constant-sheaf]. Flatness [def-pc-flat-sheaf-modules] makes $-\otimes_{A_{\mathcal C}}R$ exact. Applying it to $0\to A_{\mathcal C}\xrightarrow{a}A_{\mathcal C}$ gives $0\to R\xrightarrow{a}R$. Its cokernel is the quotient $R/aR$, so the displayed augmentation is a quasi-isomorphism.

The unit $R$ is flat over itself, since its tensor functor is the identity. Both the two-term complex and $R[0]$ are bounded above complexes of flat $R$-modules, hence K-flat by [lem-pc-bounded-above-flat-kflat-site]. The K-flat computation of derived tensor [lem-weil-pbc-ringed-projection-mate-exact] now gives the asserted resolution formula.


### lem-sfb-flat-dvr-scalar-tensor

Apply [lem-sfb-dvr-matrix-smith-powers] to a finite presentation matrix of $P$ and of $Q$. Taking cokernels of the diagonal presentations decomposes each scalar module into finitely many copies of $A$ and $A/\pi^r$, $r\ge1$; exponent-zero pivots contribute zero, and unmatched target basis vectors contribute free copies. Extension of scalars, as a tensor left adjoint, preserves these cokernels and finite sums, giving the analogous decompositions over $R$. Derived tensor is additive in each variable by [lem-weil-pbc-ringed-projection-mate-exact], so it suffices to treat pairs of these summands.

The resolutions from [lem-sfb-flat-scalar-cyclic-resolution] give $[R/\pi^sR\xrightarrow{\pi^r}R/\pi^sR]$ in degrees $-1,0$ for a torsion pair. If $r\ge s$, the differential is zero. If $r<s$, its cokernel is $R/\pi^rR$. Its kernel is also $R/\pi^rR$, by the map induced by $y\mapsto\pi^{s-r}y$: locally lift a quotient section to $x\in R$. The kernel equation lifts, after a refinement, to $\pi^r x=\pi^s y$; cancellation of the injective multiplication by $\pi^r$ yields $x=\pi^{s-r}y$. The kernel of $R\to R/\pi^sR$, $y\mapsto\pi^{s-r}y$, consists exactly of $\pi^rR$: locally $\pi^{s-r}y=\pi^s z$ and cancellation gives $y=\pi^r z$. Conversely each such multiple maps to zero. All lifting is local, as required for sheaf quotients. A free factor is handled by $R[0]$. Finally $R/\pi^tR=R\otimes_{A_{\mathcal C}}\underline{A/\pi^tA}$ by the cokernel presentation, and finite sums provide the claimed finitely presented scalar $N$. No splitting of arbitrary complexes into cohomology shifts is used.


### lem-sfb-bounded-bifunctor-devissage

Fix $G\in\mathcal B_0$. Induct on the length of an interval $[a,b]$ containing the cohomology of $K$. The empty interval means $K=0$, and exactness of $B(-,G[0])$ gives zero. For a nonempty interval the cohomology-step truncation triangle [lem-weil-pbc-truncation-triangle], with $\tau_{\le b}K\simeq K$, has terms $\tau_{\le b-1}K,K,H^b(K)[-b]$. The first object's interval is shorter; the third is a shift of a degree-zero object, or zero. After applying the exact functor $B(-,G[0])$, induction and the assumed degree-zero case place the outer terms in $\mathcal S$; triangle and shift closure [def-weil-triangulated-subcategory] place the middle term there.

Now fix such a $K$ and induct on an interval $[c,d]$ for $M$. The empty case is zero. Use the same cohomology-step triangle [lem-weil-pbc-truncation-triangle], with $\tau_{\le d}M\simeq M$, and apply $B(K,-)$ to $\tau_{\le d-1}M\to M\to H^d(M)[-d]\to$. The first term lies in $\mathcal S$ by this induction. The third lies there by the first induction and shift closure, or is zero. Closure under distinguished triangles proves the middle case. This uses two finite inductions only; neither spectral-sequence convergence nor an infinite-generation assertion is required.


## Not duplicates

lem-sfb-flat-scalar-cyclic-resolution vs lem-sfb-constant-field-tor-bounds: the newly arrived existing node equates cohomological amplitude with Tor amplitude for arbitrary complexes over a constant field sheaf on a scheme. The new node constructs a specific augmented quotient K-flat resolution over an arbitrary flat sheaf algebra over a constant integral domain, including nonunits over nonfields. The field Tor-amplitude statement supplies neither scalar injectivity over such algebras nor this quotient resolution.

lem-sfb-bounded-bifunctor-devissage vs lem-weil-pbc-finite-postnikov-isomorphism: the newly arrived existing node propagates invertibility of a shift-compatible natural transformation between two exact functors on a bounded-below category to one finite upper truncation. The new node instead propagates membership in an arbitrary triangulated subcategory for a bifunctor and two arbitrary classes of heart objects; it has no natural transformation or isomorphism-locus hypothesis. Neither statement specializes to the other.

lem-sfb-bounded-bifunctor-devissage vs def-sbc-standard-tstructure-derived-category: the new node asserts two-variable finite cohomology generation into any strictly full triangulated subcategory, whereas the existing node gives the standard t-structure on one derived category.

lem-sfb-bounded-bifunctor-devissage vs def-weil-t-structure: the new node asserts two-variable finite cohomology generation into any strictly full triangulated subcategory, whereas the existing node gives the axioms and truncations of a t-structure.

lem-sfb-bounded-bifunctor-devissage vs lem-pc-derived-lower-truncation-step-ses: the new node asserts two-variable finite cohomology generation into any strictly full triangulated subcategory, whereas the existing node gives a lower-truncation short exact sequence and its two-term kernel.

lem-sfb-bounded-bifunctor-devissage vs lem-pc-lower-truncation-transition-kernel: the new node asserts two-variable finite cohomology generation into any strictly full triangulated subcategory, whereas the existing node gives coordinates and uniqueness of one lower-truncation kernel.

lem-sfb-bounded-bifunctor-devissage vs lem-pc-natural-bounded-below-truncation-couples: the new node asserts two-variable finite cohomology generation into any strictly full triangulated subcategory, whereas the existing node gives existence of natural maps of chosen exact couples for one right derived functor.

lem-sfb-bounded-bifunctor-devissage vs lem-pc-raw-truncation-couple-naturality: the new node asserts two-variable finite cohomology generation into any strictly full triangulated subcategory, whereas the existing node gives maps of raw truncation couples and abutment squares.

lem-sfb-bounded-bifunctor-devissage vs lem-weil-envelope-tstructure: the new node asserts two-variable finite cohomology generation into any strictly full triangulated subcategory, whereas the existing node gives extension of a t-structure to an idempotent completion.

lem-sfb-bounded-bifunctor-devissage vs lem-weil-pbc-truncation-descends: the new node asserts two-variable finite cohomology generation into any strictly full triangulated subcategory, whereas the existing node gives descent of good truncations and their maps to the derived category.

lem-sfb-bounded-bifunctor-devissage vs lem-weil-pbc-truncation-step-ses: the new node asserts two-variable finite cohomology generation into any strictly full triangulated subcategory, whereas the existing node gives the upper-truncation step short exact sequence and quotient quasi-isomorphism.

lem-sfb-bounded-bifunctor-devissage vs lem-weil-pbc-truncation-triangle: the new node asserts two-variable finite cohomology generation into any strictly full triangulated subcategory, whereas the existing node gives a functorial single cohomology-step triangle.

lem-sfb-bounded-bifunctor-devissage vs lem-weil-pbc-two-term-coimage-quasiiso: the new node asserts two-variable finite cohomology generation into any strictly full triangulated subcategory, whereas the existing node gives quasi-isomorphism of a specified coimage two-term complex.

lem-sfb-bounded-bifunctor-devissage vs lem-weil-pbc-upper-step-quotient-coordinates: the new node asserts two-variable finite cohomology generation into any strictly full triangulated subcategory, whereas the existing node gives coordinates of an upper-step quotient complex.

lem-sfb-flat-scalar-cyclic-resolution vs def-pc-derived-tensor-cohomology-vanishes: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives the meaning of tensor cohomology vanishing with a sheaf second factor.

lem-sfb-flat-scalar-cyclic-resolution vs def-pc-derived-tensor-complex-cohomology-vanishes: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives the meaning of tensor cohomology vanishing with a complex second factor.

lem-sfb-flat-scalar-cyclic-resolution vs def-pd-section-derived-realization: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives normalizations of transported section-module derived operations.

lem-sfb-flat-scalar-cyclic-resolution vs def-pd-section-derived-tensor-data: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives definitions of transported section tensor and total-complex comparisons.

lem-sfb-flat-scalar-cyclic-resolution vs def-sc-derived-tensor-augmentation: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives data for an augmentation represented by a K-flat tensor.

lem-sfb-flat-scalar-cyclic-resolution vs def-sfb-ringed-projection-coherence-data: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives the data and normalizations for ringed projection coherence.

lem-sfb-flat-scalar-cyclic-resolution vs def-trf-split-flat-filtered-sheaf-models: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives the definition of filtered split-flat models.

lem-sfb-flat-scalar-cyclic-resolution vs def-weil-pbc-completed-constant-realization-data: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives realization and reduction-comparison records for adic completions.

lem-sfb-flat-scalar-cyclic-resolution vs lem-pc-bounded-above-flat-tensor-acyclic-degree: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives degreewise acyclicity when tensoring an already bounded-above flat complex.

lem-sfb-flat-scalar-cyclic-resolution vs lem-pur-constant-two-term-resolution: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives the constant Z_l resolution of a fixed positive-power finite quotient, not arbitrary domains and flat scalar sheaf algebras.

lem-sfb-flat-scalar-cyclic-resolution vs lem-pur-etale-single-functor-monoidal-compatibility: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives coherence of degree-zero pairings of flat etale sheaves.

lem-sfb-flat-scalar-cyclic-resolution vs lem-sc-source-kflat-tensor-left-triangulated: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives exactness of tensor by a given K-flat complex.

lem-sfb-flat-scalar-cyclic-resolution vs lem-sf-integral-line-tensor-comparison-representative: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives K-flatness and finite-reduction comparison for an invertible integral line.

lem-sfb-flat-scalar-cyclic-resolution vs lem-sfb-ringed-site-point-kflat-resolution: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives existence of a resolution K-flat both globally and at a point.

lem-sfb-flat-scalar-cyclic-resolution vs lem-trf-finite-filtered-flat-resolution: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives existence of strict split-flat filtered resolutions.

lem-sfb-flat-scalar-cyclic-resolution vs lem-weil-pbc-completed-adic-koszul-kflat: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives K-flatness of an actual completed Koszul complex without an augmentation claim.

lem-sfb-flat-scalar-cyclic-resolution vs lem-weil-pbc-completed-constant-derived-tensor-tower: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives derivability of a whole quotient tensor diagram.

lem-sfb-flat-scalar-cyclic-resolution vs lem-weil-pbc-completed-constant-resolution-tensor-calculation: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives comparison of realized finite-free resolutions with quotient diagrams.

lem-sfb-flat-scalar-cyclic-resolution vs lem-weil-pbc-independent-bounded-flat-kflat: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives K-flatness of an already bounded-above flat complex.

lem-sfb-flat-scalar-cyclic-resolution vs lem-weil-pbc-ringed-projection-mate-exact: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives exactness and shift normalization of the projection mate.

lem-sfb-flat-scalar-cyclic-resolution vs lem-weil-pbc-site-derived-tensor-descent: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives descent of K-flat tensor through localization.

lem-sfb-flat-scalar-cyclic-resolution vs lem-weil-pbc-site-tensor-local-model-comparison: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives comparison of one tensor cohomology group with already supplied scalar complex models.

lem-sfb-flat-scalar-cyclic-resolution vs lem-weil-pbc-split-perfect-tensor-kinjective: the new node asserts injectivity of every nonzero scalar and the specific augmented quotient K-flat resolution for any flat sheaf algebra over a constant domain; the existing node gives K-injectivity after tensoring with a bounded split-perfect complex.

lem-sfb-flat-dvr-scalar-tensor vs lem-sfb-finite-constant-model-two-term-free-resolution: the existing node constructs finite free resolutions over pulled-back O_E or E on a scheme; the new node computes all tensor cohomology and finite scalar models for two modules over any flat sheaf algebra over any DVR. The existing resolution alone does not compute these kernels or identify their scalar models.

lem-sfb-flat-dvr-scalar-tensor vs lem-sfb-dc-tensor-single: the existing node assumes separated finite type over a positive-characteristic field and asserts bounded constructibility in the general ring-object sense. The new node is an arbitrary-site flat-DVR scalar tensor computation, including explicit degrees and min(r,s) cohomology, with no field-base assumption.

lem-sfb-bounded-bifunctor-devissage vs lem-sfb-dc-module-devissage: the existing node is one-variable generation from constructible sheaves on one pro-etale scheme ring; the new statement works for two arbitrary abelian categories, two arbitrary heart classes and an arbitrary triangulated target subcategory. It is not a specialization of that geometric one-variable statement.

lem-sfb-bounded-bifunctor-devissage vs lem-sfb-bounded-heart-amplitude-devissage: the existing conclusion is an upper cohomological degree bound for a single derived functor with a uniform heart bound; the new conclusion is membership in an arbitrary triangulated target subcategory for a bifunctor, without an amplitude structure on the target.

lem-sfb-scalar-model-immersion-extension vs lem-sfb-dc-open-lower-shriek-preserves: the existing node assumes the separated finite-type field setting and handles general ring-object bounded constructibility for an open immersion only. The new statement concerns sheaves with finite scalar models on arbitrary Noetherian schemes and includes closed direct image with its adapted complement stratification.

lem-sfb-scalar-model-immersion-extension vs lem-weil-pbc-proetale-ringed-open-closed: the existing node gives exactness and identity/zero restrictions, with no constructibility or finite scalar model conclusion. The new node's additional conclusion assembles these restrictions into finite adapted stratifications.

## Validation

The first required dry run was run before changing retained work and failed at the missing same-tag duplicate explanations. The report now addresses those pairs explicitly. The revised dry run exited successfully with OK (not pushed) at 9f4032ccd79. A final dry run after removing a repeated citation entry precedes the push; results are recorded by the delivery command.

The first push was refused before writing because Q03 added lem-weil-pbc-finite-postnikov-isomorphism after the successful dry run. I read its whole statement and added the comparison above; it does not supply the bifunctor lemma. The following dry run validates against that updated main tree.
