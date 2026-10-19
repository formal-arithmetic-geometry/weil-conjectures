## Files written

- dag/nodes/sec-trace-formula/lem-trf-derived-basis-local-ext-sheaf.json: statement, split into five steps, unchanged statement and statement dependencies; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-unbounded-direct-image-section-presheaf.json: statement-only helper, unsplit; no Mathlib match.
- citations.json: one verbatim statement excerpt per node cited by each item step.

## Attachments

None. Searched WeilConjectures/ in the read-only slopmaster2 source by the item id, negative Ext/Hom and ringed-space derived-Hom/direct-image notions. No project declaration states the whole item. Upstream master was treated only as reference material. No compiler or Lake was invoked.

## WANTED

None. All sources needed here are present in literature/stacks-project/.

## Problems corrected

The imported statement agrees with Stacks Tag 0D66(2), including arbitrary ringed spaces, unbounded objects and every integer i<0. No statement dispute or change was needed. The import had no proof. The split now spells out the part-(1) argument instead of treating 0D66(1), which would nearly restate the item, as a new lemma. The basis need not be intersection-closed. In particular, inverse images of basis opens need not form a basis on X, so the sheafification argument is made on Y, not incorrectly on X.

The new helper exposes the actual 0D5X comparison for arbitrary ringed spaces and arbitrary unbounded E. Existing nodes at that tag are specialized to schemes, quasi-coherent inputs or pro-etale sites and do not suffice on these hypotheses. During self-review I corrected a mistaken ancillary Leray tag to 0D5W from the local tag table and added lem-pur-kinjective-restrict-localized to Step 1 so the naturality argument explicitly has a valid restricted K-injective model.

I read the chapter and sk-i-curve-zero unit, the current main-20261015 locality proof and the item's ancestry through BBD descent. This is a generic descent tool already used by the parent, not a replacement of the contracting-correspondence unit proof. No unit or chapter record is written.

## Unfinished work

Only the new helper's proof is deliberately left for its own stage-1 item. The item's proof is complete with that cited statement as a black box. The helper has no proof sketch embedded in its statement, no proof steps and no proof dependencies.

## Mathlib searches

Every new recorded query was executed with msearch.py and its result digest is preserved verbatim in searches.jsonl and the node search records. The item received two semantic phrasings, Loogle and source grep. The helper received two semantic phrasings, LeanSearch, Loogle and two scoped source greps. The item's LeanSearch request was rate-limited and is recorded unavailable, not as evidence of absence. I retained the inherited search records on the item.

I read the returned cohomologyPresheaf and cohomologyPresheafFunctor definitions in Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean, lines 56-86, and the underived SheafOfModules.pushforward in Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean, lines 39-49. They define nonnegative cohomology for individual abelian sheaves and underived pushforward; none identifies all-degree unbounded module-derived direct-image cohomology with sheafification. The item hits on t-structure orthogonality assume cohomological bounds on the two objects and do not give this local-Ext criterion. Ordinary sheaf gluing assumes the presheaf already is a sheaf, which is what must be proved here. No Mathlib leaves were created.

I searched the whole DAG by the Stacks tags 0D66, 08DK, 08JA, 0D5X, 0D6I and keywords. I ran blueprint_refs.py ancestor and whole-blueprint searches for negative Ext, derived Hom, negative cohomology, higher direct images, 08DK, 0D5X, 0D6I, unbounded describe, Hom presheaf, local Ext and sheaf associated to the presheaf. No blueprint node states the item or the helper. Relevant generic facts were reused rather than duplicated.

## Not duplicates

lem-trf-unbounded-direct-image-section-presheaf vs new-qcoh-acyclic-sheafification-component: that node assumes a qcqs scheme morphism, quasi-coherent E and vanishing of higher direct images of quasi-coherent modules; the new node has arbitrary ringed spaces and arbitrary E and also gives the local Leray comparison.
lem-trf-unbounded-direct-image-section-presheaf vs lem-sc-qcoh-acyclic-derived-sections-comparison: that node assumes qcqs schemes and quasi-coherent acyclicity and includes an affine section calculation; the new node makes no such assumptions.
lem-trf-unbounded-direct-image-section-presheaf vs def-pc-derived-section-presheaf: that node defines a scheme presheaf but does not assert the sheafification theorem or local Leray identification for arbitrary ringed spaces.
lem-trf-unbounded-direct-image-section-presheaf vs lem-pe-bounded-complex-direct-image-presheaf: that node is restricted to bounded-below complexes on pro-etale sites of schemes; the new node concerns arbitrary ringed spaces and unbounded complexes.
lem-trf-unbounded-direct-image-section-presheaf vs det-pe-bounded-continuity-direct-image: that node concerns preservation of filtered colimits for bounded-below pro-etale complexes under a qcqs scheme morphism, not this local hypercohomology description.
lem-trf-unbounded-direct-image-section-presheaf vs lem-pur-retracted-support-localization-comparison: that node concerns a supported localization triangle and an edge-map boundary equation for a closed section of finite-type schemes with finite coefficients, not the general sheafification comparison.
lem-trf-unbounded-direct-image-section-presheaf vs lem-sc-derived-direct-image-square-mate: that node asserts a mate identity for schemes, with no global-section or sheafification conclusion.
lem-trf-unbounded-direct-image-section-presheaf vs lem-sc-mixed-sections-composition-coherence: that node asserts a normalized mixed Leray composition equation for schemes, not this sheafification theorem.
lem-trf-unbounded-direct-image-section-presheaf vs lem-sc-mixed-sections-right-unit-normalization: that node is a scheme right-unit normalization equation, not a local cohomology or sheafification theorem.
lem-trf-unbounded-direct-image-section-presheaf vs lem-sc-mixed-sections-square-comparison-coherence: that node is a scheme pullback-square comparison equation, not this general local description.
lem-trf-unbounded-direct-image-section-presheaf vs lem-sc-mixed-sections-composition-kinjective: that node asserts a normalized composition equation on scheme K-injective models; it supplies no sheafification assertion for ringed spaces.
lem-trf-unbounded-direct-image-section-presheaf vs lem-sc-mixed-sections-left-unit-normalization: that node is a scheme left-unit normalization equation, not this general local description.
lem-trf-unbounded-direct-image-section-presheaf vs lem-weil-pbc-higher-direct-image-presheaf: that node concerns a single module in nonnegative degree on a scheme, rather than an arbitrary unbounded derived object on a ringed space.
lem-trf-unbounded-direct-image-section-presheaf vs lem-weil-pbc-site-higher-direct-image-sheafified-presheaf: that node concerns a single abelian sheaf and nonnegative derived functors, not arbitrary unbounded module complexes.

## Review by Q43

I read cohomology.tex Tag 0D66 (lemma-vanishing-and-glueing), both clauses and its entire proof. The new helper was checked against cohomology.tex Tag 0D5X (lemma-unbounded-describe-higher-direct-images), its proof and the invoked 0D5W (lemma-Leray-unbounded), together with the adjacent restriction and sheafification statements. Naturality and compatibility with restriction are the canonical comparisons of section complexes, not arbitrary group isomorphisms. The helper preserves the source's lack of boundedness and geometric finiteness hypotheses.

For Step 1 I read every cited statement. def-pur-derived-internal-hom constructs precisely the unbounded internal Hom. lem-weil-pbc-ringed-internal-hom-exact-restriction gives the natural restriction isomorphism and successive-restriction compatibility; lem-sf-ringed-derived-closed-symmetric-monoidal supplies the right adjunction required by lem-sfb-derived-internal-hom-sections-model. The latter's clause (2), including its last all-integer shifted-Hom formula, is exactly the comparison used here. lem-sfb-unbounded-sections-localization identifies evaluation at U with derived sections on U. lem-pur-kinjective-restrict-localized ensures a restricted K-injective target is still K-injective. I read Stacks 08DK/08DL in cohomology.tex and the 08JA statement and proof in sites-cohomology.tex. All sites here are the small posets of opens, and all rings are commutative; no scheme, perfectness or boundedness hypothesis is imported. The local representative formula explains why restriction of a derived morphism is restriction of the corresponding Hom cocycle.

For Step 2 I checked that the new helper supplies both comparisons claimed. The basis vanishing itself is proved in the item: every presheaf map into an abelian sheaf is zero on a basis cover and hence zero by the equalizer axiom. def-weil-pbc-sites-and-cohomology states that axiom and def-weil-pbc-sheafification states the universal property used to show identity equals zero after sheafification. This does not assume that the original presheaf is already separated, nor that the inverse-image opens form a basis on X.

For Step 3 I checked bounded-derived-subcategories says that negative cohomology vanishing implies D-plus membership. lem-sc-ringed-space-module-sheaves-enough-injectives applies to any ringed space, including Y, and its source is Injectives 01DI, which I read. lem-weil-pbc-dplus-injective-representative clause (1) permits exactly lower bound 0, and clause (2) supplies K-injectivity. I read its sources Derived Categories 013K and 070J; 013K resolves the nonnegative truncation without introducing nonzero terms in negative degrees. def-sfb-right-derived-functor explicitly gives the termwise K-injective computation for additive evaluation. Thus this calculation does not require f_* itself to preserve ordinary injectives.

For Step 4 the only cited statement is def-weil-sheaf-of-modules-category, whose sectionwise-kernel clause is exactly what is used. The preceding nonnegative model makes H-zero a kernel with no degree-minus-one image. The displayed identification is explicitly compatible with restrictions because it uses the same closed section of J-zero on each open. This is a few-line calculation, not a new theorem node.

Step 5 combines preceding comparisons and the sheaf equalizer definition. I checked zero K, zero L, empty X or Y, the empty open and empty covering, the one-point space (where the helper is the identity comparison), non-intersection-closed bases, and complexes unbounded in both directions. The helper works for all q, including negative q, with no assertion that a nonzero cohomology presheaf is already a sheaf. There is no hidden use of a convergent unbounded spectral sequence. No proof step exceeds 2000 characters. No new node is elementary or restates a clause of the item: the only new node is a general direct-image comparison applicable before imposing any Ext vanishing. No SGA source was used. Existing metadata, ancestry, inherited searches and statement dependencies are retained. All off-unit proof tools are declared in split_report.tool_uses with their precise roles.
