# Q37 stage-1 repair: lem-sfb-stratified-constant-model-product-bound

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-stratified-constant-model-product-bound.json: unchanged statement, short four-step assembly.
- lem-sfb-proetale-scalar-local-model-representatives.json: statement, unsplit; scalar local representative construction; no exact Mathlib match.
- lem-sfb-noetherian-stratified-model-product-embedding.json: statement, unsplit; geometric product embedding for arbitrary supplied families; no exact Mathlib match.
- lem-sfb-small-site-image-subsheaf-representatives.json: statement, unsplit; actual sectionwise image representatives on any small ringed site; no exact Mathlib match.
- citations.json: verbatim statement quotations for every node used by every parent step.

## Attachments

None. A whole-source search in lean/WeilConjectures found no finished declaration for this item. The theorem AlgebraicGeometry.ProEtale.StratifiedConstantModels.exists_stratified_constant_model_product_bound in lean/Sheaf/Paper/StratifiedConstantModelProductBound.lean ends in sorry. Its indexing and image helpers construct data only.

## WANTED

None. No Lean files or compiler tools were used.

## Return repaired

The sandbox initially held only dispatcher marker files, no saved node/report/search log. I read the current shared item, which retains the returned ten-step argument and reviewed metadata, and copied it into this sandbox. Its statement is preserved byte-for-byte as a JSON string; all maintainer-owned fields are preserved. I did not rebase using git in the read clone: the required delivery tool builds against the current server base.

The return asks for at least two new statement-only unsplit nodes and at most 3000 parent-proof characters. This repair supplies three independently assignable nodes and a parent assembly of 2195 characters. The original arguments are preserved verbatim below. No proof is installed in the new nodes. Scalar descent, geometric embeddings and actual image coding are different arguments. The middle lemma accepts arbitrary supplied stratum sheaves, without assuming they are finite scalar models or constructing them; the image lemma treats any small ringed site and any small target family. No new node restates the whole item.

Ownership of old steps: 1–3 belong to lem-sfb-proetale-scalar-local-model-representatives; 4,5,7 belong to lem-sfb-noetherian-stratified-model-product-embedding; the finite-stratification choice of 6 is parent step 2, with the middle lemma accepting its resulting tuple; 8–9 belong to lem-sfb-small-site-image-subsheaf-representatives; 10 is retained as parent step 4, with its references updated to the new step numbering. Simultaneous choice of families remains explicit in parent step 1. Thus nothing from the 8703-character old argument disappears.

## Sources and search results

I read the current main-20261015 blueprint proof sk-lem-int-integral-heart-triangulated.proof.md, paragraph (2), final sentence, and unit sk-lem-int-integral-heart step 4, and the chapter record. Their route is essential smallness through finite stratifications, scalar presentations, local models and gluing. The sources are agent-written, so the parent proof_origin stays agent. I read Stacks proetale.tex Tag 098M (lemma-fibre-products-proetale), including its terminal object, fibre products and equalizer assertions, and sites-modules.tex Tags 03DA (lemma-abelian) and 03DB (lemma-limits-colimits). These support the retained explicit constructions; 03DA alone is not claimed to state image-code smallness.

For each new id I ran leanfinder, loogle, grep and leansearch through msearch.py and a second independent semantic phrasing. Exact queries/results are in each node and searches.jsonl; full outputs are search-local-*.txt, search-product-*.txt and search-image-*.txt. I read every hit. For scalar representatives, Quasicoherent.lean lines 234–290 only defines local finite presentations and provides their predicates, not small scalar-local-model representative families. For products, individual faithful-left-adjoint units, finite products, and Noetherian predicates do not supply the geometric jointly detecting stratum functors or bounded family. For images, PresheafOfModules.wellPowered in Presheaf/Generator.lean is about abstract presheaf subobjects; Abelian.isIso_factorThruImage is an abstract factorization; Sites.Subsheaf concerns set sheaves. Neither gives the explicit small module-subsheaf codes and sectionwise-range description required here. I read Sheaf/Limits.lean to distinguish products from image constructions. One image grep initially scoped a nonexistent Submodule.lean file; that empty result is explicitly recorded as unavailable and was replaced by a search of the actual Sheaf directory. No unrun searches are asserted.

I searched all DAG statements and titles for local-model representatives, subobject smallness, image subsheaves and stratified products, and searched the imported blueprint with blueprint_refs.py for local model, constant local, finite stratification, stratum, subobject, prescribed and image subsheaves; the new identifiers and concepts were also searched in both project Lean roots. Existing general lemmas are retained for the future workers to use; they are not duplicated as fresh foundations.

## Not duplicates

lem-sfb-proetale-scalar-local-model-representatives vs lem-sfb-locally-prescribed-modules-small: the existing lemma assumes small slice models and finite limits; the new lemma verifies the pro-etale site and scalar-presentation hypotheses and identifies geometric module restriction with those slice models.

lem-sfb-proetale-scalar-local-model-representatives vs lem-sfb-constructible-module-objects-essentially-small: the existing lemma treats locally finite presentations over an arbitrary ring object on a qc locally Noetherian X, with general coefficient-section entries; the new lemma has no Noetherian or qc hypothesis, constructs representatives within the narrower scalar-local-model class, and supplies scalar quotient codes.

lem-sfb-proetale-scalar-local-model-representatives vs det-def-sfb-constructible-local-model: this is a definition of a local scalar model, not its representative-family theorem.

lem-sfb-noetherian-stratified-model-product-embedding vs lem-sfb-joint-adjunction-model-embedding: the existing categorical lemma assumes abelian adjunctions, kernels, zero detection and products; the new geometric statement verifies these assumptions and constructs the bounded indexing family and sectionwise products.

lem-sfb-noetherian-stratified-model-product-embedding vs lem-sfb-stratified-constant-model-product-bound: the new lemma starts with arbitrary supplied sheaves and does not construct scalar-local-model representatives or bound image subsheaves.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-kinjective-set-of-subobjects: the existing theorem assumes an abstract generator and asserts set-sized subobjects; the new theorem needs no chosen generator and identifies actual ranges, uniqueness over each target and their sectionwise powerset codes.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sfb-stratified-constant-model-product-bound: the new lemma is for an arbitrary small ringed site and supplied family of targets and has no stratification or constructibility assertion.

lem-sfb-small-site-image-subsheaf-representatives vs def-cbc-finite-constant-coefficient-transport: the existing statement is Normalized finite scalar and etale-origin transport to constant coefficient modules; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs def-coef-compact-support-reduction-maps: the existing statement is Canonical quotient maps and completed-coefficient derived reductions; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs def-coef-normalized-dvr-tower: the existing statement is A normalized DVR tower; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs def-exc-proetale-sections-with-support: the existing statement is The pro-etale sheaf exceptional-image construction; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs def-pe-proetale-ring-restrict-scalars: the existing statement is Exact restriction of commutative ring-sheaf scalars on the small pro-etale site; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs def-pur-cochain-coefficient-arrows: the existing statement is Canonical scalar-association and transition arrows on cochain sheaves; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs def-pur-cochain-coefficient-universe-transport: the existing statement is Canonical common-universe transport of ring and module sheaves; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs def-pur-cochain-tensor-coherence-data: the existing statement is Canonical cochain ringed-pullback and coherence data; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs def-pur-flasque-support: the existing statement is Supported sections and flasque objects; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs def-pur-strict-quotient-diagonal-presentation: the existing statement is Section-normalized ordinary strict quotient presentation; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs def-pur-system-level-left-extension-basic: the existing statement is Strict systems and the unchanged left-extension interface; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs def-sp-varying-ring-operations: the existing statement is Canonical geometric operations on varying-ring systems; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs def-weil-derived-direct-image: the existing statement is Derived direct image; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs def-weil-pbc-derived-normalization-arrows: the existing statement is Canonical derived coefficient normalization arrows; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs def-weil-sheaf-of-modules-category: the existing statement is Category of sheaves of modules over a sheaf of rings; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs det-ind-heart-extensions: the existing statement is Ind-constructible sheaves are closed under extensions; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs det-ind-heart-full-faithfulness: the existing statement is Constructible sheaves are finitely presented; full faithfulness; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs det-pe-classical-sheaves-modules: the existing statement is The module form of the classical equivalence; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs det-pe-finite-local-systems-hom: the existing statement is Hom sheaves out of a finitely presented constant sheaf; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs det-pe-hypercover-complex: the existing statement is Cohomology via a weakly contractible hypercover; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs det-pe-sections-conservative: the existing statement is Evaluation on weakly contractible affines is conservative; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs det-pe-sections-limits-colimits: the existing statement is Evaluation on a weakly contractible affine preserves limits and colimits of modules; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs det-proper-heart-continuity-direct-image: the existing statement is Higher direct images commute with filtered colimits; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-cbc-localized-extension-zero-linear-derived: the existing statement is Module extension by zero is linear on the unbounded derived category; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-coef-exact-flat-complex-set-cogeneration: the existing statement is Set detection of the Ext orthogonal of exact flat-cycle complexes; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-coef-module-flat-cotorsion-foundation: the existing statement is The module-level flat cotorsion pair on a small ringed site; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-coef-sheaf-flat-model: the existing statement is Monoidal flat model for unbounded complexes on a ringed site; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-coef-small-flat-subextension: the existing statement is Bounded flat subextensions over a prescribed small flat subsheaf; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-coef-small-flat-subsheaf: the existing statement is Uniformly small nonzero flat subsheaves with flat quotient; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-exc-proetale-closed-exact: the existing statement is Exactness of closed direct image; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pc-module-filtered-colimits-tensor: the existing statement is Filtered colimits and tensor complexes of sheaves of modules; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pe-bounded-complex-direct-image-presheaf: the existing statement is Bounded-below direct-image cohomology is a sheafified inverse-image presheaf; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pe-finite-scalar-restriction-constructible: the existing statement is Finite scalar restriction preserves constructible complexes and bounds; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pe-internal-section-tensor-comparison: the existing statement is Relative tensor and K-flatness under the internal-to-sectionwise module equivalence; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pe-left-module-comparison-vanishing-criterion: the existing statement is Objectwise derived evaluation detects comparison direct-image vanishing; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pe-restricted-kflat-tensor-identification: the existing statement is Restricted scalar-first K-flat tensor models identify derived scalar extensions; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pe-successive-quotient-flat-complex-sequence: the existing statement is The successive coefficient sequence stays exact on flat-term sheaf complexes; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pe-successive-quotient-flat-tensor-sequence: the existing statement is Flat-term successive quotient tensor sequence; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pe-successive-quotient-linear-triangle: the existing statement is Successive derived quotients form a quotient-linear triangle; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-per-constructible-extension-finite-stage: the existing statement is Constructible-quotient extensions descend to a finite stage of the kernel; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-per-etale-closed-sheaf-internal-adjunction: the existing statement is Closed support kernel and internal sheaf adjunction over an arbitrary ring; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-per-etale-point-product-acyclic: the existing statement is Geometric-point product sheaves: adjunction, exactness and evaluation acyclicity; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-per-finite-closed-support-exchange: the existing statement is Closed extraordinary restriction commutes with finite direct image; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-per-galois-partition-exact-refinement: the existing statement is Exactness and common refinements for weak Galois constructibility; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-per-open-closed-constructible-test: the existing statement is Bounded constructibility detected by open and exceptional closed restriction; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-per-prime-power-trait-residue-model: the existing statement is Prime-power supported cohomology and canonical residue on a strictly henselian trait; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-per-trait-residue-model: the existing statement is Supported cohomology and canonical residue on a strictly henselian trait; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-based-sheaf-tensor-evaluation: the existing statement is Finite-basis tensor evaluation, exactness detection and the termwise complex comparison; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-coefficient-level-ordinary-images: the existing statement is Ordinary geometric images at the constant quotient levels; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-compatible-coefficient-tower: the existing statement is Compatible coefficient maps give a linear strict tensor tower; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-constant-sequence-module-equivalence: the existing statement is Constant-ring sequence modules are ordinary module towers; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-diagram-ring-restriction-pushforward: the existing statement is Derived coefficient restriction on ringed diagram topoi; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-exact-derived-coproducts: the existing statement is Coproduct preservation by exact derived functors; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-finite-free-quotient-completion: the existing statement is Finite free transport of regular quotient completion units; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-finite-free-quotient-tower: the existing statement is Strict quotient tower comparison induced by scalar coordinates; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-kflat-change-of-rings: the existing statement is Change of rings preserves K-flat complexes with flat terms; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-ringed-site-grothendieck-abelian: the existing statement is Sheaves of modules on a small ringed site are Grothendieck abelian; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-ringed-site-grothendieck-coefficient-universe: the existing statement is Grothendieck module categories at the coefficient universe; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-ringed-site-injective-mono-restriction: the existing statement is Injective modules on a ringed site restrict surjectively along monomorphisms; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-sequence-site-completion-projection: the existing statement is Constant/limit ringed sequence projection and coherent reduction; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-sheaf-ring-coefficient-ordinary-adjunction: the existing statement is Exact restriction and normalized ordinary scalar-extension adjunction on a general ringed site; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-signed-line-derived-base-change: the existing statement is Signed line comparisons and their unbounded derived tensor action; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-site-restriction-module-adjunction-exact: the existing statement is Restriction and extension by zero for modules on a localized site; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-strict-quotient-ordinary-flat-presentation: the existing statement is Ordinary strict quotient presentation and diagonal flatness; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-system-coproducts: the existing statement is Coproducts and derived evaluation for strict systems; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-system-derived-evaluation: the existing statement is Cohomology and joint detection by system evaluations; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-system-evaluation-kflat: the existing statement is Simultaneous componentwise K-flat representatives; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-system-evaluation-topos: the existing statement is Evaluation as inverse image on the ringed sequence site; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-system-grothendieck: the existing statement is Grothendieck abelian strict-system categories; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-system-ordinary-selected-extension: the existing statement is Ordinary subsequence left extension with actual transitions; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-system-ordinary-single-extension: the existing statement is Ordinary singleton left extension; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-system-ringed-sequence-site: the existing statement is Strict systems as modules on one ringed sequence site; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-system-scalar-coherence: the existing statement is Canonical scalar tensor unit and associators; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-system-scalar-generators: the existing statement is Unit tensor generators for scalar extension; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-system-scalar-model: the existing statement is Normalized scalar models for arbitrary sheaf-ring maps; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-pur-system-tensor-coherence: the existing statement is Canonical tensor coherence for a scalar assignment; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sf-comparison-pullback-exact: the existing statement is The comparison pullback is exact on sheaves of modules and commutes with cohomology sheaves; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sf-etale-module-stalk-cohomology-test: the existing statement is Module geometric stalks compute and detect unbounded cohomology; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sf-proetale-vanishing-detection: the existing statement is Detection of vanishing on affine weakly contractible objects; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sf-projective-cohomology-split-model: the existing statement is Finite projective cohomology splitting and shifted-free derived maps; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sf-ring-sheaf-closed-localization: the existing statement is Closed localization for arbitrary pro-etale ring-sheaf module objects; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sf-ringed-localization-rhom-orthogonality: the existing statement is Localization orthogonality for derived internal Hom; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sf-semilinear-scalar-ordinary-comparison: the existing statement is Ordinary scalar restriction with section-normalized comparisons; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sf-strict-dvr-reduction-triangles: the existing statement is Strict simultaneous DVR reduction models and residue triangles; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sfb-constant-finite-free-presentation-extension: the existing statement is Exact constant finite free presentations after flat sheaf scalar extension; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sfb-discrete-lattice-koszul-resolution: the existing statement is Discrete lattice derived invariants via a sheaf-module Koszul resolution; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sfb-flat-constant-module-scalar-mono: the existing statement is Regular constant scalars act monomorphically on flat module sheaves; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sfb-free-representable-derived-functions-model: the existing statement is Derived functions on a free representable module as sheafified derived sections; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sfb-ind-finite-free-scalar-model: the existing statement is Exact unbounded scalar model for an ind-finite-free coefficient algebra; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sfb-internal-action-site-presentation: the existing statement is Twisted-arrow site presentation of internal group actions on module sheaves; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sfb-module-upper-star-kflat-quasi-iso: the existing statement is The pullback of module objects preserves K-flat quasi-isomorphisms; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sfb-profinite-derived-functions-filtered-colimit: the existing statement is Filtered-colimit continuity of derived functions on profinite parameters; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sfb-qlbar-internal-hom-coefficient-comparison: the existing statement is Algebraic-closure internal Hom comparison from finite-field continuity; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sfb-reduction-single-cohomology-normalization: the existing statement is Cohomology of scalar reduction and signed single-sheaf identifications; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sfb-ringed-site-finite-retract-dual-exact: the existing statement is Internal dual and exact Hom of a finite-free retract sheaf; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sfb-scalar-adjunction-unit-coefficient-normalization: the existing statement is Normalized scalar adjunction on K-flat models and the coefficient unit; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sfb-section-ring-lax-pushforward-coherence: the existing statement is Section-ring reconstruction and lax direct image form a coherent exact comparison; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sfb-site-fp-stalk-realization: the existing statement is Local realization of a finitely presented module at a site point; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sfb-stratified-constant-model-product-bound: the existing statement is A small family of stratum-product and subobject models for integral constructible sheaves; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sp-finite-coefficient-realization-flat: the existing statement is Flatness of the canonical finite-coefficient realization; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sp-restricted-scalar-coefficient-local-constancy: the existing statement is Finite local cohomology of the restricted constant coefficient complex; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-sp-restricted-scalar-tensor-cohomology-comparison: the existing statement is Underlying cohomology comparison for K-flat scalar extension; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-trf-derived-sections-finite-pushforward-modules: the existing statement is Derived sections through finite pushforward for module sheaves; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-trf-finite-cech-augmentation-modules: the existing statement is Exact finite Čech augmentation for module sheaves; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-trf-frobenius-coefficient-dual-restriction: the existing statement is Residue coefficient restriction and the ambient dualizing object; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-trf-geometric-inverse-image-exact: the existing statement is Exactness of inverse image on abelian sheaves and modules; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-trf-one-point-derived-ring-identification: the existing statement is Terminal-site evaluation identifies ordinary modules and derived scalar extension; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-trf-site-derived-tensor-restriction: the existing statement is Derived tensor with a scalar-restricted sheaf on a ringed site; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-trf-witnessed-open-pullback: the existing statement is Derived pullback and open extension transport explicit etale-origin witnesses; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-constant-scalar-unit-quasi-isomorphism: the existing statement is The normalized regular coefficient scalar unit is a quasi-isomorphism; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-closed-immersion-pushforward-cokernel: the existing statement is Closed pushforward preserves module cokernels; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-diagram-site-module-equivalence: the existing statement is Product-site module sheaves are diagram modules; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-etale-open-cover-shriek-ses: the existing statement is Open-cover short exact sequence of etale extensions by zero; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-exact-faithful-torsion: the existing statement is Integer-torsion colimits under an exact fully faithful left adjoint; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-finite-perfect-adic-coefficient-limit: the existing statement is Actual coefficient limits, finite powers, and compatible finite-projective complex retracts; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-flat-constant-tensor-pro-zero-cones: the existing statement is Flat constant extension and K-flat tensor of pro-zero cone towers; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-flat-ringed-diagram-restriction: the existing statement is Flat coefficient restriction and normalized derived operations on module diagrams; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-flat-scalar-restriction-kflat: the existing statement is Flat scalar restriction preserves K-flat complexes; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-graded-realization-local-generators-epi: the existing statement is Local homogeneous generators give an explicit algebra-module epimorphism; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-local-derived-restriction-comparisons: the existing statement is Comparison of derived local restriction with exact inverse image and slice restriction; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-localization-inverse-image-coherence: the existing statement is Coherent localization comparison for exact inverse image; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-module-direct-image-left-exact: the existing statement is Direct image of etale sheaves of modules over a constant ring: module structure, additive and left exact; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-module-ses-cech-h1-surjective: the existing statement is Vanishing Cech H^1 of the kernel on a cofinal system of open coverings gives surjectivity on sections (O_X-modules); it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-module-sheaves-colimits-forgetful: the existing statement is Colimits of sheaves of modules and the forgetful functor to abelian sheaves; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-module-sheaves-enough-injectives: the existing statement is Sheaves of modules on the small etale site have enough injectives; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-module-sheaves-grothendieck-abelian: the existing statement is Sheaves of Lambda-modules on the small etale site form a Grothendieck abelian category; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-noetherian-stratum-detection: the existing statement is Finite stratified restrictions detect pro-etale sheaves; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-proetale-ringed-filtered-colimits: the existing statement is Transfer closed filtered-colimit preservation to arbitrary module coefficients; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits: the existing statement is Exact colimit-preserving evaluation at an affine weakly contractible object; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-proetale-weakly-contractible-evaluation-exact: the existing statement is Exact module-sheaf evaluation at a weakly contractible pro-etale object; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-quasi-coherence-scalar-restriction: the existing statement is Quasi-coherence over a quasi-coherent algebra agrees with quasi-coherence over the structure sheaf; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-scalar-localization-sheaf-exact: the existing statement is Exactness of actual scalar localization on module sheaves; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-singleton-site-module-comparison: the existing statement is Evaluation identifies the punctual ringed site with ordinary modules; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-pbc-site-flat-opcycles-tor-criterion: the existing statement is Flat opcycles from universal tensor exactness on a ringed site; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-point-finite-free-sections-tensor: the existing statement is Finite-free coefficient bases and the chain-level sections-tensor comparison at the point; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-point-proetale-sections-exact: the existing statement is Sections over an algebraically closed point are exact on the pro-etale site; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-proetale-countable-products-exact: the existing statement is Countable products of pro-etale modules are exact; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-proetale-direct-image-restriction-of-scalars: the existing statement is Derived pro-etale direct image commutes with restriction of scalars; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-proetale-isomorphism-inverse-image: the existing statement is Inverse image along an isomorphism of schemes on the pro-etale site; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-proetale-module-direct-image-left-exact: the existing statement is Pro-etale direct image is left exact; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-proetale-surjective-tower-derived-limit: the existing statement is Derived limit of a surjective tower of pro-etale sheaves; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-weil-restriction-of-scalars-exact: the existing statement is Exactness of restriction of scalars; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs lem-zl-contractible-derived-sections-tensor: the existing statement is Derived tensor evaluation on contractible affine and profinite objects; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs prop-weil-pbc-kinjective-resolutions-exist: the existing statement is Existence of K-injective resolutions; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs prop-weil-pbc-proetale-constant-exact: the existing statement is Exactness of the pro-etale inverse image for constant coefficients; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs sk-def-smooth: the existing statement is Smooth and allowed coefficients; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs sk-lem-pbc-finite: the existing statement is Finite morphisms; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs sk-lem-proper-heart-bound: the existing statement is A uniform bound for proper direct image; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs sk-thm-properbasechange: the existing statement is Proper base change on classical pro-étale complexes; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

lem-sfb-small-site-image-subsheaf-representatives vs thm-sf-direct-image-tor-amplitude: the existing statement is Direct image and finite Tor amplitude; it does not assert the new node's full sectionwise image-code/range representation for arbitrary small target families. The shared tag supplies the abelian/kernel input only.

## Review by Q37

I checked the repair against delivery-errors B–E with the node statements and local sources open. Every new node introduces its own universes, rings, sites, modules and quantifiers, cites the definitions its statement uses, records the exact blueprint paragraph and ancestry via this item, has proof=[], proof_deps=[] and proof_origin=null, and is unsplit. The new nodes preserve the old mathematical work rather than claim it has been proved. Their future proof obligations, including the existing statements they can use, are given in the verbatim handoff below. No SGA source is used.

Parent step 1 uses the scalar representative lemma's actual members and exhaustive isomorphism representatives; it does not infer essential smallness of a subclass just from essential smallness of a larger category. The set of bounded strata is small by the size convention, permitting simultaneous set-indexed choice. Parent step 2 uses the middle lemma's full indexing/product/mono conclusions. I separately read the locally-Noetherian quasi-separatedness statement and the constructibility definition: the former supplies exactly quasi-separatedness, which together with assumed qc makes the latter's global finite-stratification clause applicable. I checked that the families from step 1 contain representatives for precisely the restrictions in that definition. The maps use the specified module-adjunction units and the isomorphisms in the correct direction, not arbitrary embeddings. Parent step 3 uses the internal/sectionwise equivalence statement, which explicitly keeps the underlying sheaves, groups and restrictions. It then applies the image lemma with the already small J and section-small targets; the lemma explicitly gives both representation over the target and the total small indexing set. Parent step 4 keeps the old elementary empty-cover proof, citing the stratification and pro-etale site definitions. Every parent citation has an exact quote in citations.json.

For the local lemma I checked the old argument's inputs directly: weakly-etale stability includes morphisms between weakly-etale T-schemes; fibre products and equalizers give finite limits on the bounded skeleton; scalar finite presentations are actual quotients A^n/im(q); the site-object inverse-image lemma clause (1) applies to ring sheaves, and cartesian coefficients identifies the ring and scalar map. The prescribed-local-model smallness statement requires a small site, finite limits, terminal object, small section sets and small families on every slice, all supplied here; it returns members of the local-model class, not just ambient modules. The internal/sectionwise equivalence is needed here as well as for product and image computations.

For the product lemma I checked that it has the same Noetherian hypotheses as stratum zero detection, which is used with identity pro-etale covers. Cartesian coefficient pullbacks are exact with underlying abelian inverse image; hence they preserve kernels. The internal/sectionwise equivalence and the limits-sectionwise statement give the abelian categories, existing products and V-small sections required by the joint-adjunction model embedding statement. The families need no finiteness hypothesis beyond their small indices and section sizes. Counting finite bounded scheme lists and immersion arrows is distinct from choosing scalar-local representatives.

For the image lemma I checked the mono restriction carefully: sectionwise kernels and zero kernel imply injective section maps; for a mono the sectionwise bijections to its ranges transport the sheaf axiom. Linearity and naturality give inherited submodules and restrictions. Equal range families are precisely equality up to isomorphism over the target. The converse code is its inclusion's own image, so no effectivity of arbitrary descent data is invoked. The powerset product is V-small because both the site object set and section sets are V-small. This is not a claim about images of non-monos being sectionwise sheaves.

Small cases: on a point, scalar models A and A/varpi are both allowed, and the zero code m=n=0 gives zero; arbitrary torsion is not excluded. With one stratum the unit-component assertion is an isomorphism after relabelling. For an open/closed stratification, extension by zero on the open can inject into its direct image although equality need not hold. On empty X the empty covering forces every sheaf to have one-element sections, the empty product is zero and there is one image subobject. Empty strata are harmless. For an empty supplied label set the relevant summand of J is empty, so the embedding conclusion only applies when a tuple of isomorphisms exists; for J empty the total image-code set is empty. For the zero target there is exactly its zero image code. No extra separatedness, finite-type, finite-dimensional or invertibility-of-ell hypothesis was introduced.

No parent assembly step is longer than 2000 characters. The former long argument is split into three queue items, of comparable nontrivial scope, and no one of them contains the entire old theorem. There is no backward citation of the parent in a new statement or dependency, so the new dependency edges are downward. I corrected the invalid search scope and kept the previous review's internal-to-sectionwise bridge. No statement dispute was found.

## Complete preserved argument and handoff

The following are the original ten proof texts, verbatim, with their original cited statements. They are report material for future workers, not proof steps on the new nodes.

### Original step 1

For any stratum $T$, work on its fixed $\mathcal V$-small site. This site has terminal object $T/T$ and finite limits: for $U\to W\leftarrow V$ over $T$, both arrows are weakly étale by [sk-lem-pe-weakly-etale-stability], so $U\times_WV\to T$ is weakly étale by base change and composition. These scheme fibre products exist by [def-pc-fibre-product] and satisfy the same universal property in the full site category. Products are fibre products over $T$; the equalizer of $a,b:U\rightrightarrows V$ is $U\times_{V\times_TV}V$, using $(a,b)$ and the diagonal. Thus the same construction gives equalizers and finite limits. The bounded skeleton retains these limits up to isomorphism, by [def-weil-size-convention].

Uses: sk-lem-pe-weakly-etale-stability, def-pc-fibre-product, def-weil-size-convention

### Original step 2

Put $A=\mathcal O_E$. The scalar presentation codes form the set $Q=\coprod_{m,n\in\mathbf N}\operatorname{Mat}_{n\times m}(A)$ in $\mathcal U$, hence in $\mathcal V$ [def-weil-size-convention]. For a code $q:A^m\to A^n$, take the actual quotient module $P_q=A^n/\operatorname{im}q$. By [def-sc-finitely-presented-module], every finitely presented scalar module is isomorphic to some $P_q$: its given surjection $A^n\to P$ factors through this quotient, and the induced map is surjective with zero kernel. Consequently the modules $B_{U,q}=R_U\otimes_{\underline A}\underline{P_q}$ provide a small family of the scalar models in [sk-def-sfb-constructible] on every site object $U$. Passing an isomorphism $P\cong P_q$ through constant sheaves and tensor extension gives an isomorphism of these models; no assertion about arbitrary matrices of coefficient sections is used.

Uses: def-weil-size-convention, def-sc-finitely-presented-module, sk-def-sfb-constructible

### Original step 3

Apply [lem-weil-proetale-weakly-etale-localization] to each site object $U\to T$: $U_{\mathrm{proét}}$ is the slice $T_{\mathrm{proét}}/U$, with the same coverings. Clause (1) of [lem-sfb-proetale-object-inverse-image-restriction] identifies inverse image of any ring sheaf with slice restriction. Combining it with [sk-prop-sfb-cartesian-coefficients] identifies $R_T|_U$ with $R_U$, including its scalar constant-section map. Hence the families $B_{U,q}$ of step 2 are sheaves over precisely the restricted ring required by [lem-sfb-locally-prescribed-modules-small]. Apply that lemma on the site of step 1 with $I_U=Q$. For a module $M$ on $T$, the module pullback $M|_U$ of [sk-def-sfb-constructible] has underlying sheaf the inverse image, with action through the cartesian coefficient isomorphism (last paragraph of [sk-prop-sfb-cartesian-coefficients]), and clause (1) identifies that inverse image with the slice restriction. So the lemma's class is exactly the finite constant local model sheaves of the item, since the covers and scalar models agree. Its representative family consists of members of this class; denote it $(F_{T,t})_{t\in I_T}$, with $I_T\in\mathcal V$. All sites and section sets have the required size. The strata within the fixed scheme bound form a set in $\mathcal V$, so choose these representative families simultaneously, using set-indexed choice in an ambient universe containing $\mathcal V$.

Uses: lem-weil-proetale-weakly-etale-localization, lem-sfb-proetale-object-inverse-image-restriction, sk-prop-sfb-cartesian-coefficients, lem-sfb-locally-prescribed-modules-small

### Original step 4

A finite stratification is a finite list of schemes in the fixed bound and immersions to $X$ subject to the disjointness and covering conditions of [def-constructible-stratification]. Schemes and their morphisms in this bound have set-sized codes in $\mathcal V$ [def-weil-size-convention]; a finite list is therefore in a $\mathcal V$-small set, and imposing these conditions takes a subset. Call that set $H$. For $h\in H$ let its strata be $(S_s)_{s<n(h)}$. Then $J=\coprod_{h\in H}\prod_{s<n(h)}I_{S_s}$ is in $\mathcal V$, by closure under small sums and finite products. This is exactly the indexing set asserted in the statement, including all choices of stratum representatives.

Uses: def-constructible-stratification, def-weil-size-convention

### Original step 5

For $j=(h,(t_s)_s)$ the functors of [sk-def-sfb-module-pushforward-pullback] put every $a_{s*}F_{S_s,t_s}$ in $\operatorname{Mod}(R_X)$ and specify the adjunction units used in the item. These functors, and constructibility, are defined on the internal module objects $\operatorname{Mod}_{R_T}$; by [def-weil-pbc-internal-abelian-sheaf-module-equivalence] that category is equivalent to the sectionwise module sheaves of [def-weil-sheaf-of-modules-category] over the section-ring sheaf of $R_T$, by a functor keeping underlying abelian sheaves, sections and restriction maps, and $\operatorname{Mod}(R_T)$ below means either through it. These categories are abelian, with kernels computed sectionwise, by [def-weil-sheaf-of-modules-category]. Apply [lem-weil-pbc-module-sheaves-limits-sectionwise] to the finite discrete diagram of these direct images: it gives the product $P_j$ in that category, with $P_j(V)=\prod_{s<n(h)}(a_{s*}F_{S_s,t_s})(V)$. The section sets lie in $\mathcal V$; the empty product is the zero module sheaf.

Uses: sk-def-sfb-module-pushforward-pullback, def-weil-pbc-internal-abelian-sheaf-module-equivalence, def-weil-sheaf-of-modules-category, lem-weil-pbc-module-sheaves-limits-sectionwise

### Original step 6

Let $C$ be constructible. Its defining finite stratification in [sk-def-sfb-constructible] has finite constant local models on each stratum. Since $X$ is quasi-compact and locally Noetherian, it is Noetherian; [lem-weil-pbc-locally-noetherian-quasi-separated] gives quasi-separatedness. Thus $X$ is qcqs and the finite-stratification clause of that definition applies. Choose that stratification $h\in H$. For each of its finitely many strata, the representative property proved in step 3 supplies $t_s\in I_{S_s}$ and an isomorphism $\varphi_s:a_s^*C\xrightarrow{\sim}F_{S_s,t_s}$. Thus these choices define $j\in J$.

Uses: sk-def-sfb-constructible, lem-weil-pbc-locally-noetherian-quasi-separated

### Original step 7

Each $a_s^*$ is exact and its underlying abelian sheaf is the inverse image along $a_s$, by [sk-prop-sfb-cartesian-coefficients]; it is additive and preserves kernels. The restrictions $a_s^*$ jointly detect zero objects: apply [lem-weil-pbc-noetherian-stratum-detection] to the given finite stratification and the identity pro-étale covering on each stratum. Its Noetherian hypothesis is exactly quasi-compactness and local Noetherianity, both assumed for $X$; its arbitrary-ring-sheaf conclusion applies to $R_X$, identified with $R_{S_s}$ after inverse image by the cartesian coefficient isomorphism. Now apply [lem-sfb-joint-adjunction-model-embedding] with $\mathcal A=\operatorname{Mod}(R_X)$, $\mathcal B_s=\operatorname{Mod}(R_{S_s})$, $F_s=a_s^*$, $G_s=a_{s*}$, $M=C$, $B_s=F_{S_s,t_s}$ and $e_s=\varphi_s$. The abelian categories, adjunctions and product were verified in step 5. It follows that the map $u:C\to P_j$ whose components are $a_{s*}(\varphi_s)\circ\eta_{s,C}$ is a monomorphism, with exactly the units specified in the statement.

Uses: sk-prop-sfb-cartesian-coefficients, lem-weil-pbc-noetherian-stratum-detection, lem-sfb-joint-adjunction-model-embedding

### Original step 8

Fix $j$ and a subobject represented by a monomorphism $m:M\to P_j$. Its kernel arrow is zero, by cancellation against the zero arrow. Since kernels are sectionwise [def-weil-sheaf-of-modules-category], every $m_V$ is injective. Put $N(V)=m_V(M(V))\subseteq P_j(V)$. Linearity and naturality make these subsets submodules stable under restriction. The bijections $M(V)\to N(V)$ commute with restrictions and scalar actions; transporting the sheaf axiom through these bijections makes $N$ a module sheaf, and gives an isomorphism $M\cong N$ over $P_j$. This is the sectionwise image for a mono; no assertion that the sectionwise image of an arbitrary sheaf morphism is already a sheaf is being made. If two such monos have equal families $N(V)$, their induced isomorphisms to $N$ identify them over $P_j$. Conversely an isomorphism over $P_j$ gives the same subsets at every $V$.

Uses: def-weil-sheaf-of-modules-category

### Original step 9

Let $K$ be the object set of the fixed small site of $X$. The family of subsets specifying an image in step 8 is an element of $D_j=\prod_{V\in K}\mathcal P(P_j(V))$. Both $K$ and the section sets are in $\mathcal V$, so $D_j\in\mathcal V$ by [def-weil-size-convention]. Take the subset $E_j\subseteq D_j$ consisting of families that form module subsheaves of $P_j$. The inherited operations and restrictions determine a unique module subsheaf from each such family. Each is itself an image, namely the image of its inclusion. Step 8 therefore represents all subobjects, up to isomorphism over $P_j$, by this small family of actual image subsheaves. Finally $\coprod_{j\in J}E_j\in\mathcal V$, giving the required small family simultaneously for all $j$.

Uses: def-weil-size-convention

### Original step 10

If $X$ is empty, the empty list is a stratification by [def-constructible-stratification], and its tuple of indices is the unique empty tuple. The empty cover of the empty scheme is a pro-étale cover by [def-weil-pbc-proetale-site]. The sheaf axiom forces every module sheaf on that site to be zero: every site object over $X$ is empty, and its empty covering has exactly one matching family. Thus the map to the empty product of step 5 is $0\to0$, which is monic, and this product has exactly one image subsheaf. The same argument handles empty strata in any chosen stratification; zero scalar models, including the $m=n=0$ presentation, were already allowed in step 2.

Uses: def-constructible-stratification, def-weil-pbc-proetale-site

## Unfinished work

The three new nodes intentionally remain unsplit and unproved for independent stage-1 workers. No other mathematical work requested in this repair is left unfinished. Delivery validation and push follow below when completed.

## Validation

The first required server dry run completed successfully: OK (not pushed), preflight passed, commit 1f6efe61390. Final reading then corrected the retained empty-case paragraph's obsolete internal step numbers (old step 5 is now step 2; scalar codes now refer to step 1). Its original text remains verbatim in the handoff above. The final dry run is repeated after this correction.
