# Stage-1 repair: finite scalar comparison models

Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-integral-scalar-finite-comparison-models.json`: unchanged statement; short four-step assembly (2193 characters).
- `dag/nodes/sec-smooth-purity/lem-pur-integral-scalar-pullback-level-exists-unique.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-integral-scalar-tensor-level-exists-unique.json`: statement, unsplit; no Mathlib match.
- `citations.json`, `searches.jsonl`, and this report retain the citation and search evidence. Scratch scripts and a verbatim original-proof record are confined to `work/`.

Attachments to make (existing *sorried* declarations, not finished proofs):

- `WeilConjectures.scalarPullbackLevel_existsUnique` belongs to `lem-pur-integral-scalar-pullback-level-exists-unique`, `Sheaf.Paper.IntegralOperationsScalarComparisonModels`, `lean/Sheaf/Paper/IntegralOperationsScalarComparisonModels.lean:118`.
- `WeilConjectures.scalarTensorLevel_existsUnique` belongs to `lem-pur-integral-scalar-tensor-level-exists-unique`, same module, line 234.

Both new sandbox nodes contain the requested `lean.declaration` and `lean.module`, and the same information under `lean_candidates`. The packaging tool's `merge_split_node` retains `lean_candidates` but strips `lean`/`lean_audit` from new stage-1 nodes; the maintainer must install these attachment records from the preserved candidates. No Lean module is moved or written in this stage. Moving either declaration to a separate module would need its normalization predicate and imports moved too; retaining the actual existing module in the attachment is accurate.

WANTED: none.

## Repair order and existing evidence

The released stage-1 repair note dated 2026-10-27 overrides the old split-and-interface-review status. It expressly orders one node per sorried declaration, unchanged parent statement, and a parent proof of at most 3000 characters. This is the authorized exception to the usual rule against extracting a clause of the item merely to relabel it: there are two independent Lean holes to distribute, not one renamed theorem.

The required archive glob returned no abandoned attempts. The active sandbox initially contained only dispatcher marker files, no item, report or searches. The source search under WeilConjectures found no exact finished declaration and no blueprint tag for the item. The actual Sheaf module has exactly the two displayed `sorry` bodies at lines 125 and 240. Its other tower and good-complex results are retained assembly material, not evidence that the entire item is finished.

The blueprint ancestor command returns None because this extracted item's `created.item` is the old module name, not a DAG id. The dry run requires exactly the ancestor tool result, so the children record from.node=null and retain the already recorded real ancestor `def-weil-derived-pullback-tensor-hom` explicitly in from.place; the via list prepends the item to its existing chain. I did not change maintainer-owned creation metadata. I read the ancestor in `literature/blueprint/latest/blueprint/sec-proetale-coefficients/sk-prop-sf-open-closed-triangle/def-weil-derived-pullback-tensor-hom.md`: its last paragraph now refers coefficient compatibility to `sk-prop-scalar-six`. This legacy finite-model repair does not replace that current route or assert that the old final paragraph remains verbatim upstream.

## Source and citation corrections

There is no statement correction. The parent statement is byte-for-byte unchanged, as keep_plan requires. Its existing source metadata includes 099N, which is proetale-lemma-pushforward-Noetherian-case, and 08J9 in the module docstrings is internal Hom; neither proves these finite representative maps. The new nodes cite the actual balanced tensor sources: sites-modules.tex section-tensor-product (03EK), including its change-of-rings formula, and lemma-tensor-product-pullback (03EL). I read sites-cohomology.tex lemma-pullback-tensor-product (07A4) and lemma-pullback-K-flat (0G7E), and derived.tex definition-derived-limit (08TC). The latter warns that an abstract derived-limit triangle gives only nonunique isomorphisms; this is why our chain map uses both fixed Roos coordinates.

The old proof cited `lem-weil-scalar-extension-composition` for ordinary coefficient extension's object/map formulas. Its statement is instead about composition on rationalized constructible categories. I removed that proof citation. The parent statement still mentions it, so its statement dependency remains unchanged. Ordinary scalar extension is explicitly identified as termwise sheaf change of rings, using `def-pur-change-of-rings-complex` for exactly that definition; no property of the rationalized composition theorem is borrowed.

## Construction arguments assigned to the two new nodes

These are retained proof material for the workers taking the unsplit statements, not proof steps claimed as completed in the new nodes. The new nodes have empty proof and proof_deps as required for a one-level split.

For `lem-pur-integral-scalar-pullback-level-exists-unique`: use scalar tensor and inverse-image adjunction universal properties to send the generator 1 tensor f*(1 tensor x) to f*(1 tensor (1 tensor x)), extending by the target completed-ring action. The coefficient quotient square makes the assignment balanced. Inverse image is obtained by the Kan-extension/sheafification construction; the adjunction unit specifies what f*(x) means over a base-changed site object. Restrictions commute with the formula, so it induces the sheaf map. Applying the formula to d(x) on either side gives the same value, hence a chain map. Applying it to h(x) gives the same value for both composites for any chain map h, hence naturality. Equality on the unit images, inverse-image adjunction, tensor balancing and the sheafification universal property force uniqueness. This retains every part of old proof step 2's pullback argument and the existing declaration's docstring. Proving the complete model-specific universal-property implementation is the work assigned to this unsplit node; it has not been disguised as elementary assembly.

For `lem-pur-integral-scalar-tensor-level-exists-unique`: send 1 tensor ((1 tensor x) tensor (1 tensor y)) to (1 tensor (1 tensor x)) tensor (1 tensor (1 tensor y)), extending by the completed target scalar action. The quotient coefficient map gives the balancing relations in both entries and in the outer scalar extension. The construction commutes with restrictions and descends through sheafification. On bidegree (p,q), the two terms of the differential are mapped respectively to d(x) tensor y and (-1)^p x tensor d(y), so the same signed formula holds after the map. The coproduct universal property extends these summand maps to the direct-sum total complex; it also gives uniqueness once the balanced summand maps are unique. Applying a pair of chain maps to x,y proves naturality by the same explicit generator values. This retains old proof step 2's tensor argument and the existing docstring. It is not the assertion that arbitrary sheaf tensor sections are globally pure tensors.

## Retained original proof, verbatim

1. Use the original additive Roos construction, its proved coordinate characterization, generic naturality, and strict tower assembly helpers, all retained in ScalarRoosComparison. The finite-level and good-representative statements below are unchanged.

2. For pullback at each finite quotient level, use the scalar tensor and inverse-image adjunction universal properties to define the map sending 1 tensor f*(1 tensor x) to f*(1 tensor (1 tensor x)). The balanced relations, restriction maps, and differentials commute with this formula. Pure tensors and the inverse-image adjunction force uniqueness and naturality. For tensor at each level, the balanced tensor universal property gives 1 tensor ((1 tensor x) tensor (1 tensor y)) mapping to (1 tensor (1 tensor x)) tensor (1 tensor (1 tensor y)). The signed total differential commutes by bidegree, and the coproduct universal property gives the total chain map and its uniqueness. These are exactly the two pre-existing holes; no new comparison assertion is introduced.

3. Apply the existing consecutive reduction equations to these normalized maps. The retained proved scalarTowerAssembly constructs the strict tower transformation by recursion and proves its uniqueness componentwise. Define the pullback and tensor chain maps as the normalized Roos map followed by the strict tower map.

4. Identify ordinary coefficient extension with the concrete termwise change-of-rings complex using the existing object and morphism formulas. Transport K-flatness and flatness through that complex isomorphism. The change-of-rings K-flat theorem and the independent-coefficient tensor presentation supply the properties. Keep the existing proved scalarGood body and the prescribed ordinary pullback normalization unchanged.

The construction arguments of original step 2 are assigned above to the two new statement nodes; steps 1, 3 and 4 are still carried explicitly by the parent assembly. No argument of the original proof is discarded. In particular, strict consecutive equations, recursion, componentwise uniqueness, fixed diagonal Roos coordinates, concrete complex identification, and preservation of both flat terms and K-flatness remain visible.

## Mathlib search review

All new records are the exact tool/query pairs executed by msearch.py in this session; the log JSON is copied verbatim into results. Six records per new node cover LeanFinder, Loogle, LeanSearch and source grep, with a second semantic phrasing. I read the returned hits and the source of ModuleCat.ChangeOfRings, Sheaf.PullbackContinuous, Sheaf.Free, Sheaf.PullbackFree, and Presheaf.Monoidal. ModuleCat.extendRestrictScalarsAdj and ExtendScalars.hom_ext are ordinary-module adjunction and uniqueness ingredients; they do not construct the normalized finite quotient/sheaf/complex transformation in one specialization. SheafOfModules.pullback and pullbackIso define the general pullback, and the free-sheaf comparison hits apply only to free presentations. PresheafOfModules.Monoidal.tensorObjMap is the restriction map for a presheaf tensor, not our comparison. The second Loogle search returned a Lie bracket instance, unrelated here. No exact or one-line specialization was found. The parent's earlier H1 search records are preserved as inherited evidence, not presented as NG searches.

## Review by NG

I read the released repair, the chapter and unit records, the latest ancestor text, the two existing Lean signatures and their complete normalization predicates, the strict tower assembly helper, and scalarGood's object/map comparison. I checked the new pullback statement against lines 88-125 and the tensor statement against lines 201-240, including the direction of both functor composites, the target completed-ring action, all input complexes and chain maps, and the finite index shift: Lean n=0 is exponent 1, not the zero quotient. Neither new existence theorem needs good complexes; that hypothesis is imposed only when the parent later uses the good-complex assertion. Arbitrary scheme arrows are retained; no smoothness, properness, noetherianity, finite dimension or invertibility of ell is added.

Parent step 1 uses exactly the two new statements' unique natural maps and their displayed generator equations. It does not take reduction compatibility or a quasi-isomorphism from either. Step 2 uses exactly the two existing level-reduction statements: each assumes such a family and gives its consecutive equation. I opened both nodes and checked that neither claims tower existence. The induction on m-n, identity base, composition step, input naturality and componentwise uniqueness are written in the parent; no generic tower theorem is silently assumed. Step 3 uses the statement of def-sf-additive-roos-map for both coordinates and def-sf-strict-roos-functor for the induced map of towers; composing those actual chain maps is elementary. It never invokes an unspecified triangle completion, a derived isomorphism, or commutation with countable products. Step 4 uses def-pur-change-of-rings-complex's terms and differential, lem-pur-kflat-change-of-rings's precise K-flat-plus-flat-terms hypotheses and its two conclusions, and lem-weil-pbc-independent-sheaf-tensor-colimits's independent-universe tensor statement. The generic theorem is valid for any coefficient ring-sheaf map, so no finite-free basis or flat coefficient extension is inserted. The independent-coefficient colimit assertion is quoted only for what it states; the actual good-complex inference is the general change-of-rings theorem. The two generic off-unit tools are declared in split_report.tool_uses. Every used node's relevant statement is quoted verbatim in citations.json.

I tested identity coefficients and identity f (the formulas reduce to the ordinary unit/reassociation maps), the zero complex and zero tensor factor (unique zero maps), quotient exponent 1, an empty scheme, and unbounded complexes (every total differential acts on only the two adjacent summands; direct-sum totalization, not an unsupported infinite product). For a ramified extension, there is only the canonical quotient ring map, not an asserted equality or an isomorphism between residue rings; the maps are not claimed to be isomorphisms. I checked that new nodes have no parent in their stmt_deps, and the parent never uses its own derived scalar comparisons, avoiding cycles. The new nodes are deliberately unsplit, and their source-specialization arguments remain above for later workers. All four parent steps are shorter than 2000 characters, and their combined text is below the repair's 3000-character bound.

Against delivery-errors B-E: self-contained objects and hypotheses, explicit notions and definition citations, searched source tags and blueprint, exact logged searches, no false Mathlib leaf, no proof body on the unsplit children, no borrowed proof-only facts, no missing non-elementary assembly fact, and no circular or added-hypothesis shortcut. The two extracted clauses are explicitly required by the human's repair order to distribute the existing holes. Remaining work is precisely the two existing finite-level constructions, assigned to their own nodes; stage-1 assembly is complete.

## Not duplicates

lem-pur-integral-scalar-pullback-level-exists-unique vs lem-sfb-site-inverse-image-multimap-universal: the existing node states a set-valued finite-family inverse-image universal property, without completed scalar extension, quotient coefficient modules or cochain comparison.

lem-pur-integral-scalar-pullback-level-exists-unique vs lem-sfb-site-inverse-image-bilinear-adjunction: the existing node states an additive bilinear adjunction, without the completed/finite coefficient ring actions or the normalized natural cochain map.

lem-pur-integral-scalar-pullback-level-exists-unique vs lem-weil-pbc-ringed-slice-normalized-comparisons: the existing node states tensor/Hom comparisons for slice restriction; our map changes finite coefficient fields and allows an arbitrary scheme arrow.

lem-pur-integral-scalar-pullback-level-exists-unique vs def-sf-etale-open-scalar-data: the existing node states definitions of scalar/open-immersion adjunction mates on etale sites, not existence of the pro-etale finite quotient comparison.

lem-pur-integral-scalar-pullback-level-exists-unique vs lem-sf-proper-open-pull-tensor-composition: the existing node states coherence between geometric compositors and derived tensor comparisons, not finite scalar change.

lem-pur-integral-scalar-pullback-level-exists-unique vs def-coef-semilinear-geometry-derived: the existing node states a package requiring geometric comparison data, not existence of our completed/finite scalar representative map.

lem-pur-integral-scalar-pullback-level-exists-unique vs def-sf-point-evaluation-tensor-coherence: the existing node states coherence equations for supplied point tensor data, not a scalar comparison existence theorem.

lem-pur-integral-scalar-pullback-level-exists-unique vs def-sf-point-evaluation-scalar-data: the existing node states data at Spec of a field involving global-section evaluation, not finite reduction on an arbitrary scheme.

lem-pur-integral-scalar-pullback-level-exists-unique vs lem-coef-geometric-tensor-component-horizontal: the existing node states horizontal equations for a supplied system comparison, not construction of our scalar comparison.

lem-pur-integral-scalar-pullback-level-exists-unique vs lem-sf-open-total-normalized-comparisons: the existing node states scalar comparisons with slice/open extension; no finite quotient scalar-change pullback comparison for arbitrary f.

lem-pur-integral-scalar-pullback-level-exists-unique vs lem-weil-isomorphism-limit-scalar-chain-comparison: the existing node states requires a scheme isomorphism and completed coefficient pullback isomorphisms; our f is arbitrary and the finite quotient map is not an isomorphism.

lem-pur-integral-scalar-pullback-level-exists-unique vs lem-weil-pbc-ringed-slice-total-tensor-comparison: the existing node states a slice-restriction total tensor comparison, with no coefficient field change.

lem-pur-integral-scalar-tensor-level-exists-unique vs lem-pe-internal-section-tensor-comparison: the existing node states an internal-module to section-module equivalence over the same ring sheaf, not scalar change between completed fields and finite reductions.

lem-pur-integral-scalar-tensor-level-exists-unique vs lem-pe-restricted-kflat-tensor-identification: the existing node states a scalar-first/scalar-last derived identification for one K-flat complex and an arbitrary scalar map; no two-input finite total tensor comparison.

lem-pur-integral-scalar-tensor-level-exists-unique vs lem-pe-successive-quotient-flat-complex-sequence: the existing node states short exact sequences for powers of one regular element and one flat-term complex; no coefficient-field change or bifunctor comparison.

lem-pur-integral-scalar-tensor-level-exists-unique vs def-sfb-scalar-extension-pure-tensor-section: the existing node states only defines the canonical tensor section; our existence and uniqueness for complex bifunctors are additional assertions.

lem-pur-integral-scalar-tensor-level-exists-unique vs def-sf-etale-open-scalar-data: the existing node states definitions of scalar/open-immersion adjunction mates on etale sites, not existence of the pro-etale finite quotient comparison.

lem-pur-integral-scalar-tensor-level-exists-unique vs lem-sf-adic-module-section-comparison: the existing node states a coefficient-system/adic section equivalence, not the displayed normalized finite total tensor map.

lem-pur-integral-scalar-tensor-level-exists-unique vs lem-sf-slice-system-extension-construction: the existing node states constructs open extension on strict systems, not scalar change of two-input finite total tensors.

lem-pur-integral-scalar-tensor-level-exists-unique vs lem-sf-open-system-unit-sections: the existing node states normalizes an open-system adjunction unit on extension summands, not scalar/tensor comparison existence.

lem-pur-integral-scalar-tensor-level-exists-unique vs lem-weil-isomorphism-scalar-quotient-chain-squares: the existing node states finite coefficient comparison for one complex under scheme isomorphism pullback; no tensor bifunctor.

lem-pur-integral-scalar-tensor-level-exists-unique vs lem-sf-open-semilinear-ordinary-comparison: the existing node states compares open extension and simultaneous quotient systems, not ordinary coefficient-field change of a finite total tensor.

lem-pur-integral-scalar-tensor-level-exists-unique vs def-pur-module-pure-tensor: the existing node states defines pure-tensor sections and makes no comparison-map existence or uniqueness assertion.

lem-pur-integral-scalar-tensor-level-exists-unique vs lem-sf-native-geometric-tensor-comparison: the existing node states a derived geometric-forget comparison at algebraic-closure coefficients, not a finite quotient comparison for arbitrary module complexes.

The two new nodes also differ from their parent: each isolates one named Lean hole and neither asserts strict tower assembly, the diagonal Roos comparison, or preservation of good complexes. This is the released repair order's expressly required split.

The delivery gate sorts candidates differently from the read clone glob; I opened the additional candidate statements named by the first dry run:

lem-pur-integral-scalar-pullback-level-exists-unique vs lem-pur-integral-scalar-finite-comparison-models: the parent also assembles strict towers and Roos maps and preserves good complexes; this child isolates one of its two existing sorried declarations exactly as the released repair order requires.

lem-pur-integral-scalar-pullback-level-exists-unique vs def-a1-completed-pullback-universe-transport-data: defines universe transports and completed/finite geometric pullback normalizations for a single coefficient field, without a scalar comparison existence theorem.

lem-pur-integral-scalar-pullback-level-exists-unique vs def-a1-constant-complex-base-change-data: defines supplied finite/geometric reduction comparisons on bounded finite-projective constant scalar complexes, not existence of a comparison on arbitrary completed-module complexes.

lem-pur-integral-scalar-pullback-level-exists-unique vs def-a1-constant-complex-quotient-model: defines constant R-module quotient towers and their normalization predicates; our inputs are arbitrary module sheaves and our assertion is existence and uniqueness of a scalar comparison.

lem-pur-integral-scalar-pullback-level-exists-unique vs def-a1-finite-pullback-strict-tower-data: defines normalized quotient, Koszul and geometric pullback data for one coefficient field, without constructing a comparison between E and L.

lem-pur-integral-scalar-pullback-level-exists-unique vs def-a1-pulled-koszul-tower-normalization: defines geometric pullback normalizations on the two basis vectors of a principal Koszul complex over one field, not our scalar comparison.

lem-pur-integral-scalar-pullback-level-exists-unique vs lem-a1-balanced-finite-tower-generator-comparison: compares completed geometric pullback with finite geometric pullback for a single field and assumes ell invertible, not coefficient-field change for arbitrary schemes.

lem-pur-integral-scalar-pullback-level-exists-unique vs lem-a1-balanced-finite-tower-quotient-comparison: compares geometric pullback of a reduction tower with the finite geometric pullback tower for a single coefficient field; our comparison changes E to L.

lem-pur-integral-scalar-pullback-level-exists-unique vs lem-a1-balanced-finite-tower-scalar-comparison: compares reduction of geometric completed pullback with finite geometric pullback for a single coefficient field; despite scalar in the name it does not compare E and L.

lem-pur-integral-scalar-pullback-level-exists-unique vs lem-a1-completed-scalar-exact-base-change: treats completed scalar realization of constant R-modules and its geometric base change, not arbitrary completed-coefficient sheaves or change of coefficient field.

lem-pur-integral-scalar-pullback-level-exists-unique vs lem-a1-constant-complex-completed-pullback: constructs geometric reduction data from supplied finite comparisons on completed constant scalar complexes, not arbitrary completed-module complexes with a coefficient-field embedding.

lem-pur-integral-scalar-pullback-level-exists-unique vs lem-a1-constant-complex-finite-pullback: constructs a geometric comparison between two constant scalar quotient towers, not a comparison between E and L finite operation functors on arbitrary module sheaves.

lem-pur-integral-scalar-tensor-level-exists-unique vs lem-pur-integral-scalar-finite-comparison-models: the parent also assembles strict towers and Roos maps and preserves good complexes; this child isolates one of its two existing sorried declarations exactly as the released repair order requires.

lem-pur-integral-scalar-tensor-level-exists-unique vs def-a1-completed-pullback-universe-transport-data: defines universe transports and completed/finite geometric pullback normalizations for a single coefficient field, without a scalar comparison existence theorem.

lem-pur-integral-scalar-tensor-level-exists-unique vs def-a1-constant-complex-quotient-model: defines constant R-module quotient towers and their normalization predicates; our inputs are arbitrary module sheaves and our assertion is existence and uniqueness of a scalar comparison.

lem-pur-integral-scalar-tensor-level-exists-unique vs def-a1-finite-pullback-strict-tower-data: defines normalized quotient, Koszul and geometric pullback data for one coefficient field, without constructing a comparison between E and L.

lem-pur-integral-scalar-tensor-level-exists-unique vs def-a1-pulled-koszul-tower-normalization: defines geometric pullback normalizations on the two basis vectors of a principal Koszul complex over one field, not our scalar comparison.

lem-pur-integral-scalar-tensor-level-exists-unique vs def-per-etale-differential-pullback-presentation: defines etale relative differential representing pairs and their tensor pullback; it has no coefficient-field extension or cochain tensor comparison.

lem-pur-integral-scalar-tensor-level-exists-unique vs lem-a1-balanced-finite-tower-koszul-augmentation: compares geometric pullback of a principal Koszul augmentation assuming two supplied tower isomorphisms; it does not construct a two-input finite scalar tensor comparison.

lem-pur-integral-scalar-tensor-level-exists-unique vs lem-a1-balanced-finite-tower-quotient-comparison: compares geometric pullback of a reduction tower with the finite geometric pullback tower for a single coefficient field; our comparison changes E to L.

lem-pur-integral-scalar-tensor-level-exists-unique vs lem-a1-balanced-finite-tower-scalar-comparison: compares reduction of geometric completed pullback with finite geometric pullback for a single coefficient field; despite scalar in the name it does not compare E and L.

lem-pur-integral-scalar-tensor-level-exists-unique vs lem-a1-constant-complex-completed-pullback: constructs geometric reduction data from supplied finite comparisons on completed constant scalar complexes, not arbitrary completed-module complexes with a coefficient-field embedding.

lem-pur-integral-scalar-tensor-level-exists-unique vs lem-a1-constant-complex-finite-pullback: constructs a geometric comparison between two constant scalar quotient towers, not a comparison between E and L finite operation functors on arbitrary module sheaves.

lem-pur-integral-scalar-tensor-level-exists-unique vs lem-a1-constant-complex-normalized-reductions: constructs normalized quotient towers and reductions of constant scalar complexes, not the E-to-L finite tensor comparison bifunctor on arbitrary module sheaves.


The original step-2 construction paragraph is also retained verbatim, with H1 attribution, in each child source.note as source proof material. The children still have empty proof and proof_deps. This preserves the old argument within the new nodes without pretending their model-specific constructions have already been split.
