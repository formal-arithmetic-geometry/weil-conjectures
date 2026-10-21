# Worker report

1. Files written: dag/nodes/sec-smooth-purity/lem-fix-scalar-completion-associator.json (item, split in seven steps); dag/nodes/sec-smooth-purity/lem-fix-cofinal-roos-restriction.json (one new statement-only unsplit node, no Mathlib match); citations.json (one verbatim statement quote per step/citation); searches.jsonl (written by the prescribed msearch commands); this report. The original NY item and the entire previous Q09 report are preserved in scratch/item-ny-original.json and scratch/report-prior-attempts.md.
2. Attachments: none. Exact-id and notion searches in lean/WeilConjectures found no project declaration stating all clauses. The scalarCompletion declarations in lean/Sheaf concern individual comparisons and transport, not an attachment under the project's required WeilConjectures criterion.
3. WANTED: none.
4. Previous input defect resolved on resumption: the assigned item now exists in the current live DAG. A field-by-field comparison shows that the retained statement, title, source, chapter, unit, blueprint ancestry, statement dependencies and NY creation provenance agree with the live item. The earlier recovery and failed dry-run history below are retained as history. No mathematical statement dispute or weakening was needed.
5. Unfinished: delivery status is recorded below. No Lean was written, no compiler/Lake/build tool was run, and no agent was started. The current resumption accidentally ran one read-only git status command during initial inspection, contrary to the brief; it made no repository change. No further direct git commands were run.

## Source and route

Read GOAL.md, roles/worker.md, the stage-1 brief and stage document, SETUP.md's three levels and generic-tool convention, and delivery-errors B–E. Read dag/chapters/sec-smooth-purity.json, dag/units/sk-prop-sf-pf-reduction.json and the current blueprint lem-fix-operation-reduction.proof.md, paragraph 3. That paragraph transports the actual scalar, tensor, unit and counit maps to field stages. The present split supplies its strict scalar-completion associator; it does not replace the unit's projection-formula route. Generic off-unit tools are declared in split_report.tool_uses.

Read Stacks algebraization.tex Tag 099B, lemma-derived-completion, statement and proof, and Tag 0A0E, lemma-derived-completion-koszul, statement and proof. These supply the general completion context, not a false claim that Stacks states this field-tower identity verbatim. Read sites-cohomology.tex Tag 0941, lemma-derived-limit-is-ok, statement and proof. That source constructs the Roos realization on strict towers. The explicit arbitrary-subsequence formulas in the new node are an agent refinement of this model and of the existing arithmetic restriction statement. The item proof_origin is agent.

## Review by Q09

I read each cited node's statement in the live DAG, including the long current integral-scalar-extension and finite-free-comparison statements. The copied item spells out rho as the same-index constant quotient map after the finite projection, the strict coefficient transitions, restriction to the target completed ring, and the termwise Cone(1-s)[-1] model. This matters: the proof does not replace a strict tower with unrelated isomorphisms of values.

Step 1 uses lem-weil-finite-free-completed-scalar-comparison for the canonical ring maps and finite freeness; lem-weil-l-adic-extension-absolute-value and lem-weil-l-adic-extension-integers-dvr give positive ramification powers and units. I checked that regularity and sheaf quotients are supplied by lem-weil-pbc-constant-completion-equivalence together with exact sheafification, rather than assumed from an ordinary ring calculation. The latter node requires a Noetherian coefficient ring, which holds because the valuation ring is a PID. The product theorem applies to arbitrary completed ring sheaves on any small pro-etale scheme site; it therefore supplies exactly the three module-product and abelian-product hypotheses required by exchange. No hypothesis on the scheme's dimension, finiteness or Noetherianity enters.

Step 2 uses lem-pc-kflat-resolution and lem-pur-kflat-change-of-rings for the resolving representatives and their change of rings. The explicit balanced formulas give an isomorphism of the actual quotient systems and identify the actual rho actions and transitions. Quotient-scalar-comparison-descent fixes the zero shifted-product augmentation and its derived naturality; integral-scalar-extension-well-defined identifies the target functor and ensures resolution independence. The ordinary successive-derived-quotient-normalization statement gives precisely the unrestricted ring-sheaf associator and its iterated coherence, not merely vector-space scalar extension. I checked both displayed inverse maps and the order of scalar multiplication.

Step 3 applies lem-pur-finite-free-completion-exchange to S -> T, with every hypothesis checked in step 1. Its statement specifies the tensor/product comparison, quotient maps, arithmetic restriction and the unit equation; it also explicitly says basis independent and no boundedness hypothesis. The existing exchange-coherence statement says that successive comparisons are equal on the actual Roos coordinates after the specified arithmetic restrictions, including their augmentations. It is a distinct generic input, not the present complete-input scalar associator in disguise. No step cites only a definition for an unproved exactness or coherence assertion.

Step 4 constructs d and aI explicitly. The domains are C_b D_L C_a K and D_M C_b D_L C_a K, respectively, and the target is J=D_M C_ba K. Finite-free scalar comparison supplies completeness of C_ba K and of J. Its identity-extension clause makes the actual unit eta_J invertible. Thus the inverse used in the formula is the inverse of a specified natural completeness map, not a chosen isomorphism of values and not a chain-level inverse. The elementary operations are functorial images and composition of the isomorphisms already supplied.

Step 5 is the written naturality calculation. I checked aI eta=d using eta_J d = D_M(d) eta, then substituted the unit equation epsilon C_b eta_L = eta_M and naturality through alpha. The source of the result is C_b C_a K, exactly the source of the requested normalization. The final I_b(chi_a) chi_b formula is naturality of the same quotient unit. This proves equality before any use of finite-level evaluation to detect derived morphisms.

Step 6 uses the new general cofinal Roos statement for non-arithmetic choices; the live arithmetic theorem alone would not justify them. I corrected an initially drafted 'common subsequence' argument: two subsequences can have disjoint images, so they compare via their invertible restrictions from the full tower, rather than an asserted common image. Both restriction maps preserve the actual augmentation. Finite-free tensor commutes with their finite-block sums and product projections by its finite-direct-sum description. Resolution independence uses the already normalized descent and exchange comparisons. The uniqueness invoked is cancellation of the invertible composite I_b(chi_a) chi_b, never uniqueness of a lift to an arbitrary distinguished triangle.

Step 7 precomposes the two four-field routes with the specified threefold chi comparison. Each factor is invertible because the inputs and their finite-free scalar extensions are complete. Naturality and the step-5 formula reduce the routes to the ordinary successive-scalar coherence. The repeated-field cases use the actual completeness unit given by the finite-free-comparison statement; they are not claimed to be strict equality I_FF=id before that identification. The displayed multiplication formulas verify both unit directions. There are no steps over 2000 characters and no elementary child nodes.

I tested zero K, the empty scheme, all fields equal, one repeated adjacent field, unramified extension (e=f=1), ramified extensions (including e=2,f=3), a nonzero unit relating uniformizers, and unbounded complete K. The constructions use no bounded amplitude, site-perfectness, constructibility, or finite-type condition. For e=2,f=3 the cofinal blocks compose to the target powers 6n, with no spurious multiplication by a unit on residue classes. The only restriction on the new cofinal map is strict increase and unboundedness; identity, arithmetic multiples, deletion of a finite prefix, and a nonlinear subsequence such as n^2 all satisfy its statement. The zero tower and constant tower also give the asserted comparison.

I checked B1–B10: the new node is self-contained, every notion has a stated dependency, the source names a tag and label, it contains no proof or proof dependency, and all search records are actual Q09 msearch entries. C1/C4 are checked above and citations.json quotes the actual statements verbatim. C5 duplication searches used the whole DAG, blueprint helper and project Lean, not only this chapter. D1/D2 do not apply: the new lemma concerns arbitrary strict towers over an arbitrary ringed site, has no scalar fields, tensor functors or chi comparisons, and is a small input only for cofinal choice independence. E1/E4 were checked by typing d, eta and aI as above. The full prior report and original imported search records remain available in scratch; the delivered node search fields use only searches actually performed by Q09, without attributing NY's prior searches to this group.

## New node and proof guidance

lem-fix-cofinal-roos-restriction is a statement-only lemma. Its source is Stacks 0941's strict Roos model, refined by the following argument. Coordinate selection a and the finite-block transition sum b satisfy b(1-s)=(1-s')a by telescoping. Split the countable product into the selected coordinates and the finite intervening blocks, including the initial finite prefix. Within each block the discarded-coordinate part of 1-s is upper triangular with identity diagonal, and its inverse is the finite geometric series in its strictly upper triangular transition part. These operations are well-defined product morphisms even when block lengths are unbounded, since each output coordinate uses only its own finite block. Eliminating these invertible blocks expresses the full cone as the selected-tower cone plus a contractible identity cone. The induced comparison is exactly selection on the source product and the weighted block sum on the target product, so it is a quasi-isomorphism. The consecutive block sums for two restrictions partition precisely the composite interval; transition composition gives the asserted strict composition formula. On an augmented tower the shifted-product coordinate is zero, remains zero under b, and a selects exactly the retained quotient maps. This proves the stated augmentation normalization. This argument is guidance for the node's later splitter; the node itself has no proof.

The new node's Q09 searches used LeanFinder, Loogle, grep and LeanSearch, followed by a second semantic phrasing and another grep. Results concern general mapping cones, ordinary inverse systems or levelwise complex limits, not this specified quasi-isomorphism and its coordinates. The item searches likewise returned ordinary AdicCompletion and scalar-tower declarations, not the derived ring-sheaf comparison. I read Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean:57–80 (ofTensorProduct and its naturality); these are ordinary module completions. No Mathlib leaf is claimed. The full exact query strings and raw summaries are in searches.jsonl and the node records.

## Not duplicates

lem-fix-cofinal-roos-restriction vs lem-sp-strict-tower-arithmetic-restriction: the live result permits only n -> en and is formulated on total derived limits; the new result allows any strictly increasing unbounded subsequence, including n^2 and n+2, with its actual strict cone coordinates and composition.

lem-fix-cofinal-roos-restriction vs lem-pur-compact-support-roos-cofinality: the live result is arithmetic and uses a constant coefficient ring, adding a finite-free tensor comparison. The new result is the arbitrary-subsequence restriction for a general ring sheaf, with no scalar-extension assertion.

lem-fix-cofinal-roos-restriction vs lem-pur-system-derived-subsequence: the live result identifies derived evaluation and composition of restriction functors for varying coefficient systems; it does not assert that inverse limits are unchanged or give the block map between Roos cones.

lem-fix-scalar-completion-associator vs lem-pur-finite-free-completion-exchange-coherence: the live theorem compares C_V(alpha) epsilon_b T_b(epsilon_a) with epsilon_ba alpha_C on arbitrary inputs; the item constructs the associator for independently specified completed scalar functors on complete inputs, normalizes it by actual chi maps, and states unit/pentagon and representative/cofinal independence. The exchange theorem is an input, not an exact attachment.

lem-fix-cofinal-roos-restriction vs def-a1-lisse-section-evaluation: the existing node is Canonical evaluation of ordinary common-stage sections at a geometric point; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-a1-integral-pullback-completed-comparison: the existing node is The integral derived pullback agrees with the strict-tower completed pullback; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-dl-a1-constant-field-charts: the existing node is Pointed geometric affine charts and adic open-image comparison; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-per-algebraic-local-duality: the existing node is Algebraic local duality with completed Ext; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs def-zl-field-weil-shriek-shift-data: the existing node is Canonical field-coefficient Weil compact support and shift data; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pod-integral-pullback-composition: the existing node is Composition isomorphism for integral derived pullbacks; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pod-integral-pullback-system-comparison: the existing node is For every morphism f:X→Y of schemes with ell invertible, the actual constructible completed integral pullback followed by coherent system reduction is naturally isomorphic to coherent system reduction followed by exact finite-system inverse image; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pod-integral-system-pullback-lift-associativity: the existing node is Associativity of a fixed fully faithful integral pullback lift; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pod-integral-system-reduction-fully-faithful: the existing node is Coherent reduction is fully faithful on the full category of derived-complete bounded constructible integral coefficient objects; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs det-pe-continuous-cohomology-etale: the existing node is Identification with continuous étale cohomology; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pe-completion-triangle-comparison: the existing node is Exact completion functor and its canonical triangle comparison; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pe-integral-completion-presentation: the existing node is Canonical completeness in the completed integral coefficient presentation; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs def-weil-pbc-derived-reduction-model-data: the existing node is Derived reduction model data and normalized complex comparisons; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs def-weil-pbc-koszul-reconstruction-models: the existing node is The fixed Koszul and quotient reconstruction models; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs def-weil-pbc-ringed-koszul-system: the existing node is The finite strict Koszul system and its derived-limit presentations; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-completed-fiber-cech-comparison: the existing node is Published completed Koszul fiber compared with Cech internal Hom; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-completed-fiber-roos-representative-comparison: the existing node is The explicit Koszul comparison is compatible with every derived representative; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-completed-fiber-strict-limit-comparison: the existing node is Published completed Koszul fiber computes the strict derived limit; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-completed-koszul-product-comparison: the existing node is Finite Koszul comparison induces the normalized product-fiber comparison; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-direct-image-roos-normalization: the existing node is Canonical direct-image limit comparison as a morphism of Roos triangles; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-exact-products-roos-comparison: the existing node is The normalized Roos fibre computes derived inverse limit with exact products; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-finite-perfect-adic-coefficient-limit: the existing node is Actual coefficient limits, finite powers, and compatible finite-projective complex retracts; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-finite-perfect-adic-complex-roos: the existing node is Roos limit of a termwise epimorphic completed-module complex tower; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-finite-perfect-adic-marked-roos: the existing node is Roos limit of the canonical finite-projective quotient diagram; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-finite-perfect-adic-realization: the existing node is Completed realization of uniform finite perfect quotient models; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-finite-perfect-adic-tower-limit: the existing node is Specified completed strict limit from a compatible finite-projective marking; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-flat-constant-tensor-pro-zero-cones: the existing node is Flat constant extension and K-flat tensor of pro-zero cone towers; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-rectangle-derived-limit: the existing node is The rectangle passes to the derived limit; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-ringed-cech-koszul-comparison-existence: the existing node is Existence of the normalized ringed Koszul Cech comparison; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-ringed-cech-koszul-comparison-on-site: the existing node is A unit-compatible Cech Koszul comparison on one ringed site; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-ringed-cech-koszul-dual-limit: the existing node is Extended Cech complex and Koszul dual limit; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-ringed-cech-koszul-hom-limit-comparison: the existing node is Telescope Hom comparison for a prescribed strict Koszul limit; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-ringed-strict-tower-homotopy-limit: the existing node is Strict tower homotopy limit; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-pbc-stratum-completion-unit-restriction: the existing node is Restriction and finite-stratum detection of the adic completion unit; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lemma-weil-pbc-koszul-quotient-limit: the existing node is Koszul and quotient towers have the same limit; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs prop-weil-pbc-koszul-reconstruction-comparison: the existing node is Comparison of completed Koszul and quotient derived limits; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs prop-weil-pbc-koszul-reconstruction: the existing node is Koszul and quotient reconstruction; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs def-coef-ringed-sequence-site: the existing node is Canonical ringed sequence site for the coefficient quotient tower; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-coef-derived-system-evaluation-calculus: the existing node is Coherent derived reduction, limit adjunction and fiberwise evaluation; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-coef-finite-adjunction-diagram-realization: the existing node is Finite exceptional operations and enriched adjunction on coherent coefficient systems; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-coef-sequence-global-sections-evaluation: the existing node is Derived termwise global sections with finite evaluation and transition normalization; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-coef-sequence-projection-derived-adjunction: the existing node is Derived adjunction of a ringed sequence projection; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-coef-sequence-pushforward-limit-projections: the existing node is Restricted total-limit comparison with adjunction projections; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-coef-sequence-sections-limit-comparison: the existing node is Derived sections and total limit with specified projections; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-coef-tower-coaugmentation: the existing node is Compact-support tower coaugmentation; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-fix-constructible-tensor-completion: the existing node is Ordinary and completed tensor agree on integral constructible complexes; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pod-identity-compact-support-normalization: the existing node is Canonical identity compact-support normalization; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sf-identification-coefficient-transport: the existing node is Identity-point composition normalization at all coefficient stages; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sf-integral-compactification-comparison-bridge: the existing node is Constant-tower and semilinear-counit normalizations of integral compactification composition agree; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sf-integral-compactification-system-realization: the existing node is Coherent integral realization of compactification expressions and their maps; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sf-integral-open-product-diagram-normalization: the existing node is Strict-diagram normalization of integral open product comparisons; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sf-integral-open-reduction-comparison: the existing node is Strict reduction and normalized realization of completed open extension; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sf-point-fibre-derived-tensor: the existing node is The point fibre functor preserves derived tensor at all coefficient stages; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sf-rational-slice-completed-evaluation: the existing node is Restriction compatibility for completed rational evaluation; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sf-rational-thick-evaluation: the existing node is Triangulated closure of the rational evaluation class; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs prop-coef-integral-dualizing: the existing node is The integral dualizing object and its adjunction; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sfb-adic-complete-hom-section-surjective: the existing node is Compatible finite-reduction morphisms lift into a complete target; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sfb-adic-complete-reduction-cone: the existing node is Normalized quotient homotopy-limit cone for a complete object; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sfb-adic-stratum-completion-unit: the existing node is Restriction of the completion unit to strata and covering slices; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sfb-ringed-complete-triangulated: the existing node is Exact Koszul completion and the triangulated complete locus; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs def-pur-integral-operation-shift-data: the existing node is Representative-normalized operation and independent-slot shifts; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs def-pur-principal-koszul-quotient-towers: the existing node is Canonical principal Koszul and quotient towers with tensor augmentations; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs def-pur-synchronized-canonical-maps: the existing node is The same canonical map at two independent input families; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs def-sp-strict-tower-arithmetic-restriction-data: the existing node is Arithmetic restriction and its specified product and cocone maps; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs def-weil-strict-roos-model: the existing node is StrictRoosModel; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs det-sp-normalized-equivalence: the existing node is Integral constructible complexes are normalized constructible towers; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-cbc-completed-pullback-triangles: the existing node is Completed pullback preserves shifts and distinguished triangles; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-cbc-exact-product-functor-strict-limit: the existing node is Canonical strict derived-limit comparison for exact product-preserving module functors; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-coef-constant-tower-roos: the existing node is Canonical Roos triangle of a completed-coefficient derived tower; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-coef-sequence-roos-model: the existing node is Normalized DVR tower carried by a normalized derived coefficient sequence; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pur-compact-support-completed-projection-coherence: the existing node is Completion coherence for the integral projection mate; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pur-compact-support-integral-coefficient-comparison: the existing node is Integral compact support under finite free coefficient extension; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pur-compact-support-roos-cofinality: the existing node is Cofinal restriction of a Roos tower complex; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pur-completed-operation-tower-substitution: the existing node is Coherent substitution of normalized systems into completed operations; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pur-condensed-tate-realization: the existing node is Realization of the reconstructed Tate tower in the condensed coefficient category; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pur-derived-complete-koszul-reconstruction: the existing node is Koszul reconstruction of a derived-complete reduction tower; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pur-finite-free-completion-exchange-coherence: the existing node is Coefficient-tower coherence of the specified quotient-completion exchange; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pur-finite-free-completion-exchange: the existing node is Finite free change of rings exchanges quotient completion on arbitrary complexes; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pur-integral-ambient-operation-models: the existing node is Ambient completion presentations for integral pullback and tensor; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pur-integral-coherence-tower: the existing node is Coherence identities on normalized integral comparison towers; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pur-integral-operations-scalar-extension: the existing node is Integral derived operations commute with finite scalar extension; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pur-integral-realization-shift-coherence: the existing node is Shift compatibility of strict-system realization maps; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pur-integral-tower-limit-comparison: the existing node is Derived limit of the strict integral comparison tower; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pur-reduction-limit-shift-adjunction: the existing node is Shift compatibility of the reduction and total-limit adjunction; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pur-roos-additive-comparison: the existing node is Additive comparison for the strict Roos cone; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-pur-roos-intrinsic-completeness-equivalence: the existing node is Roos and intrinsic completeness for completed local-field coefficients; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sf-cbc-compact-support-composition-limit: the existing node is Normalized reconstruction of composites of completed operations; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sf-cbc-constant-tower-direct-image-normalization: the existing node is Constant strict towers and normalized derived direct image; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sf-cbc-extension-zero-completion: the existing node is Strict reduction of completed extension by zero; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sf-completion-unit-finite-projection: the existing node is Projection of the completion unit is the finite scalar-extension unit; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sf-quotient-tower-evaluation-complex: the existing node is Explicit finite evaluation of a quotient-tower complex; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sf-strict-roos-derived-limit-comparison: the existing node is Strict Roos cone comparison with total derived inverse limit and evaluations; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sp-completed-pullback-adjunction: the existing node is Completed pullback is left adjoint to direct image; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sp-completion-mate-comparison: the existing node is The strict quotient-tower exchange realizes the completed-adjunction mate; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sp-levelwise-kinjective-tower-image: the existing node is Levelwise K-injective towers compute additive functors applied levelwise; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sp-proper-open-tower-comparison: the existing node is Open-adjunction normalization of proper/open interchange on strict coefficient towers; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sp-slice-restriction-strict-derived-limit: the existing node is Slice restriction commutes with total derived inverse limit of strict towers; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sp-strict-tower-arithmetic-restriction-cochain-model: the existing node is Finite-block arithmetic cochain Roos comparison; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sp-strict-tower-arithmetic-restriction-comparison: the existing node is Normalized derived arithmetic comparison; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sp-strict-tower-arithmetic-restriction-model: the existing node is Localized arithmetic cochain comparison and derived normalization; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sp-strict-tower-arithmetic-restriction-resolution: the existing node is Simultaneous degreewise injective K-injective tower resolutions; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-sp-strict-tower-arithmetic-restriction: the existing node is Canonical restriction of strict derived towers to arithmetic subsequences; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-compact-support-reduction-tower-functor: the existing node is Coherent compact-support reduction tower functor; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-derived-direct-image-composition: the existing node is Composition of derived direct images; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-integral-scalar-extension-well-defined: the existing node is The integral scalar extension is well defined, a derived limit, and O_E-linear; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-ringed-tower-pushforward-limit-comparison: the existing node is Derived pushforward commutes canonically with strict tower inverse limit; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-strict-roos-comparison: the existing node is Natural comparison of strict derived inverse limit and the product cone; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-strict-roos-derivation: the existing node is StrictRoosDerivation; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-strict-roos-normalization: the existing node is StrictRoosNormalization; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs sk-lem-sp-tower: the existing node is Reconstruction of a normalized tower; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs thm-cbc-complete-proetale: the existing node is Complete pro-etale compact-support base change; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs def-trf-coefficient-tower-operations: the existing node is Coefficient tower operations and point sections; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs def-trf-compact-support-system-evaluation-diagram: the existing node is The actual compact-support system evaluation diagram; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs def-trf-integral-tower-inverse-image-unit: the existing node is Canonical inverse-image tensor unit on entire quotient towers; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs def-trf-total-etale-augmentation-adjunction: the existing node is Canonical adjunction of a total small etale augmentation; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-trf-compact-support-system-evaluation-coherence: the existing node is Comparison of strict and enhanced system operation models; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-trf-completed-stalk-reparametrization-coherence: the existing node is Completed stalk comparisons and source reparametrization; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-trf-integral-cone-counit-realization: the existing node is The derived-limit counit recovers a compatible tower family from its cone lift; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-trf-integral-inverse-image-comparison-composition: the existing node is The integral inverse-image/pullback comparison respects composition; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-trf-integral-point-transport-tower-powers: the existing node is Point transport on whole coefficient systems, powers and integral realization; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-trf-integral-pullback-comparison-realization: the existing node is Strict-system realization and composition coherence of integral pullback comparisons; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-trf-integral-pullback-reduction-counit: the existing node is K-flat reduction-unit counit calculation for integral inverse image; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-trf-integral-pullback-resolution-matching: the existing node is Counit identity for the inverse-image/pullback comparison; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

lem-fix-cofinal-roos-restriction vs lem-weil-isomorphism-derived-pullback-comparison-normalization: the existing node is Specified inverse-image comparison is the completion unit; the new statement requires the explicit selected-coordinate/finite-block cone quasi-isomorphism for every strictly increasing unbounded subsequence, with strict composition and augmentation equations. This is neither the arithmetic-only comparison nor mere derived-limit existence, an additive tensor comparison, or a functor definition.

## Previous attempts

The entire prior report, including the earlier missing-item blockers, is retained verbatim in scratch/report-prior-attempts.md. It is superseded only in its assertion that no concrete split was prepared: this attempt recovered the exact NY source copy and prepared the candidate above. The live-node absence itself has not been hidden.

## Required dry run result

Ran exactly one active invocation of `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q09 lem-fix-scalar-completion-associator --no-push` in this attempt. Polled that same tool session until it exited 1. After admission to server preflight slot 0, it printed:

```
PREFLIGHT FAILED, nothing pushed. Repair in the sandbox and run this command again:
preflight FAILED, 1 reason(s); do not push:
 1. the item lem-fix-scalar-completion-associator does not exist on 2d40f98364c86b5c94f452dfefa775caf4e00c90 (a delivery splits an existing node)
```

This confirms the concrete prerequisite, beyond the former empty-sandbox error: even with the exact recovered item, its seven-step candidate split, the one generic child, citation evidence and report prepared, the delivery cannot introduce its own assigned item. The node must be landed/restored on the meeting-point DAG, normally by landing the originating NY delivery, before Q09 can deliver the split. I did not change creation provenance, patch a gate, edit the live repository/launcher, or try pushing after this failure. No delivery invocation remains active. The candidate is retained for retry after the missing base node is landed; the server did not certify its downstream DAG/review checks in this failed preflight.


## Retry on 2026-10-21

Retained the existing item, child node, seven-step proof, citations and all 13 logged searches without alteration. Re-read the standing stage-1 brief, stage document, worker role, GOAL.md, the three-level route rules in SETUP.md, and delivery-errors B–E. The shared read clone still has no item file: an exact filename search under dag/nodes returned no match. A current search under lean/WeilConjectures for the item id and scalar-completion/associator notions returned no attachment candidate.

As required for a resumed candidate, ran the dry run before making any changes to the split:

```
python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q09 lem-fix-scalar-completion-associator --no-push
```

This was the only delivery invocation of this retry; polled its same session until exit 1. It was admitted to server preflight slot 0, then returned:

```
PREFLIGHT FAILED, nothing pushed. Repair in the sandbox and run this command again:
preflight FAILED, 1 reason(s); do not push:
 1. the item lem-fix-scalar-completion-associator does not exist on 7ffa57a7871172d4200a9e2197b5032c1124007d (a delivery splits an existing node)
```

The blocker persists on the newer server base. It cannot be repaired in this worker's sandbox: the assigned item must first be landed or restored in the base DAG by the maintainer. No downstream DAG/review pass is claimed from this failed preflight. No push was attempted, and no delivery process remains active. The candidate and earlier evidence remain available unchanged for a retry once the originating item exists. No repository, launcher or Lean source was written, no compiler/build was run, and no agent was started.


## Dispatcher retry — 2026-10-21T05:49:12+00:00

The retained item and report were present, so I ran the required dry run before changing either node. Re-read the worker contract, GOAL.md, stage-1 rules, SETUP.md's three-level route requirements, and delivery-errors B–E. Exact filename search of the current shared dag/nodes still found no lem-fix-scalar-completion-associator item; exact-id and scalar/completion/associator notion searches of lean/WeilConjectures found no attachment candidate.

Ran only one delivery invocation:

```
python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q09 lem-fix-scalar-completion-associator --no-push
```

Polled its same process until exit 1. It was admitted to server preflight slot 2, then printed:

```
PREFLIGHT FAILED, nothing pushed. Repair in the sandbox and run this command again:
preflight FAILED, 1 reason(s); do not push:
 1. the item lem-fix-scalar-completion-associator does not exist on 7ffa57a7871172d4200a9e2197b5032c1124007d (a delivery splits an existing node)
```

The blocker is unchanged: the maintainer must land or restore the assigned item in the server base DAG. This prerequisite cannot be repaired within the authorized Q09 sandbox. No downstream check success is claimed, no push was attempted, and the dry-run process has exited. The retained nodes, proof, citations, prior report text and logged searches were left unchanged. Only this report entry was appended. No repository, launcher or Lean source was written; no direct git, compiler, Lake or build command was run; no agents were started.


## Retry 2026-10-21T05:50:44+00:00

The retained item and report were present, so the first action after reading the worker rules was the required dry run:

```
python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q09 lem-fix-scalar-completion-associator --no-push
```

Kept that single invocation active and polled the same session (92705) until exit 1. Server preflight admitted it in slot 0 and returned:

```
PREFLIGHT FAILED, nothing pushed. Repair in the sandbox and run this command again:
preflight FAILED, 1 reason(s); do not push:
 1. the item lem-fix-scalar-completion-associator does not exist on 7ffa57a7871172d4200a9e2197b5032c1124007d (a delivery splits an existing node)
```

Confirmed with a current filename search of shared dag/nodes that the assigned item is still absent. Exact-id and scalar/completion/associator notion searches under lean/WeilConjectures returned no attachment candidate. Re-read GOAL.md, the worker role, stage-1 instructions, SETUP.md's three-level route and generic-tool requirements, and delivery-errors B–E. The gate's existing-item prerequisite cannot be repaired in the authorized sandbox: the maintainer must land or restore the assigned item in the server base DAG. No tool workaround or push was attempted. The retained node files, seven-step proof, citations, report history and logged searches remain unchanged; only this retry entry was appended. No additional mathematical verification or downstream check success is claimed. No repository, launcher or Lean file was written; no direct git, compiler, Lake or build command was run; no agents were started.


## Dispatcher retry — 2026-10-21T05:56:19+00:00

Retained the existing item, child node, proof, citations, report history and all 13 logged searches. Read the stage-1 brief and rules, GOAL.md, worker role, SETUP.md's three blueprint levels and delivery-errors B–E. The assigned item remains absent from the shared dag/nodes filename search; exact-id and scalar/completion/associator searches under lean/WeilConjectures produced no declaration stating the item.

Because both the item and report were already present, ran the required dry run before editing the retained split:

```
python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q09 lem-fix-scalar-completion-associator --no-push
```

Kept this single invocation active and polled the same tool session (99235) until exit 1. Server preflight admitted it in slot 1 and printed:

```
PREFLIGHT FAILED, nothing pushed. Repair in the sandbox and run this command again:
preflight FAILED, 1 reason(s); do not push:
 1. the item lem-fix-scalar-completion-associator does not exist on ae5a9662b01b11fdcf241597ae385d98d2a84ad0 (a delivery splits an existing node)
```

The server's existing-item prerequisite still prevents delivery. The maintainer must land or restore the assigned node in the base DAG; a worker cannot repair this within the authorized sandbox. No downstream check success is claimed. No push or workaround was attempted, and the dry-run process has exited. Only this report entry was appended; the existing mathematical work and search evidence remain unchanged. No repository, launcher or Lean file was written, no direct git or compiler/build command was run, and no agents were started.


## Resume dry run — 2026-10-21, base cc9c0f6f

Retained the existing split, child node, citations, report history and logged searches. Read the required stage-1 instructions, GOAL.md and delivery-errors B–E. Confirmed that the item file is still absent from the current shared DAG. A fresh exact-id and scalar/completion/associator search under lean/WeilConjectures did not find an exact attachment.

As required for an existing item and report, started with a single invocation of `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q09 lem-fix-scalar-completion-associator --no-push`, then polled that same process (session 61402) until it exited with code 1. Server preflight admitted it in slot 2 and returned:

```
PREFLIGHT FAILED, nothing pushed. Repair in the sandbox and run this command again:
preflight FAILED, 1 reason(s); do not push:
 1. the item lem-fix-scalar-completion-associator does not exist on cc9c0f6fc42325e9acc8f9d18d91d6659cbbd8f3 (a delivery splits an existing node)
```

This is an existing-item prerequisite outside the sandbox's repair scope: the maintainer must land or restore the assigned node in the base DAG. No successful downstream check or delivery is claimed. No push or workaround was attempted. The mathematical files and search evidence remain unchanged; only this report entry was appended. No repository, launcher or Lean file was written, no direct git or compiler/build command was run, and no agents were started.


## Resume dry run — 2026-10-21T06:00:40.460968+00:00, base 8e6fa122

The item and report were already present, so I retained the earlier split, child node, citations and logged searches and ran the required dry run before editing the mathematical work:

```
python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q09 lem-fix-scalar-completion-associator --no-push .
```

Kept this single invocation active and polled its same session (36298) until exit 1. Server preflight admitted it in slot 1 and returned:

```
PREFLIGHT FAILED, nothing pushed. Repair in the sandbox and run this command again:
preflight FAILED, 1 reason(s); do not push:
 1. the item lem-fix-scalar-completion-associator does not exist on 8e6fa1227992c174348e877de523952273079eaf (a delivery splits an existing node)
```

Read the standing stage-1 brief, stage document, worker role, GOAL.md, SETUP.md's three-level route rules and delivery-errors B–E. Confirmed by an exact filename search that the assigned item remains absent from the shared DAG. An exact-id and scalar/completion/associator search under lean/WeilConjectures returned no attachment candidate. The retained item's creation provenance identifies it as a child of lem-fix-operation-reduction created by NY; no provenance or mathematical file was changed.

This is the same missing-base-node prerequisite as the previous attempt, now on the newer server base. The maintainer must land or restore the item before Q09 can split it by delivery. This cannot be repaired inside the worker's authorized sandbox, and I did not patch or bypass the tool. No downstream DAG/review success is claimed, no push was attempted, and the dry-run process has exited. Only this report entry was appended; the previous work remains intact. No repository, launcher or Lean file was written; no direct git, compiler, Lake or build command was run; no agents were started.


## Required resume dry run — 2026-10-21T06:02:12.190460+00:00

Preserved the existing split, new node, citations, report and searches. As required when the item and report already exist, ran `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q09 lem-fix-scalar-completion-associator --no-push` before changing any mathematical work. Kept that invocation as the only active delivery and polled session 28686 until it exited with code 1. Server preflight admitted it in slot 1 and returned:

```
PREFLIGHT FAILED, nothing pushed. Repair in the sandbox and run this command again:
preflight FAILED, 1 reason(s); do not push:
 1. the item lem-fix-scalar-completion-associator does not exist on 8e6fa1227992c174348e877de523952273079eaf (a delivery splits an existing node)
```

The current shared DAG filename search confirms that the assigned item is absent. An exact-id and scalar-completion-associator-name search of lean/WeilConjectures found no attachment candidate. Read the required stage-1 brief, stage document, GOAL.md, worker role, SETUP.md's blueprint levels, and delivery-errors B–E. The failure concerns the server base, not a repairable sandbox field: the maintainer must land or restore the assigned node before this delivery can pass. No downstream check success or full renewed mathematical review is claimed. No push was attempted; no tool was patched or bypassed. Only this report entry was appended; all earlier mathematical files and search evidence remain unchanged. No repository, launcher or Lean file was written; no direct git, compiler, Lake or build command was run; no agents were started.


## Required resume dry run — 2026-10-21T06:03:39.911162+00:00

The preserved item and report were present, so I ran the required dry run before changing mathematical work:

```
python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q09 lem-fix-scalar-completion-associator --no-push
```

Kept this as the only active delivery invocation and polled session 65712 until exit 1. Server preflight admitted it in slot 0 and returned:

```
PREFLIGHT FAILED, nothing pushed. Repair in the sandbox and run this command again:
preflight FAILED, 1 reason(s); do not push:
 1. the item lem-fix-scalar-completion-associator does not exist on 317159bb9f22bf3de43dfc31ee21011db020e67b (a delivery splits an existing node)
```

Read the required stage-1 brief, stage document, worker role, GOAL.md, SETUP.md's three-level route requirements and delivery-errors B–E. An exact filename search of shared dag/nodes confirms that the item is absent; exact-id and scalar-completion/associator notion searches under lean/WeilConjectures found no attachment candidate. The assigned node must first be landed or restored in the server base DAG by the maintainer. This existing-item prerequisite cannot be repaired within the authorized sandbox. No downstream DAG/review success or renewed full mathematical review is claimed. No push or tool workaround was attempted. The retained item, child, proof, citations and search evidence remain unchanged; only this report entry was appended. No repository, launcher or Lean source was written, no direct git, compiler, Lake or build command was run, and no agents were started. The dry-run process has exited.


## Required resume dry run — 2026-10-21T06:05:59.691313+00:00

Preserved the existing item, child node, proof, citations, report history and logged searches. Since the item and report were already present, ran the required dry run before changing mathematical work:

```
python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q09 lem-fix-scalar-completion-associator --no-push .
```

Kept this as the only active delivery invocation and polled its same session (99668) until exit 1. Server preflight admitted it in slot 0 and returned:

```
PREFLIGHT FAILED, nothing pushed. Repair in the sandbox and run this command again:
preflight FAILED, 1 reason(s); do not push:
 1. the item lem-fix-scalar-completion-associator does not exist on 317159bb9f22bf3de43dfc31ee21011db020e67b (a delivery splits an existing node)
```

The current shared DAG filename search confirms that the assigned item is absent. Exact-id and scalar/completion/associator notion searches under lean/WeilConjectures found only unrelated completion references, no declaration stating the assigned item. Consulted the standing stage-1 brief, worker role, stage document, GOAL.md, SETUP.md's three-level route requirements and delivery-errors B–E.

This server-base prerequisite cannot be repaired within the authorized sandbox. The maintainer must land or restore the assigned item before Q09 can deliver its split. No downstream DAG/review success or renewed full mathematical review is claimed. No push or tool workaround was attempted. The dry-run process has exited. Only this report entry was appended; all mathematical work and search evidence remain unchanged. No repository, launcher or Lean source was written; no direct git, compiler, Lake or build command was run; no agents were started.


## Resumption review by Q09, 2026-10-21

Started with the required dry run of the retained item and report, kept its sole process active and polled session 25463 to exit 0. The server printed `OK (not pushed) deliver/Q09/lem-fix-scalar-completion-associator at ddb336a2403: preflight passed`. The previous missing-base-item failure is resolved.

Reopened the live item, its chapter and unit, and paragraph 3 of the current blueprint operation-reduction proof. The live item's statement and source are unchanged from the retained split. Reopened all fourteen proof-dependency statements (the child from the sandbox), the strict Roos coordinate definition and the inverse-system definition. Checked all twenty step/citation pairs against the current statements: every listed quote remains verbatim, every used node has a quote, and the proof-dependency list is unchanged. Step lengths are 963, 900, 651, 707, 492, 1237 and 1021 characters, so no long step requires a hidden-lemma extraction.

For step 1 the current finite-free comparison, DVR and absolute-value statements still supply the same finite-free rings and positive exponents; completed-constant flatness supplies regularity and the correct sheaf quotients, and the pro-etale product statement applies also to the integer constant sheaf to supply exact products of abelian sheaves. For step 2 I checked flat-term K-flat change of rings, the balanced inverse formulas, the literal rho coefficient maps, and descent of the zero shifted-coordinate quotient unit. Steps 3-5 use exactly the exchange unit equation and naturality: the constructed d has target J, D_M(d) has target D_M J, and the inverse of eta_J returns it to J. Completeness of J follows because chi identifies it with the complete ordinary scalar extension C_ba K. Thus there is no unidentified chain inverse in the construction. In step 6 the two arbitrary cofinal restrictions compare through the full tower, even for disjoint subsequences. In step 7 cancellation uses only invertible chi maps on complete inputs, with ordinary scalar coherence supplied by the current successive-derived-quotient statement.

Reopened Stacks 0941 (sites-cohomology.tex, lemma-derived-limit-is-ok), 099B (algebraization.tex, lemma-derived-completion) and 0A0E (lemma-derived-completion-koszul), including their proofs. The arbitrary-subsequence block formula is still an explicitly agent-formulated refinement, not attributed verbatim to Stacks. Checked the finite prefix and variable finite-block elimination argument again: every output involves finitely many transitions; block-sum composition and the zero shifted augmentation follow by the written telescoping formulas. This includes deletion of a prefix and n-squared reindexing.

Repeated current DAG/blueprint and project-source searches for duplicate or completed declarations, while reusing all fourteen logged Mathlib searches after reading their recorded hits. The blueprint search for cofinal subsequence had no matches; the Roos search returned general derived-limit and completion nodes, not the specified arbitrary-subsequence map. Read the current arithmetic comparison, its cochain-model child, the constant-ring finite-free cofinality statement and the varying-ring derived-subsequence statement. They still do not state the new arbitrary-subsequence strict cone comparison. Project searches found neither item's blueprint tag nor a declaration giving all its clauses. No attachment or Mathlib leaf is claimed.

The mathematical split, child statement, citations and search log are retained unchanged. This resumption updates the report's obsolete missing-item diagnosis and the item's split-report summary; the prior proof and provenance remain intact.
