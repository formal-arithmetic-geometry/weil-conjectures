# Worker report: lem-sfb-evaluation-duality-completion

1. Files written:
   - dag/nodes/sec-six-functors-basics/lem-sfb-evaluation-duality-completion.json: statement, now split into seven argument steps; existing statement, creation record, blueprint ancestor and prior Q53 searches retained.
   - dag/nodes/sec-six-functors-basics/lem-sfb-kflat-augmented-roos-comparison.json: statement-only, unsplit; no Mathlib match. This is the resolution-normalized comparison for tensoring an arbitrary strict augmented tower, conditional on the relevant derived-product comparison being invertible.
   - citations.json: a verbatim statement quotation for every step/node citation.
2. Attachments: none. Searching WeilConjectures for the item tag and for coevaluation, ExactPairing, dualizability, products and completion found finite projective module pairings and specialized pro-etale results, not a finished declaration of this arbitrary ringed-site statement. The useful project homotopy-limit theorem is already attached to lem-pc-homotopy-limit-map.
3. WANTED: none. The blueprint and the needed Stacks source are available locally.
4. Defects corrected: the item was a statement-only child of Q53's split. The blueprint suppresses both triangle calculations, and a bare triangulated cone argument does not fix a natural completion comparison or its augmentation. Those are now explicit. The scheme-only lem-pc-dualizable-evaluation-criterion does not cover arbitrary ringed sites; its second-triangle child also has a non-self-contained statement, so neither is used here. No statement dispute or correction of the item's statement was necessary.
5. Unfinished: no stage-1 work on the item; the new comparison lemma is intentionally left statement-only for the next level. No Lean was written or compiled, and no repository or launcher file was changed.

## Sources and route

I read the current chapter sec-six-functors-basics and unit sk-lem-int-tensor, especially its third paragraph, together with the first paragraph of main-20261015/sk-lem-int-tensor/det-lem-int-tensor-product.proof.md. The proof stays on its dualizability -> both adjoints -> products and derived limits -> completeness route. This is not the unit's key statement, so no unit binding is changed. I read Stacks sites-cohomology.tex, Tag 0FPU (example-dual-derived), which constructs the same evaluation and coevaluation and explicitly omits the two triangle verifications. I filled those omissions with the currying/interchange calculations below. For the new node I read Tag 0941 (lemma-derived-limit-is-ok), whose K-injective tower proof uses derived products, and Tag 06YM (lemma-derived-tor-exact), with 06YS (lemma-K-flat-resolution) for the representatives used by the item. The new augmented tensor refinement is agent-formulated, not claimed to be the literal statement of 0941.

## Review by Q70

I checked the seven steps against the cited node statements, not their proofs. Step 1 uses the evaluation-normalized right-tensor/derived-Hom adjunction of lem-sf-ringed-derived-tensor-hom-adjunction: its source categories are arbitrary small ringed sites at compatible module universes, exactly as in the item. Transposing the defining equation u_M c = transpose(id_M) gives the first triangle, so no perfection hypothesis is being imported. Step 2 uses the same adjunction's injectivity with target R. Interchange says the two orders of contracting D tensor M tensor D tensor M equal e tensor e; after the first triangle this gives e(h tensor id_M)=e, whose transpose is h=id_D. Thus both identities concern the specified c and e, not merely existence of some duality.

Step 3 uses the statement of the existing Mathlib leaf lem-sfb-dual-tensor-adjunctions. Its orientation is T_D left adjoint to T_M and U_M left adjoint to U_D. The fixed symmetry identifies right and left tensor functors, giving the other required adjunction. Its right-adjoint preservation clause really includes every existing small product. I read Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean:459,468, the two adjunction declarations; no exact-pairing-existence result is being inferred from those declarations.

Step 4 uses lem-pc-kflat-resolution for a flat-term K-flat representative; lem-weil-pbc-kflat-fixed-tensor-triangulated explicitly gives additive exact descent and the connecting map without a boundedness assumption. The closed project theorem lem-pc-homotopy-limit-map states precisely preservation of homotopy-limit cones under an additive triangulated functor preserving tower products. I read the corresponding IsHomotopyLimit.map proof at HomotopyLimit.lean:255. I checked countable products here are derived products, not products assumed exact in Mod(R).

Step 5 uses lem-pe-kflat-scalar-tower-realization for both displayed equations, the derived unit and the transition comparison, on the same K-flat representative P. Its statement explicitly permits nonsurjective and nonflat R-algebra maps. The new node supplies the canonical whole-fibre map with a specified sign on the second coordinate. Product preservation from step 3 makes its derived-product comparison invertible. The citation for the new node is its actual augmentation equation. Step 6 proves associator compatibility on the strict augmentation and each transition by the two written tensor formulas; it uses the same new-node augmentation equation after that tower identification. I added the direct K-flatness check for A tensor P to avoid an unspoken closure claim, citing its definition, and cited lem-sf-ringed-derived-native-tensor for the one-K-flat localization comparison and its preservation of associators. That node's statement explicitly says the native comparisons preserve associators and unitors. Step 7 is only composition of inverses and substitution of the resulting actual unit equation.

For B1-B9, the new node introduces the site, ring, complex, tower, resolutions, product maps and augmentation. It has no proof, proof dependencies or proof sketch in its statement: its coordinate formula is the normalization asserted of the map, not an argument. It retains its mathematical claim under arbitrary small ringed sites and unbounded complexes; it never assumes countable products of sheaves exact. All its notions have cited definition nodes or inline definitions. The source tags are verified in the local tags table. Its blueprint from.node is det-lem-int-tensor-product, via the current item; all-chapter blueprint searches for evaluation, homotopy limit, dualizability, augmented, K-flat, Roos, tensor Roos and product-preserving gave no equivalent general augmented K-flat comparison. The whole DAG and project Lean source were searched before writing it. The closest same-tag statements are distinguished below. Every Mathlib search was run through msearch.py and its returned hits read; there were no service failures. The second phrasing found Mathlib's additive-coefficient-functor mappingCone.mapHomologicalComplexIso (MappingCone.lean:639), whose source I read. That does not handle the total tensor by an unbounded complex or resolution-normalized derived products. No near hit was labelled absent without inspection.

Small cases: M=0 gives D=0 and c=e=0 with both identities equal to the zero object's identity; M=R reduces to unitors, and a shift of R requires the usual signed symmetry, retained by the fixed derived structure. In the new node, A=0 gives the zero comparison, A=R[0] gives the identity, and A=R[1] gives a minus sign on the shifted-product coordinate; I checked that omitting (-1)^p would fail the chain-map equation. A constant tower with identity transitions gives the expected constant-family augmentation; a tower with all transitions zero has 1-s=1 and acyclic fibre. Nonexact sheaf products cause no problem because products are computed from the K-injective I_n,J_n. The quotient cases pi=0 and pi a unit reduce respectively to the identity tower and the zero tower; no nonexistent nonzerodivisor hypothesis is used. The preservation assertion is about the canonical augmentation being invertible, not a claim that every quotient tower is a particular intrinsic completion without additional coefficient hypotheses.

I checked C1-C4 specifically at the two dangerous points: exactness is a theorem citation, not the definition of K-flatness, and compatibility with the map into a homotopy limit is the new node's whole augmented comparison, not a claim that equality after projections detects equality. I checked that no new node restates evaluation duality, either adjunction, or completeness preservation. The new lemma has a K-flat complex and arbitrary strict tower as inputs and assumes only the relevant product comparison; it asserts neither dualizability nor completeness. Every item step is under 2000 characters. All new arguments occur in the steps or in this report, and the new node remains statement-only.

## Argument retained for the new statement-only node

Choose X -> I and A tensor I -> J as in the statement. The b map is an actual chain map defined by all product projections; because the q_n form one strict tower map it satisfies b(1 tensor s_I)=s_J b. For homogeneous a in A^p, expand the two differentials on (a tensor x, a tensor y). The first coordinate is d_A a tensor x + (-1)^p a tensor d_I x on both sides. In the second coordinate the A-differential changes (-1)^p to (-1)^(p+1), while the shifted I-differential contributes a minus; these are exactly the two terms of -d_J((-1)^p b(a tensor y)). The remaining term is b(a tensor (1-s_I)x)=(1-s_J)b(a tensor x). This proves the displayed whole-fibre map is a chain map, with the signed shift comparison rather than an arbitrary filler.

Each I_n,J_n is K-injective. Thus their termwise products compute the products in D(R), as in the proof of 0941; the localized b is precisely the derived product comparison after the quasi-isomorphisms q_n are inverted. K-flatness makes A tensor - invert all comparison quasi-isomorphisms. Tensor exactness from 06YM identifies the source with the fibre of T_A(1-s_I). Consequently, if the product comparison is invertible, both product entries in the fibre comparison are invertible and so is the fibre comparison. For a strict augmentation gamma the source has coordinates (gamma,0), and the map above carries it to (q(A tensor gamma),0), which is the target augmentation including its zero shifted coordinate.

Independence and naturality use the whole tower resolutions: a map between input towers extends, up to tower cochain homotopy, to a map between their K-injective resolutions. The same extension applies after A tensor - and into J. Products send tower homotopies to product homotopies, and the signed cone construction sends such homotopies to cone homotopies. Therefore the two induced maps coincide in the derived category. Comparisons between two resolutions yield inverse maps by the same argument applied to their identity comparison; composition and quasi-isomorphism compatibility follow. This is not a uniqueness argument using only the level projections of an arbitrary triangulated cone. The statement's explicit normalized comparison is the resolution-derived map.

## Not duplicates

lem-sfb-kflat-augmented-roos-comparison vs def-pc-tensor-complex-sheaves: defines the signed total tensor; it asserts no comparison with a derived tower limit.

lem-sfb-kflat-augmented-roos-comparison vs lem-weil-pbc-total-tensor-homotopy-cone-signs: gives ordinary homotopy and cone signs and K-flat quasi-isomorphism preservation, not independence of a derived-product Roos comparison or its augmented limit map.

lem-sfb-kflat-augmented-roos-comparison vs lem-pur-integral-tensor-transition-compatibility: compares consecutive finite scalar-reduction transitions, not a tensor functor applied to a derived product or its fibre.

lem-sfb-kflat-augmented-roos-comparison vs def-sp-total-tensor-summand-interface: defines summand inclusions for the total tensor, without any inverse-limit assertion.

lem-sfb-kflat-augmented-roos-comparison vs def-sf-ringed-kflat-tensor-representative-data: names resolving tensor models, with no product, Roos or augmentation comparison theorem.

lem-sfb-kflat-augmented-roos-comparison vs lem-pur-integral-tensor-reduction-tower-comparison: identifies two finite coefficient-reduction tensor towers, without comparing tensor of the derived limit to the limit of tensors.

lem-sfb-kflat-augmented-roos-comparison vs lem-pe-kflat-roos-representative-invariance: requires exact countable sheaf products and proves invariance of scalar-extension completion under representative changes; it does not construct tensor/derived-limit comparison for arbitrary strict towers.

lem-sfb-kflat-augmented-roos-comparison vs lem-sfb-ringed-finite-free-resolution-tensor: computes tensor from a specified bounded-above finite free resolution and a degree-zero sheaf, with no inverse-limit or augmentation assertion.

lem-sfb-kflat-augmented-roos-comparison vs lem-sbc-koszul-tensor-derived-tower: identifies a Koszul tensor tower termwise with its derived version, not tensor of its limit with limit of its tensors.

lem-sfb-kflat-augmented-roos-comparison vs lem-sbc-scalar-extension-counit-properties: gives exactness and K-flat computation for a derived scalar-extension counit, without a derived-product or augmented Roos comparison.

lem-sfb-kflat-augmented-roos-comparison vs lem-sf-cochain-tensor-model-rigidity: identifies tensor bifunctor models by localization uniqueness, with no inverse-limit comparison.

lem-sfb-kflat-augmented-roos-comparison vs lem-exc-intrinsic-resolution-tensor-homology: compares intrinsic and fixed-scalar tensor cohomology on a scheme, with no tower, product or derived-limit comparison.

lem-sfb-kflat-augmented-roos-comparison vs lem-sfb-dual-tensor-adjunctions: is the already reused exact-pairing adjunction/preservation leaf; it does not specify a map of augmented derived Roos fibres.

lem-sfb-kflat-augmented-roos-comparison vs lem-pc-dualizable-evaluation-criterion: is restricted to the scheme structure sheaf and concerns the triangle identities; the new node assumes a K-flat complex and product comparison, and concerns arbitrary augmented strict towers.

lem-sfb-kflat-augmented-roos-comparison vs lem-cbc-exact-functor-rlim: only asserts object and triangle comparison for an exact triangulated functor and explicitly disclaims a canonical filler; the new node supplies a resolution-normalized natural morphism and augmentation equality.

lem-sfb-kflat-augmented-roos-comparison vs lem-cbc-exact-product-functor-roos-compatibility: requires an exact coefficient-sheaf functor, exact sheaf products and a supplied normalized comparison; the new node treats total tensor by an unbounded K-flat complex using derived products and constructs the comparison.

lem-sfb-kflat-augmented-roos-comparison vs lem-pur-roos-additive-comparison: is termwise application of an additive coefficient functor preserving ordinary products, not unbounded total tensor with derived products.

lem-sfb-kflat-augmented-roos-comparison vs lem-sf-roos-adjunction-unit-coherence: assumes exact adjoint functors on sheaves and exact sheaf products; its unit calculation does not construct a K-flat tensor comparison.

lem-sfb-kflat-augmented-roos-comparison vs lem-sf-perfect-tensor-roos-completion: concerns bounded projective modules over one complete DVR and their quotient tower, not arbitrary ringed sites and arbitrary augmented towers.

lem-sfb-kflat-augmented-roos-comparison vs lem-pur-flat-roos-functor-descent: requires exact sheaf products and descends an already specified tower functor; it does not prove tensor commutes with derived Roos fibres.

lem-sfb-kflat-augmented-roos-comparison vs lem-weil-pbc-ringed-strict-tower-homotopy-limit: constructs the normalized derived-limit functor and Roos triangle, but does not compare this functor with tensoring a fixed complex.

lem-sfb-kflat-augmented-roos-comparison vs lem-fix-bounded-projective-tensor-complete: proves completeness of bounded projective sheaf complexes for one integral quotient tower; it gives no comparison for arbitrary strict towers.

lem-sfb-kflat-augmented-roos-comparison vs lem-sf-sequence-tensor-augmentation-unit: identifies the quotient augmentation with a particular reduction/limit adjunction unit; it does not construct the tensor/limit comparison.

lem-sfb-kflat-augmented-roos-comparison vs def-a1-integral-completed-tower-pullback-universes: defines universal derived reduction and ordinary pullback on integral pro-etale towers; it does not construct tensoring a fixed K-flat complex through derived inverse limit.

lem-sfb-kflat-augmented-roos-comparison vs lem-a1-principal-koszul-strict-replacement: gives an objectwise K-flat replacement of a principal quotient tower; it does not compare tensor of a derived limit to the limit of tensors.

lem-sfb-kflat-augmented-roos-comparison vs lem-per-proetale-scalar-slice-comparison: compares scalar extension with literal slice restriction; it asserts no inverse-limit comparison.

lem-sfb-kflat-augmented-roos-comparison vs def-pc-derived-tensor-cohomology-vanishes: defines one-degree tensor-cohomology vanishing on a scheme, with a module as second factor; it has no tower or limit assertion.

lem-sfb-kflat-augmented-roos-comparison vs def-pc-derived-tensor-complex-cohomology-vanishes: defines one-degree tensor-cohomology vanishing for two derived scheme objects; it has no tower, product or limit assertion.

lem-sfb-kflat-augmented-roos-comparison vs def-pc-kflat-complex: defines acyclicity, K-flatness and a resolution; it supplies no normalized augmented derived Roos comparison.

## Validation

The first dry run identified six additional shared-source-tag pairs; their statements were opened and the distinctions added above. The repaired dry run completed with exit 0: server preflight passed at c330256c14e (not pushed). It includes tools/check_dag.py and tools/review_split.py; no compiler or local check script was run. This final report update is included in the final dry run before direct delivery.
