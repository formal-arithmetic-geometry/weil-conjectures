# Stage-1 delivery: lem-sfb-ringed-hypercohomology-edge-tensor

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-hypercohomology-edge-tensor.json: item, statement, split with five steps; not a Mathlib leaf.
- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-derived-naive-cup-comparison.json: new statement-only node, unsplit, no Mathlib match. General ringed-topos derived/naive cup diagram, Stacks 0FPK.
- citations.json: verbatim statements for every step/node citation.
- searches.jsonl: searches recorded by the prescribed msearch command. Existing searches in the live item have been preserved.

## Attachments

None. Searched WeilConjectures/ for the exact blueprint tag and the notions hypercohomology, edge/tensor and naive/derived cup compatibility. Existing module cup declarations concern schemes, not arbitrary ringed sites. Existing hypercohomology-left-edge declarations concern bounded-below abstract complexes and do not state the tensor assertion. No exact finished declaration covers this item.

## WANTED

None. All mathematical source material needed is in literature/stacks-project/.

## Audit findings and corrections

The live item was unsplit with an empty proof, and no repair note exists. No prior sandbox split or report existed. Its statement is retained verbatim: all integer edges, naturality for every derived morphism, the tensor identity for nonnegative a,b, arbitrary unbounded complexes, and no final object/flatness/quasi-coherence hypotheses. No statement dispute was found.

The important potential gap is that a K-flat resolution need not be surjective on global cocycles. Step 3 does not choose an arbitrary resolution and claim a lift. It factors the actual map O[-a] to a K-injective representative through a flat-term K-flat complex by the existing lem-pur-kflat-map-factorization (0G7D). The homotopy gives the exact global boundary difference. The same argument applies to y. Another potential gap is that Gamma(P) need not be K-flat over A. Step 4 uses the existing shifted-free-unit tensor lemma to calculate the canonical derived-to-ordinary map on the two specific cycles instead.

The one new node is the whole derived/naive cup diagram of 0FPK, in derived form, for arbitrary ringed-topos morphisms. It has no edge map, no e-identity, and no proof sketch. The edge construction, independence, adapted representatives and final equality remain in the item's proof. No elementary fact was made a node.

Ancestry: tools/blueprint_refs.py ancestor reports null on the live item; this is inherited through its long existing alteration/Picard ancestry. Preserved it, appended the item's id to the new node's via chain, and named the exact auxiliary input in from.place. Whole-blueprint searches for cup compatibility, naive cup, 0FPK, tensor cocycles, and the edge-tensor assertion found no blueprint duplicate. Read the current latest blueprint unit sk-thm-sf-ctf-stability as well as the recorded unit and chapter; this is infrastructure below the direct-image/relative cup route, not a replacement for it. No unit realization fields are changed because this is not its key node.

## Not duplicates

lem-sfb-ringed-derived-naive-cup-comparison vs lem-sfb-ringed-hypercohomology-edge-tensor: the new statement is a derived-category comparison between arbitrary cochain pushforwards, without any edge or cohomology identity; the item uses it after constructing adapted cocycle representatives to prove its edge identity.
lem-sfb-ringed-derived-naive-cup-comparison vs lem-sfb-space-affine-relative-cup-sections: the latter compares coherent relative cup sections on algebraic spaces over an affine base, while the new node is a generic unbounded derived/naive tensor comparison on arbitrary ringed topoi, without affine geometry or coherent coefficients.
lem-sfb-ringed-derived-naive-cup-comparison vs lem-sc-module-cup-naive-derived-compatibility: the existing node is restricted to a scheme X and its global-sections functor, and asserts existence of a family; the new node covers every morphism of ringed topoi and identifies the canonical adjunction-defined cup product of def-sfb-ringed-site-module-cup-product. The existing scheme result cannot specialize to an arbitrary ringed site.
lem-sfb-ringed-derived-naive-cup-comparison vs lem-sc-module-cup-kinjective-target: the existing node is again scheme global sections and requires a chosen chain pairing into a K-injective target; the new diagram is for an arbitrary ringed-topos morphism and the canonical derived/ordinary tensor comparison.
lem-sfb-ringed-derived-naive-cup-comparison vs lem-sc-module-cup-adjunction-polygon: that existing conditional scheme statement assumes additional comparison polygons and normalization data; the new node is the unconditional ringed-topos assertion of 0FPK.

lem-sfb-ringed-derived-naive-cup-comparison vs def-wf-finite-coefficient-cup: this definition constructs a particular finite-coefficient etale cup using Yoneda Ext and coefficient forgetting; it does not give a derived/naive comparison for arbitrary complexes and ringed-topos morphisms.
lem-sfb-ringed-derived-naive-cup-comparison vs def-wf-finite-etale-cup: this defines a predicate on finite-coefficient etale cohomology pairings, not a theorem comparing derived and ordinary tensor on arbitrary ringed topoi.
lem-sfb-ringed-derived-naive-cup-comparison vs def-wf-ordinary-etale-cup: this defines the ordinary integral etale cup through shifted unit morphisms and scalar forgetting; it does not state the derived/naive cochain square for arbitrary ring sheaves and arbitrary direct images.
lem-sfb-ringed-derived-naive-cup-comparison vs lem-wf-curve-trace-cup-naturality: the existing statement concerns the trace pairing on smooth proper curves and its coefficient-reduction and isomorphism invariance, not the unbounded cochain comparison diagram.
lem-sfb-ringed-derived-naive-cup-comparison vs lem-wf-etale-cup-functoriality: the existing theorem is pullback functoriality of ordinary etale sheaf-cohomology cup products with coefficient maps; the new statement compares derived direct-image tensor with the naive cochain map before taking any cohomology.

## Review by Q113

I read Stacks sites-cohomology.tex lemma-sheafification-cohomology (0BKV), including its actual kernel/quotient proof, lemma-factor-through-K-flat (0G7D), including the flat-term clause and its homotopy-triangle proof, and section-cup-product (0FPJ) and the full lemma-cup-compatible-with-naive (0FPK) diagram and proof. The first dry run identified five additional shared-tag 0FPJ records; I opened all five full statements and added their individual distinctions under Not duplicates. None states a derived/naive cochain comparison. For the new node I checked that both composites have source [f_*M] tensor-derived [f_*N] and target Rf_*[Tot(M tensor N)], with the right vertical arrow being Rf_*(rho), not its inverse. Its beta is the canonical derived comparison. The global-sections case uses the point topos (Sh(pt),Gamma O), which exists even when C has no final object. Read the current definition of the cup morphism (the mate of the tensor counits); its normalization is exactly the one in 0FPK, not an arbitrary pairing.

For step 1 I opened def-weil-derived-cohomology-sheaves: it gives ker(d)/im(d) and the class map for a derived morphism. The proof explicitly descends the global cycle family and calculates the chain-map/homotopy equations. No presheaf hypercohomology sheafification theorem is being substituted for a stronger unbounded module statement.

For step 2 I opened prop-pur-kinjective-resolutions-exist, def-pur-ringed-site-zeroth-hypercohomology, and lem-weil-pbc-kinjective-hom-derived. The first provides resolutions on every small ringed site; the second defines the whole RΓ by termwise K-injectives (its H^0 designation does not restrict which cohomology of that complex can be taken); the third gives all derived maps into a K-injective as homotopy classes and makes quasi-isomorphisms between these models homotopy equivalences. Thus the independence/naturality conclusion is justified for arbitrary morphisms and unbounded objects. The beta equation is a direct calculation with the resolution chain map, not an assumed comparison theorem.

For step 3 I opened def-pc-kflat-complex, def-pc-tensor-complex-sheaves and lem-pur-kflat-map-factorization. Tensor with the shifted regular module is a shifted acyclic complex, so its K-flatness needs only the displayed definitions. Flatness of its terms is the elementary fact that tensoring with O is the identity and with 0 is zero. The factorization lemma applies to precisely this domain; its conclusion includes flat terms and homotopy, which gives the boundary h(1) required by the step. Smallness and commutativity match the item. There is no claim that K-flatness makes Gamma exact.

For step 4 I opened lem-weil-pbc-site-derived-tensor-descent and the new 0FPK node, and read lem-sc-module-cup-shifted-unit-tensor and its shifted free source statement. The descent statement supplies the canonical derived isomorphism for P,Q with flat terms; the comparison lemma supplies the equality of the actual derived maps. The shifted-unit lemma applies over the arbitrary ring A to chain maps into the arbitrary complexes Gamma(P), Gamma(Q), so it does not need flat global sections. Its normalization states that the value at 1 is the (a,b) summand of the two cycles, without a sign. The cocycle pairing is the current one in def-sfb-ringed-site-module-cup-product, natural under the canonical resolution identifications; on free single complexes its definition has exactly that normalization. All off-unit statements used as generic tools are declared in split_report.tool_uses.

For step 5 I reread the local tensor-of-cocycles clause of def-sfb-ringed-site-module-cup-product. Both edges now send the same global family to its sheaf class. This is checked object by object and the differential/boundary signs are written explicitly, rather than asserted as an unspecified transport. The step uses only that definition and previous proved steps; it is elementary. No step exceeds 2000 characters, and none hides a separate comparison argument.

I tested a=b=0, zero input classes and complexes, and the zero ring/zero sheaf: the map reduces to tensoring the appropriate class or is zero. For the one-object point site over an arbitrary ring with torsion allowed the edge is the identity and the formula is the ordinary derived tensor cocycle formula; it requires no field or flatness assumptions on K,L. For a site with no final object, a global cocycle is a compatible family and equivalently a map O[-a]→I, so every construction in steps 1 and 3 still makes sense. Negative n for the edge and shifts are allowed; only the requested a,b are nonnegative. Unbounded totals have direct-sum terms; a particular pure tensor uses a single summand, so neither Gamma commuting with infinite sums nor convergence of a spectral sequence was used.

Mathlib checks: all new recorded searches were run via msearch and their results read. Two Loogle attempts had unknown identifiers and are marked unavailable; the corrected query DerivedCategory, CategoryTheory.Functor.LaxMonoidal ran successfully with no hits. Read SheafCohomology/Basic.lean (H and cohomologyPresheaf are Ext for a single abelian sheaf), Algebra/Homology/Monoidal.lean (tensorObj/tensorHom are ordinary total tensor), presheaf Monoidal.lean (sectionwise tensor), PullbackContinuous.lean (underived composition), PointwiseRightDerived.lean (generic derived comparison factorization), and Monoidal/Functor.lean (rightAdjointLaxMonoidal). None states 0FPK or the edge identity in one line. The new result remains unsplit, not a Mathlib leaf.

## Unfinished work

No unfinished part of this one-level split. The new statement-only 0FPK node is intentionally left for a later stage-1 worker, as required.
