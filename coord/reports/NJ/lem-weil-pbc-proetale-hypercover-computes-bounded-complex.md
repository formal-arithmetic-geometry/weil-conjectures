## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-proetale-hypercover-computes-bounded-complex.json: item, statement, split into eight proof steps; not a Mathlib leaf.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-ringed-hypercover-injective-augmentation.json: new statement-only node, unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for every proof-step citation.

## Attachments

None. Searches of WeilConjectures in both read-only source trees for the item tag and for hypercover/injective and weakly contractible terminology gave only finite-degree site APIs and unrelated declarations, not the all-degree bounded-below derived-section comparison. Upstream master was used only as reference, never as evidence that a sorry declaration is finished.

## WANTED

None. The relevant Stacks source files are present.

## Corrections and scope

The statement's hypotheses and conclusions are preserved. Its last explanatory resolution reference was corrected from lem-weil-pbc-dplus-injective-representative to lem-sc-bounded-below-injective-resolution. The former supplies an abstract derived-category isomorphism in an abelian category with enough injectives; its etale example is not an existence theorem for chain maps on this ringed pro-etale site. The latter explicitly supplies the needed chain quasi-isomorphism on any small ringed site, with bounded-below injective terms and K-injectivity. No mathematical statement dispute or unit-route error was found.

The split follows Stacks 09A2, not an assertion that weakly contractible hypercovers are finite or truncated. The one new node handles a single injective module sheaf, independently of any complex, weak contractibility, affineness or derived evaluation. The two total-complex comparisons, resolution choice, and naturality remain arguments of the item; they have not been moved into another node.

The generic small-site epimorphism criteria, general ringed-site resolution theorem and first-quadrant total comparison are declared as tool uses in split_report. They implement the hypercover model used for coefficient-extension continuity below thm-weil-pbc-qbar and do not replace any step of the proper-base-change unit. The item is not the key statement of its unit, so no unit record was changed. Its blueprint ancestor was checked with blueprint_refs.py ancestor; searches across the whole imported blueprint for hypercover, injective hypercover, first-quadrant, ringed hypercover, free resolution, 01GW, 01GF and 0946 gave no equivalent all-degree ringed-site statement. The narrower etale free-resolution node was read rather than generalized silently.

## Not duplicates

lem-weil-pbc-ringed-hypercover-injective-augmentation vs lem-weil-pbc-hypercover-free-resolution: the existing node assumes a split etale hypercover of a scheme and concludes free abelian/constant-ring resolution and injective acyclicity there; the new node concerns arbitrary small subcanonical sites, arbitrary nonconstant ring sheaves, and any sheaf-matching hypercover, without splitting or etaleness. Its specialization to a constant-ring split etale hypercover is already covered by the existing node, but its needed pro-etale arbitrary-ring case is not.

## Source checks

For the item I read proetale.tex, Tag 09A2 (lemma-compute-cohomology), including the two spectral-sequence comparisons; sites-cohomology.tex, Tag 0946 (lemma-w-contractible); sites-modules.tex, Tag 03DA (lemma-abelian); derived.tex, Tag 013K (lemma-injective-resolutions-exist), especially part (3); homology.tex, Tag 0132 (lemma-first-quadrant-ss); and the K-injective localization-Hom declaration at Mathlib/Algebra/Homology/DerivedCategory/KInjective.lean:41-46. The Stacks tag/label mappings were checked in tags/tags.

For the new node I read hypercovering.tex, Tags 01GE (lemma-acyclic-hypercover-sheaves), 01GF (lemma-hypercovering-acyclic), 01GW (lemma-injective-trivial-cech), and 01GY (lemma-cech-spectral-sequence). This is explicitly a ringed-module analogue, not a verbatim assertion of 01GW about module injectives. The 01GE proof uses coskeleton comparisons and objectwise trivial-Kan homotopy contractions before exact sheafification. The same free-chain calculation works with free modules over R(T) in place of free abelian groups: the contractions and chain homotopies are coefficient-linear, so their tensor with R(T) remains a contraction; no flatness of R over the integers is needed. Sheafifying the free R-module hypercover chain complex therefore gives an exact augmented resolution of the free R-module sheaf on h_W. Adjunction identifies Hom from the free sheaf on h_V to I with I(V), compatibly with all faces. Applying exact contravariant Hom(-,I), using module injectivity, gives the new node's canonical augmented section sequence. This is the 01GW Hom argument with module coefficients; it does not assume that I is injective after forgetting coefficients. The sheaf-matching formulation uses 01GE directly, so no finite-limit property of the site itself is required (the finite matching limits are taken in sheaves).

As an independent sanity check, sites-cohomology.tex Tag 03FD proves that module injectives are underlying-abelian cohomologically acyclic at every object, even without underlying-abelian injectivity. Where the site's fibre products exist, Tag 01GY then collapses for such a coefficient sheaf to give the same positive-degree vanishing and canonical degree-zero augmentation. This cross-check was not used as a cited step of the item's proof.

## Mathlib searches

All recorded searches were executed through /home/ubuntu/weil-launcher-nt/msearch.py NJ lem-weil-pbc-proetale-hypercover-computes-bounded-complex and their actual results are in searches.jsonl. Both the item and the new node were searched twice by semantic phrasing, with Loogle and source grep as well. LeanSearch returned Internal Server Error and is recorded as unavailable. LeanFinder was available. Its results concern generic injective resolution objects, K-injectivity, Mayer-Vietoris squares and one-hypercover sheaf conditions. Loogle's quoted Injective/Sheaf searches produce local injectivity of morphisms or presheaf monomorphisms, not injective objects' all-degree hypercover cohomology. Source grep gave only finite-degree hypercover exactness and Cech-like local-cohomology comments. I read the Zero and IsSheaf hypercover API descriptions: those cover degrees zero and one and do not state the new lemma or the item. These hits are not one-line specializations to the statements here. No new Mathlib leaf is claimed.

## Review by NJ

I checked delivery-errors B through E against the statements, cited nodes, and source files. The new node introduces its site, universes, ring sheaf, module sheaf, injectivity, object W, simplicial object, matching epimorphisms, section complex and canonical augmentation. It has no proof sketch in its statement and no proof or proof dependencies. Matching objects are finite limits in the sheaf category, not an unstated finite-limit hypothesis on the site. This correction avoids making the item prove closure of weakly etale schemes under limits as a side theorem. There is one genuinely missing non-elementary sheaf lemma and no new elementary fact or relocated complex-computation clause.

Step 1 uses the affine-hypercover node only for the meanings of its simplicial maps and representable sheaves, the module-category definition for semilinearity, and the double-complex definition for the total signs. I checked all three statements. Their combination gives the explicitly written cancellation and finite diagonal, marked elementary; no existence theorem or qcqs hypothesis is applied to W.

Step 2 uses the two general-site epimorphism criteria, not their etale specializations. I read their statements: one says an abelian-sheaf epimorphism is equivalent to local section lifts and the other says those same lifts give a set-sheaf epimorphism. The module-category statement computes kernels sectionwise and cokernels by sheafification, so forgetting coefficients preserves these operations. The weak-contractibility definition in the hypercover node then says exactly that evaluation sends this set-sheaf epimorphism to a surjection. Kernel preservation and cohomology preservation are written out. This is a module-valued exactness argument for arbitrary R, without a coefficient-flatness assumption.

Step 3 uses the actual chain-level small-ringed-site resolution node and the size convention; both statements were opened. Its conclusion supplies every property of J used later, including K-injectivity. I corrected the original abstract D+ reference and used a common lower bound instead of assuming that the theorem preserves the original bound N. Reindexing is explicitly plain relabelling, with no hidden shift sign.

Step 4 uses the total-comparison node, whose statement concerns the flipped resolution columns. I read its statement and recorded the necessary transposition for the vertical section complexes. The factor (-1)^(pt) converts the total signs in both differential directions. This ensures that the theorem applies to the right coordinate and the comparison obtained is the actual totalized map beta, not just an abstract homology isomorphism.

Step 5 uses the newly stated injective augmentation and the hypercover notion node. The module injectivity is provided by step 3. Subcanonical representables are the sheaves of scheme morphisms in the hypercover node's statement, and matching epimorphisms are assumed for the given U. Neither an affine nor a qcqs conclusion is taken from the existence node. The new theorem has no weak-contractibility assumption; only the already assumed all-degree hypercover condition is needed here.

Step 6 uses the same total-comparison statement, now without transposition: for fixed coefficient t the flipped complexes are the horizontal hypercover rows of step 5. I wrote the single-column source S explicitly and checked delta kills its degree-zero restriction augmentation. Its total is J(W) with the prescribed differential. Localization at quasi-isomorphisms in the derived-category definition gives inverses for alpha and beta, and their composite is the requested A-module isomorphism. Every restriction and augmentation is A-linear by step 1.

Step 7 uses the existing Mathlib leaf for localization-Hom bijectivity into K-injectives, together with the generic ringed-site K-injective/homotopy and localization definitions. I read its Mathlib signature, so both surjectivity (choice of comparison a) and injectivity (homotopy equality of the two lifts) are available. The signed total homotopy and augmentation square are explicit. They show equality in the derived category, independence of the chosen resolution, and naturality for coefficient maps; no canonical or functorial chain-level injective choice was assumed.

Step 8 reapplies the total-comparison theorem to an arbitrary quasi-isomorphism using exact evaluation from step 2. A common lower bound exists even when the two complexes have different bounds. This proves the final chain-level assertion directly.

I tested the zero complex, the zero ring, a sheaf concentrated in an arbitrary degree (including negative degrees), and different lower bounds for source and target. The resulting total below the bound is zero and the relabelling does not change the differential signs. For the new node I tested the identity hypercover: the alternating complex has successive differentials 0, identity, 0, identity, giving the required exact augmentation. An ordinary Cech nerve is a special case, but the new node does not silently replace every hypercover by a Cech nerve. Arbitrary nonflat torsion coefficient rings are permitted: the argument uses module injectivity and free-chain homotopies, not tensoring a nonsplit exact sequence with a nonflat ring. Neither W nor U was given an extra quasi-compactness assumption. No cycle is introduced through resolution existence, total comparison or K-injective comparison, whose statements have no dependency on the item.

## Unfinished work

The new injective hypercover augmentation is intentionally left unsplit for the next stage-1 item. All eight steps of the present item are supplied. No Lean was written, no compiler was invoked, and no delivery was pushed. The sandbox is for the required second reader.

## Second reading by NJ

- Item statement: checked against proetale.tex Tag 09A2 (lemma-compute-cohomology), with sites-cohomology.tex Tag 0946 and the cited resolution/total-comparison tags; all hypotheses, boundedness, finite-diagonal sums, derived-evaluation conclusion, naturality, and quasi-isomorphism clause agree.
- Step 1: checked the affine-hypercover, module-category, and total-complex statements; the stated sign cancellation, finite diagonal, and A-linearity are elementary consequences.
- Step 2: checked both site epimorphism criteria, module kernel/cokernel definitions, and weak-contractibility clause; evaluation exactness and preservation of cohomology use precisely those statements.
- Step 3: checked the bounded-below injective-resolution and size-convention nodes; the chain-level resolution, K-injectivity, common lower bound, and reindexing are stated with no stronger bound assumed.
- Step 4: checked the first-quadrant total-column comparison and double-complex total definitions; the transposition and $(-1)^{pt}$ sign identify the comparison with the displayed total map.
- Step 5: checked the new ringed-hypercover augmentation against hypercovering.tex Tags 01GE and 01GW and the hypercover notion node; it uses module injectivity and no hidden affineness or weak-contractibility premise.
- Step 6: checked the total-column comparison and derived-category localization statements; the augmentation map, source total, and inverse composite are the asserted derived isomorphism.
- Step 7: checked the K-injective localization-Hom declaration and the K-injective/homotopy definitions; the signed total homotopy proves resolution independence and naturality.
- Step 8: checked the total-comparison node and Tag 09A2; the argument handles distinct lower bounds and proves the chain-level quasi-isomorphism directly.
- New node `lem-weil-pbc-ringed-hypercover-injective-augmentation`: checked against hypercovering.tex Tags 01GE, 01GF, 01GW, and 01GY; it is self-contained, statement-only, defines the matching epimorphism and section complex, and has no Mathlib match.
- Edge cases checked: zero complex and zero ring, arbitrary (including negative) concentrated degree, unequal lower bounds, and the identity hypercover; all give the stated zero/exact or relabelled complexes.

Changes made: corrected the item node's `created.item` metadata to this delivered item; retained the worker's mathematical statements and proof steps after source and dependency checks; added this second-reading record.
