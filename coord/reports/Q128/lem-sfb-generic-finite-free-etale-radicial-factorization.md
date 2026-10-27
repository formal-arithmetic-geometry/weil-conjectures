# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-generic-finite-free-etale-radicial-factorization.json`: statement, split; no Mathlib match. Nine proof steps, all using existing nodes. The statement and statement dependencies are unchanged.
- `citations.json`: one verbatim statement quotation for each step/node pair.
- `report.md`: this report and signed reading.

New nodes: 0. New Mathlib leaves: 0. No Lean files were written, no compiler was run, and the shared repository was read only.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for generic finite free, maximal etale, radicial and factorization terminology. The hits on radicial preparation and generic reduced models have different statements; none proves this item. Existing sorry declarations were not treated as closed proofs.

## Literature wanted

WANTED: Bosch–Lütkebohmert–Raynaud, Néron Models, §7.6 proof of Proposition 5(a), printed p.197, PDF p.203, for lem-sfb-generic-finite-free-etale-radicial-factorization. The local PDF named by the item is absent. I read the primary-source scan at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf, including the generic factorization paragraph. No document was downloaded to the repository. The explicit argument is marked `proof_origin.by = agent` because it replaces the abbreviated shrinking/power argument with cited Stacks results and supplies the finite-local-freeness strengthening.

## Problems found and corrections

The imported node had a correct strengthened statement but no proof. The proof now constructs the maximal etale generic algebra from the existing finite-subalgebra union, proves the necessary generic properties, descends its inclusion, and descends both surjectivity and surjectivity of the relative diagonal. It does not assume that the descended inclusion is injective, that the original scheme is reduced, or that any rank is positive or globally constant.

The `blueprint_refs.py ancestor` command returns `None` for this inherited chain, as recorded in the live item. Its existing `blueprint.from.node = null` and via list are retained. The place already identifies BLR Proposition 5(a) below the current blueprint's `det-thm-sf-ctf-stability-direct-images`, proof (3). I read that proof in `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`, together with the chapter and unit records. This is a generic algebra tool on the inherited Weil-restriction route, not a replacement of a unit step. The item is not its unit's key statement, so the unit realization record is not edited.

## Source error

The BLR paragraph asserts that each element of the finite generic algebra has some positive power in its maximal etale subalgebra. As written for arbitrary finite algebras this is false: in characteristic zero take $K'=K[\epsilon]/(\epsilon^2)$, with etale core $K$, and $a=1+\epsilon$. Then $a^n=1+n\epsilon$ never belongs to $K$ for $n>0$. Thus this sentence cannot justify the nonreduced characteristic-zero case of the imported item. The intended radicial factorization is nevertheless true. Steps 3–4 establish it by the maximal etale core after algebraically closed scalar extension, and step 8 descends its surjective diagonal. The source field notation is not silently interpreted as requiring reducedness. There is no dispute with or change to the item's statement.

## Searches and reuse

The live node's prior searches and results are retained. Fresh Q128 searches were executed by the required `batch2/msearch.py` command and appended from its actual `searches.jsonl` records, without inventing queries. They include LeanFinder with both the localization-factorization wording and finite-dimensional/maximal-separable wording; LeanSearch on the etale core and spreading; Loogle on the morphism classes and on `Algebra.FormallyEtale, Module.Finite`; and the prescribed grep in AlgebraicGeometry. The morphism-class Loogle query reported an unknown identifier and is recorded as unavailable. The second Loogle query ran and returned no hits.

I read the candidate `Mathlib/RingTheory/Etale/Field.lean`, in particular `Algebra.FormallyEtale.iff_exists_algEquiv_prod` at line 194 and its surrounding results. It classifies an already formally etale algebra and does not construct the core or the radicial factor. Other hits are etale-locus existence and etale Noetherian descent; none states the whole item. The logged search results in the JSON preserve the returned names. Existing Mathlib leaves in the DAG are reused as leaves; no duplicate leaf is introduced.

I searched the whole DAG by maximal etale/separable subalgebra, Artinian decomposition, field algebra, generic freeness, spreading, descent and the source tags (including 0CKR, 0CKT, 0CKU, 00KJ, 01ZO, 06AC, 05N9). Whole-blueprint searches used `blueprint_refs.py search 'etale radicial'`, `'finite etale'`, and `'maximal'`. No blueprint node states this item exactly. The searches found existing nodes for every non-elementary input, so no new statement-only node is needed.

## Not duplicates

No new nodes. In particular the finite-algebra field calculation reuses `lem-sfb-finite-etale-subalgebra-directed-union`, `lem-sfb-maximal-ind-etale-field-base-change`, `lem-sfb-ind-etale-core-ring-operations`, and the Artinian decomposition; the spreading calculation reuses the existing filtered-colimit and property-descent nodes. The item is not replaced by a new node restating its clauses.

## Review by Q128

I read the BLR paragraph described above against the entire unchanged statement: the base is a nonzero Noetherian domain, the finite locally free source may be disconnected or nonreduced, and the conclusion includes finite local freeness of the universally homeomorphic factor. I checked the supporting Stacks source statements in `algebra.tex`, `more-algebra.tex`, `limits.tex`, `morphisms.tex`, and the field and affine-spectrum source places. There are no new nodes requiring separate source validation. The following is my step-by-step check of the statements actually cited, not of arguments hidden in their proofs.

1. The definition of finite morphism says precisely that the inverse image of an affine is affine with finite coordinate module. The Noetherian finite-type/finitely-presented node supplies the finite algebra presentation, under the actual hypothesis that R is Noetherian (Tag 00FP). The affine fibre-product node identifies the tensor algebra with the actual generic fibre. A finite module generating family tensors to a spanning family. For the empty case I checked the spectrum-of-finite-free-algebra node explicitly allows an empty basis and the finite-product-etale node explicitly includes the zero algebra. Thus f=1 and T empty really work.

2. The directed-union node gives finite-subset capture, not merely existence of a union. Applying that exact clause to a vector-space basis proves that the core is itself finite etale, without an uncited finite-generation theorem. The field-product node says finite separable field factors, exactly what is used. Orthogonal idempotents give the displayed inverse maps by multiplication and summation. The finite K-spanning family also spans each component over its field L_j, so the finite-free-spectrum node applies. No common rank for the components is asserted. The definition of finite locally free has local flatness and local finite presentation, so disjoint target components suffice.

3. Tag 0CKU, through the existing core-base-change node, identifies the actual included subalgebras after arbitrary field extension; it does not just give an abstract isomorphism. The finite-dimensional Artinian observation is proved by decreasing vector-space dimension. Tag 00KJ's existing node then gives nonzero local factors, including the empty product. The local-idempotent node verifies exactly the hypothesis of the field clause of the core-operations node. Each core field is a finite-dimensional subspace, so the finite-extension-of-an-algebraically-closed-field node applies. The product clause of the core-operations node identifies the maps componentwise, not just the product objects.

4. The Artinian-local unique-prime node is applied to the actual factors H_i, not to their products. Each residue field is a quotient of a finite-dimensional Omega-space, hence finite, as required by the algebraically-closed-extension node. The uniqueness of the residue map and selection of one idempotent factor are written out. For arbitrary F the algebraic-closure definition explicitly includes existence of an embedding; the tensor-pushout node supplies the two extended maps and their restrictions. The field-point equivalence in the radicial definition is stronger than a definition alone and explicitly states both universal injectivity and surjectivity of the diagonal (Tag 01S4). Therefore this citation really supplies both assertions used later. No assumption that B is reduced is made.

5. The finite-algebra-integral node is used with the finite C-module B. Its finite family is the K-spanning family, so no extra finiteness hypothesis is missing. The lying-over node requires an injective integral ring map, and the generic core map is an actual subalgebra inclusion. This proves generic surjectivity; I did not apply lying over to the later model, whose injectivity is not known.

6. Tag 00CR supplies the colimit of principal localizations. The nonzero elements are a set and directed by products because R is a domain; one can replace the preorder by its quotient directed set if desired, with canonically isomorphic localizations. Tags 01YX/01YW give the scheme limit of these affine schemes. The etale-algebra-colimit node provides an etale C_g model with its generic algebra identification. The map-descent node is Tag 05N9(2) for *two finitely presented algebras*, and both presentations are available: etaleness gives one, and the localized Noetherian finite-type presentation gives the other. This descends the specified inclusion, so the eventual composition is the original p, not an unspecified generic factorization.

7. I checked the elementary relative-presentation calculation explicitly. The q_j(P) lie in the ideal of the r_k because the chosen map already exists. For the diagonal the differences of the finitely many algebra generators generate the multiplication kernel, as quotienting by them gives A_g itself. This is why no general diagonal-finite-presentation lemma needs to be created or cited. The affine fibre-product and tensor-pushout statements give the particular ring maps in the calculation. Thus the finite-presentation assumption of every application in the next step is checked, including the diagonal, and all three schemes in each limit situation are affine qcqs.

8. I opened each property-descent statement and checked the hypotheses in Situation 081D: affine transition maps, qcqs base/source/target, and the appropriate initial locally finite type or locally finite presentation. Tag 01ZO is used only for finiteness of the C-model. Tag 07RR is used separately for u and its relative diagonal, with the generic assertions established in steps 4–5. The permanence of surjectivity at larger indices is the statement of the spectrum-surjectivity-base-change node, and permanence of etaleness is the etale-ring-base-change node. Finiteness persists by explicitly localizing a generating family. I corrected the draft's ordering: Tag 06AC is now applied last, so there is no unstated appeal to permanence of finite local freeness while taking a common index. The 06AC node allows variable degree, exactly as needed.

9. The affine fibre-product formula identifies the final source and the algebra homomorphism makes the composite the restricted structural map. The radicial node states diagonal-surjective iff universally injective. The finite-implies-integral node and the integral/radicial/surjective universal-homeomorphism node supply precisely the remaining assertions. The last point-bijection statement follows from the definition of universal homeomorphism. Thus no non-elementary implication is left uncited.

I tested the argument on the empty scheme, a split product with unequal component ranks, dual numbers over characteristic zero, and a purely inseparable field extension over an imperfect field. Empty products are used consistently, each local factor is nonzero when the field clause requires it, no reducedness is smuggled in, and no assertion of uniform positive rank is needed. The dual-number example is the explicit counterexample to the source's power sentence; it satisfies the intended factorization with the core equal to K. Over a field base the localization system can already be taken at f=1. Nonzero products of shrinking denominators remain nonzero.

Every proof dependency has an exact quotation in `citations.json`, copied from the current node's statement. Off-unit tools are declared in `split_report.tool_uses` with their role; their statements are generic algebraic inputs, not replacements for the unit's six-functor route. All nine steps are under 2000 characters (maximum 1393 after the final order correction). The only step marked elementary is the explicit presentation/diagonal calculation. I checked B–E of delivery-errors against these files: no new nodes, no relabelled clauses, no assumptions added, no source tags used as substitutes for node citations, and no statement weakened.

## Unfinished work

None in the requested stage-1 split. The server review_split check passed before report completion; the required complete delivery dry run and push follow this report.
