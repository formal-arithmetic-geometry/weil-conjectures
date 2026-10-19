# Stage-1 delivery: thm-dg-finite-type-constructibility

## Files written

- `dag/nodes/sec-smooth-purity/thm-dg-finite-type-constructibility.json`: existing statement unchanged; seven-step split following the current blueprint, status split.
- `dag/nodes/sec-smooth-purity/lem-dg-etale-injective-finite-cech-rows.json`: one new statement-only lemma, status unsplit; no exact Mathlib match.
- `citations.json`: verbatim statement excerpts for every use in every step, including the module-sheaf derived-image clause in step 2.
- `report.md`: this report. Search evidence is preserved in `searches.jsonl`.

## Attachments

None. I searched the entire `WeilConjectures/` tree of the read-only slopmaster2 source by the blueprint id and by finite-type/constructibility and Cech/augmentation terminology. In `SixFunctors/Etale/Derived/Finiteness/DirectImage.lean`, `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType` (lines 105–114) has exactly the expected field/finite coefficient/finite-type hypotheses, no separatedness hypothesis, and a `sorry` body. It is reference material, not a finished proof. Its open-immersion predecessor is also sorried. The project Cech source files give ordinary presheaf/abelian Cech constructions and positive exactness, not the new finite ordered etale module-sheaf split resolution.

## WANTED

None: the current blueprint and the required Stacks source files are present locally.

## What was wrong or incomplete

The imported item remains unsplit despite carrying the earlier 2026-10-14 proof and review records. Those records and every maintainer-owned field are retained. I used the `blueprint_update` proof and read its actual files under `main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/`, rather than relying on the old master path in the protected source field.

The old step 1 and step 3 each exceed 2000 characters and contain independent comparison arguments: localized injective computations, split exact Cech rows, and the row-to-total quasi-isomorphism. The new split isolates these. I found the existing `lem-sc-finite-strip-row-augmentation` and reused it rather than adding another totalization lemma. The genuinely missing input is the finite ordered Cech sheaf resolution for injective modules on the small etale site; its split exactness must be stated, since an arbitrary left exact direct image does not preserve arbitrary exact rows.

No statement dispute, target change, unit-route replacement, SGA citation, Lean edit or compilation is involved. The node is not the unit's key compact-support base-change statement, so no unit realization record is changed.

## What remains unfinished

The new Cech-row node is deliberately statement-only and unsplit, as required for a one-level split. The intended later proof is recorded below. There are no unresolved parts of the item's natural-language proof.

## Searches and source reading

All new Mathlib search records are generated from actual `msearch.py` results in `searches.jsonl`, with identical tool/query strings. I ran LeanFinder with both a totalization phrasing and two phrasings specifically about finite split Cech rows, LeanSearch for both formulations, Loogle with qualified names after the unqualified `Sheaf` identifier failed, and grep in `Algebra/Category/ModuleCat`, `CategoryTheory/Sites` and `Algebra/Homology`. I also searched the item itself with two semantic phrasings. No service failure is represented as absence.

The closest real hit is `CategoryTheory.ShortComplex.ShortExact.splittingOfInjective`, read at `Mathlib/Algebra/Homology/ShortComplex/ShortExact.lean:205–209`; it assumes an already short-exact short complex and an injective first term. It does not construct or prove exactness or injectivity of the ordered Cech sheaf terms. Thus it is not a one-line specialization proving the new node. `Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean` was read in full: it defines the tuple-indexed presheaf Cech complex; it contains no finite ordered split sheaf-resolution theorem. The injection hits concern either functions or isolated injective-resolution components. The finite-type hits include Chevalley constructible images of subsets, not constructible etale sheaves or their higher direct images.

Before naming the new node I searched the whole DAG by Cech, split exact, injective terms, 08FI, 0136, 0137 and 0133, and ran `tools/blueprint_refs.py search` for Cech, finite filtration, totalization, injective complex, open cover, finite open, split exact and injective terms. The ancestor command gives the item itself. No blueprint node has the new statement. The existing O_X-module results in the Picard chapter cannot be specialized to constant A_X modules on the small etale site merely by changing coefficients: their sites and structure sheaves differ.

For the item I read the current blueprint statement and all three proof paragraphs; for the new node I read `sites-cohomology.tex`, the discussion preceding and proof of Tag 08FI (`lemma-restrict-K-injective-to-open`), `homology.tex` Tag 0136 (`lemma-characterize-injectives`) and Tag 0137 (`lemma-product-injectives`). I also read `homology.tex` Tags 0130, 0132, 0133 for the row/column total-complex comparison, and `cohomology.tex` Tags 01FJ and 01FM for the distinction between increasing and unrestricted tuples. The new node is honestly described as an agent-formulated finite etale module-sheaf corollary; none of those tags is falsely presented as stating it verbatim.

The later proof of the new node is as follows. Define all face restriction maps on sheaves by their section maps. Deleting two different indices in either order gives opposite signs, so the differential squares to zero and annihilates the augmentation. On each U_t, the augmented ordered row is contractible: for an increasing tuple I not containing t, the homotopy takes the component indexed by I union {t}, with the sign of the position of t, and for a tuple containing t it is zero. The degree-zero homotopy is restriction to U_t; pairing deletion/insertion terms gives dh+hd=1, including the augmentation. Since the U_t cover X this proves exactness as module sheaves, without asserting exactness of global sections. Open restriction is exact and has an exact left adjoint, so it preserves injectives. Direct image along u_I is right adjoint to exact open restriction and also preserves injectives. Each finite sum is a finite product of injectives and is injective. Start with the injective cycle J; its inclusion into C^0 retracts. Its complement is a direct summand of the injective C^0 and hence injective, so the next cycle inclusion retracts. Repeat through the finite row. The r=0 case is the zero category of sheaves on the empty scheme. This uses no statement or conclusion about constructibility.

## Review by Q102

I reviewed the source and every cited node's statement, rather than treating the previous review as evidence. The item's statement agrees with the current blueprint: arbitrary (possibly nonseparated) morphisms between finite-type k-schemes, finite allowable coefficients, and ordinary bounded constructible derived categories. The proof never uses adic, completed or pro-etale coefficients. The new node quantifies over arbitrary schemes and arbitrary commutative A; it assumes injectivity and a finite cover, and asserts only the split ordered module-sheaf resolution. Finiteness and invertibility of A are needed only for the geometric finiteness results, not for this new lemma.

In step 1, `lem-wf-affine-noetherian-components` actually states both Noetherianity of a finitely generated k-algebra and the descending-chain condition on its spectrum. Restricting closed chains to finitely many charts, and passing to finitely many distinguished opens, are the explicit elementary arguments establishing the assertions used later. No separatedness of X or affineness of its intersections is inferred.

In step 2, the enough-injectives node applies to Mod(X_et,A), not only Ab(X_et). The injective-representative node supplies both a strictly bounded-below complex of injectives and K-injectivity of any such complex. The localized-adjunction node asserts a left adjoint preserving finite limits and colimits, so the displayed adjunction lifting argument really proves that restriction preserves injective objects; it does not cite a definition as a preservation theorem. The direct-image node's module clause explicitly supplies the same K-injective computation for module sheaves. Restriction is exact by the local description of cokernels and preserves the zero maps required by that adjunction node.

In step 3, the direct-image node says (u_*F)(W)=F(W times_V U). This gives an equality of the two actual restricted complexes, respecting differentials, and step 2 makes both derived computations legitimate. The bounded-constructible definition gives exactly the finite-stratification and cohomological-range conditions used here. Refining by the successive differences V_j minus the earlier opens is an explicit finite disjoint stratification; finite local constancy restricts to it. I did not use the abelian-only etale localization exchange node for module coefficients.

In step 4, I checked the actual statements of the affine compactification proposition and its two construction definitions: for an affine finite-type map to affine Y they supply an open immersion into a proper Y-scheme. An intersection X_I is an open of X_i and hence of that same compactification, so taking another closure is unnecessary. Its finite-type property follows from step 1. Properness includes finite type, so the ambient compactification is again finite type over k. The open and proper bounded-constructibility nodes both apply to these finite-type k-schemes with the same allowable A. Clause (5) of the composition node explicitly concerns ordinary unbounded derived categories on the small etale site for any commutative A; its much more restricted adic clauses are not used. No assumption that f is separated enters this step.

In step 5, the new node supplies split exactness of the augmented sheaf rows, not merely ordinary exactness. Applying additive f_* preserves all splitting equations. Its direct-image section formula identifies the resulting composite terms with f_I,* and its additivity preserves finite biproducts. The finite-strip row-augmentation node requires a given row quasi-isomorphism whose degree-zero component is the displayed augmentation, a chain map into the total with that same component, and a finite horizontal strip. Each is verified in the step. This justifies the actual augmentation, not merely an abstract homology isomorphism. The bounded-below vertical reindexing reconciles the existing first-quadrant total definition with potentially negative cohomological degrees. Every sum in a total degree is finite.

In step 6, the double-complex definition identifies the associated graded with the signed shifted column. Step 2 supplies its injective computation, and the sign is an invertible scalar. I read the full statement of the bounded filtered-page theorem: it gives E_1=H(gr), page cohomology, stabilization and the finite separated abutment filtration. Its required quotient comparison maps are explicitly supplied by inclusion; F^(p+t) is contained in F^(p+1), so they are well defined. Uniform finiteness is horizontal, so an unbounded resolution above does not violate this hypothesis. The composite-functor Grothendieck spectral sequence is not incorrectly substituted for the Cech spectral sequence.

In step 7, the constructible Serre node explicitly gives kernels, cokernels and extensions. Finite sums follow by split short exact sequences, images by taking kernels of cokernels, and page terms by taking the cohomology kernel modulo the image. The finite filtration therefore gives constructibility of the abutment and vanishing outside [a,b+r-1]. A finite filtration with all quotients zero is zero by induction. The bounded-constructible definition is exactly the final conclusion.

I tested the new statement on r=0 with X empty, r=1, a repeated open, disjoint opens, empty intersections, the zero sheaf, A=0, and a nonseparated scheme. None requires stalk finiteness, any affineness of an intersection, or exactness of arbitrary direct image. For the item I also checked K=0 and a complex shifted into negative degrees. Every non-elementary step is below 2000 characters; the formal subclaim formerly hidden in the long Cech step is now either the new node or the existing finite-strip theorem. I checked B1–B9 (self-contained statement, no child proof or sketch, single TeX escaping, concrete source tags, exact search evidence, blueprint ancestry), C1–C8 (all inputs cited with verbatim quotes and off-unit tools proposed), D1–D5 (child is not a finiteness clause and seven parent steps carry the proof), and E1–E7 (the exact hypotheses and coefficient/site choices above). I corrected the old unchecked row-total comparison and did not change the item's statement.

## Not duplicates

lem-dg-etale-injective-finite-cech-rows vs lem-weil-pbc-etale-localization-exchange: the existing node asserts derived exchange for etale base change for bounded-below abelian complexes; the new node constructs split finite ordered Cech rows of injective A-module sheaves and asserts no exchange isomorphism.

lem-dg-etale-injective-finite-cech-rows vs lem-weil-pbc-ringed-projection-restriction: the existing node compares pro-etale ringed derived operations and projection maps under localization; the new node concerns an ordinary small-etale finite ordered sheaf resolution and contains no tensor or projection map.

lem-dg-etale-injective-finite-cech-rows vs lem-weil-pbc-horseshoe-morphism-lift: the existing node lifts maps between prescribed horseshoe resolutions of short exact sequences; the new node specifies a finite Cech sheaf resolution without any input horseshoe data.

lem-dg-etale-injective-finite-cech-rows vs lem-weil-pbc-colimit-of-sites-injective-system: the existing node embeds an inverse system of abelian sheaves in an injective system over a family of sites; the new node is a finite ordered Cech resolution on a single small etale site.

lem-dg-etale-injective-finite-cech-rows vs lem-weil-pbc-horseshoe-degreewise-map: the existing node lifts prescribed end maps degreewise between already short-exact complexes; the new node proves exactness and injectivity for explicitly prescribed finite Cech sheaf terms.

lem-dg-etale-injective-finite-cech-rows vs lem-weil-pbc-ses-injective-kernel-splits: the existing node splits an already given short exact sequence with injective kernel; it is a tool in the later proof, whereas the new node establishes exactness and injectivity of the explicit entire ordered Cech sheaf resolution.

lem-dg-etale-injective-finite-cech-rows vs lem-weil-pbc-product-injectives: the existing node only proves that products of injectives are injective; it does not construct Cech terms, prove their restricted/pushed-forward factors injective, or prove exactness and splitting of Cech rows.

lem-dg-etale-injective-finite-cech-rows vs lem-pur-kinjective-restrict-localized: the existing node preserves K-injectivity under localized restriction; it asserts nothing about finite ordered Cech row exactness or splitting.

lem-dg-etale-injective-finite-cech-rows vs lem-pur-kinjective-restrict-localized-adjunction: the existing node supplies the exact left adjoint of localized restriction; the new node is an entire finite ordered Cech sheaf resolution, including exactness and splitting.

lem-dg-etale-injective-finite-cech-rows vs new-localized-restriction-extension-exists: the existing node asserts existence of the exact left adjoint of localized restriction; it gives no Cech resolution or splitting.

Additional concept checks: lem-dg-etale-injective-finite-cech-rows vs lem-sc-injective-terms-alternating-cech-augmentation: that node compares global sections of integer-indexed O_X-module complexes on the Zariski site with an alternating total; the new node concerns split augmented rows of A-module sheaves on X_et.

lem-dg-etale-injective-finite-cech-rows vs lem-sc-etale-open-cech-injective-augmentation: that node gives an abelian-group tuple-indexed section quasi-isomorphism; the new node gives injective terms and split exactness as module sheaves, which is what permits arbitrary additive direct image.

lem-dg-etale-injective-finite-cech-rows vs lem-sc-finite-strip-row-augmentation: that node assumes row quasi-isomorphisms in an arbitrary abelian category and concludes a total quasi-isomorphism; the new node establishes the specific sheaf-row input. The item cites the existing totalization node directly.
