# Q115 — lem-sfb-ringed-hom-composition-model

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-hom-composition-model.json`: existing statement node, now split in eight steps. The statement and its hypotheses are unchanged. No exact Mathlib match; the abstract closed-category composition and the group-valued cochain composition do not establish the sheaf-valued construction and its normalized derived representative comparison.
- `citations.json`: a literal statement quotation for every node cited in every proof step.
- `searches.jsonl`: actual searches made with the required msearch command. The inherited Mathlib search records were retained and the new logged searches appended to the item.

New nodes: 0. New Mathlib leaves: 0. No Lean files or repository files written; no compiler, Lake, or build run.

## Attachments

None. The project search for the exact blueprint tag returned no declaration. Searches by HomComplex, internal-Hom composition and homComplex composition led to `WeilConjectures/Algebra/Homology/HomComplex.lean`, `DerivedInternalHom.lean`, `ModuleHomComplex.lean`, and `CategoryTheory/Monoidal/Mod/IhomComp.lean`. The first builds the sheaf Hom bifunctor and degree-zero pre/postcomposition, the second builds the derived bifunctor and representative comparisons, the third concerns scalar module complexes, and the last concerns module objects in an abstract monoidal category. None states every clause of this item, notably the arbitrary one-K-flat total-sheaf-tensor composition model with the fixed derived adjunction. These are not attachment claims, and no sorry declaration was treated as a finished proof.

## WANTED

None. All sources used are present locally.

## Findings and corrections

The item was an unsplit statement with no proof. I supplied the omitted functoriality of Stacks 0A98 by counit naturality and wrote its chain construction and the comparison with the stipulated normalized adjunction explicitly. There is no statement dispute and no source correction.

A crucial distinction is that the Stacks construction starts with `Hom(J,I) tensor T`, where only T is K-flat. I used the existing one-K-flat native comparison, rather than assuming `Hom(J,I)` K-flat. Auxiliary K-flat replacements U of `Hom(J,I)` and P of E are used only to test the equality after invertible localization maps. The original arbitrary T is kept throughout and is never assumed to have flat terms. A second distinction is that I and J, although K-injective, need not equal their fixed functorial replacements; the Hom comparisons use their actual augmentations and cancel their localized inverses explicitly.

The source unit record still has no realization recorded (the server review reports this). This item is an auxiliary created node, not the unit's key node; I left the unit and chapter records untouched. The blueprint origin and its precise paragraph were retained, with `same_as: []` confirmed by whole-blueprint searches for Hom complex and internal Hom composition. No unit-level proof route is replaced.

## Not duplicates

There are no new nodes and consequently no new/existing-node pairs requiring a duplicate distinction. Whole-DAG searches for 0A91, 0A98, uncurrying, K-injective Hom invariance, and Hom-complex composition found the model, resolution, and comparison nodes reused below. The neighboring ordinary-evaluation lemma concerns `F tensor Hom(E,O)` and the dual-unit evaluation comparison; it does not state arbitrary composable Hom complexes. The neighboring strict-transpose lemma has a flat-term K-flat argument and a scalar-sheaf numerator; it is unnecessary here because the fixed model already normalizes pairs of K-flat complexes.

## Unfinished work

None within the assigned one-level split. Existing dependencies retain their own stage status. The proof is marked agent-written because I supplied the functoriality and normalization argument omitted by the source, rather than attributing these extra details to Stacks.

## Review by Q115

I read Stacks `sites-cohomology.tex`, section-hom-complexes (0A8X), lemma-composition (0A91), lemma-internal-hom-composition (0A98), lemma-internal-hom (08J9), lemma-RHom-well-defined (0A95), and lemma-K-flat-resolution (06YS). I also read the direct calculation in `more-algebra.tex`, lemma-composition (0A8I), which 0A91 explicitly points to, and the module-sheafification universal property in `sites-modules.tex`, lemma-sheafification-presheaf-modules (03CY). The exact tag/label correspondences were checked in `tags/tags`. I read the current main-20261015 blueprint ancestor proof, especially paragraph 2's perfect-dual evaluation identification, and the recorded chapter and unit route. There are no new nodes with additional sources to review.

For steps 1 and 2, I opened `lem-sf-ringed-derived-closed-symmetric-monoidal` and verified that its statement supplies a bijection natural in all three objects and the evaluation formula for its inverse. These are precisely the two ingredients needed: injectivity of transposition, target naturality of evaluation, and its parameter naturality. Step 1 gives both outer naturality identities; step 2 gives the actual common uncurried map for the two dinaturality composites. No representative of an arbitrary derived morphism is assumed.

For step 3 I read `def-pur-hom-complex`, `def-pc-tensor-complex-sheaves`, `def-pur-sheaf-tensor-product`, and `def-weil-presheaf-modules-sheafification`. Their statements supply the Hom products, tensor direct sums and differential, the sectionwise presheaf tensor followed by sheafification, and unique factorization of linear maps into sheaves. The argument uses those universal properties, not a nonexistent claim that sections commute with tensor or arbitrary coproducts. It uses finitely many total-tensor summands at a time, but imposes no finite support on a Hom-product family. Uniqueness follows on all actual tensor units and Hom projections.

For step 4 I checked the same definitions and expanded the differential. The intermediate `f d_J g` terms cancel with coefficients `-(-1)^p` and `(+1)(-1)^p`; the final coefficient is `-(-1)^(p+q)`. This proves the precise unsigned composition formula. I also wrote out the evaluation differential identity needed later. These are elementary calculations from the cited definitions, not separate theorem nodes or a restatement of the item in new nodes.

For step 5 I opened `lem-pc-kflat-resolution`, `lem-pur-rhom-well-defined`, `def-pur-derived-internal-hom`, and `lem-sf-ringed-derived-native-tensor`. The first gives the two auxiliary quasi-isomorphisms with K-flat sources on this small ringed site. The second allows precomposition by any quasi-isomorphism when the target is K-injective, and postcomposition only between K-injectives. I verified that the latter condition holds for I to I(I) and J to I(J); it is not asserted for an arbitrary non-K-injective target. The fixed RHom definition supplies exactly the canonical representative comparisons. The native tensor statement explicitly says either tensor factor may be K-flat, which is necessary for A tensor T here.

For step 6 I read `def-coef-ringed-tensor-hom-model` and `lem-sf-ringed-derived-tensor-hom-adjunction`: the former fixes the componentwise uncurrying equation for K-flat pairs, and the latter asserts that this is the equation for the chosen adjunction and native comparison. Both T and P are K-flat, so it applies to the actual chain map into Hom(P,I(J)). Its uncurry is eta_J composed with h; the prescribed inverse augmentation cancels eta_J. The Hom-invariance statement ensures the comparison used in step 5 is valid. Closure of the total tensor of K-flat complexes is explicitly part of the model's statement, so V is K-flat without a boundedness hypothesis.

For step 7 I checked that U and V meet the same normalization hypothesis. Precomposition with the actual chain map h defines k with the displayed formula; it requires no lifting of h through a chosen resolution. Counit naturality from the closed-structure statement identifies this normalized evaluation with evaluation at J after Qh. This gives the transpose of the closed composition on the auxiliary representatives.

For step 8 I checked the different pair W=U tensor T and P is again K-flat. The chain map phi is built from the already proved chain composition and actual Hom pre/postcomposition, so its formula is the same triple evaluation. The native comparison statement expressly preserves associators, which is the needed agreement between the two bracketings; I did not infer it from an arbitrary objectwise tensor isomorphism. Transposition is injective, and Qr, Qs, Qt are invertible because they localize quasi-isomorphisms. Cancelling these and the canonical Hom comparisons proves the conclusion for the original E,J,I,T. This comparison is the principal argument of the item, not a hidden auxiliary statement moved to a new node.

I checked edge cases E=0, J=0, I=0, identity u, a zero middle morphism, complexes concentrated in degree zero, and homogeneous maps of odd degree over the one-point ringed site with coefficient ring Z. In degree zero the construction is ordinary composition; in odd degrees the cancellation above has the required total-tensor sign and still no sign multiplying composition. The formulas make sense for arbitrarily unbounded complexes because they only compose one Hom coordinate at a time and sum finitely many tensor summands. No finiteness, perfectness, stalk, or field-coefficient assumption enters the proof.

I checked B through E of `delivery-errors.md`: all cited facts were read as statements, every non-elementary input is a cited node, all cited ids exist and are unmerged, no dependency reaches this item, the statement is unchanged, the exact current blueprint origin is filled, and there are no new nodes which could be elementary, duplicated, restated clauses, or missed Mathlib leaves. All eight proof steps are under 2000 characters. The out-of-unit results are generic resolution/adjunction/localization tools; their uses and reasons are declared in `split_report.tool_uses`, without adding top-level approvals.

The actual msearch hits were read: `CochainComplex.HomComplex.Cochain.comp` at Mathlib `Algebra/Homology/HomotopyCategory/HomComplex.lean:219`, its differential lemma at line 485, and abstract `CategoryTheory.MonoidalClosed.comp` at `CategoryTheory/Monoidal/Closed/Basic.lean` were inspected. They establish related group-cochain or abstract categorical facts, not this complete sheaf-valued/derived assertion. A second semantic phrasing and a second Loogle query were run before concluding no match. All new query records are copied from the actual msearch log, with no invented unavailable or empty result.

Server `review_split` passed with 0 new nodes; its only note is the unrelated unit realization mentioned above. The full deliver.py dry run and final push are the remaining delivery operations.
