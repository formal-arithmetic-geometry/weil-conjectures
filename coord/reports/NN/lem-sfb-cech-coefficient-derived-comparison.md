# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-cech-coefficient-derived-comparison.json: assigned statement, split into seven steps; no exact project declaration or Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-exact-square-right-derived-unit.json: general statement, unsplit; no exact Mathlib match.
- citations.json: a verbatim statement quotation for each step/node citation.

## Attachments

None. Searches by the exact blueprint tag and by coefficient/Cech concepts in lean/WeilConjectures found only special-case abelian etale transfers, ordinary scalar squares, and signed total homotopies. They do not state this general ringed-topos derived assertion.

## Literature wanted

None.

## Corrections and remaining work

No statement correction. The empty proof is replaced by the actual seven-step calculation. The item is an agent-created extension, so proof_origin is agent, not a claim that Stacks states the Cech coefficient assertion verbatim. The general exact-square lemma remains unsplit for the next stage-1 worker. There is no Lean writing or compilation.

## Searches and route

Read the original item, the current chapter and unit records, the current blueprint unit text, and the source references. blueprint_refs.py ancestor returns None, matching the imported item's existing null ancestor; this is retained. Searches for Cech coefficient, coefficient comparison, right derived base change, exact square and right derived functor found no blueprint duplicate. Whole-DAG statement searches found the nearby exact-square comparison requiring preservation of K-injectives, the adjoint-square comparison assuming the postcomposed universal property, and the common-resolution comparison assuming an invertible comparison; none gives the new general noninvertible unit comparison under the stated hypotheses. The unit route remains the direct-image coefficient compatibility route of paragraph (3). No source from SGA is used.

Read msearch.py results and searches.jsonl before recording searches. The item reuses its original searches and a second phrasing. The new lemma uses the exact logged query strings for LeanFinder, Loogle, LeanSearch and grep, including a second phrasing concerning exact postcomposition. Read PointwiseRightDerived.lean lines 43-83: its comparison assumes a universal source pair and does not establish that the postcomposed pair is universal. Read the source library PlusBaseChange.lean lines 30-88, whose analogous result is only bounded below. These are candidates for implementation, not Mathlib matches of the new unbounded statement.

## Review by NN

I read derived.tex at Tags 015F (lemma-right-derived-exact-functor), 070I (lemma-K-injective), 070Y (lemma-K-injective-defined), and 070J (bounded-below injective complexes). For the Cech construction I read sites-modules.tex Tags 04IE and 04J4 and sites-cohomology.tex Tags 08FI and 03FC. The source explicitly explains the exact left adjoint behind slice preservation of K-injectives. The new lemma's source is 070Y with an explicitly agent-written exact-postcomposition consequence, not a purported verbatim Stacks statement. Its planned proof uses K-injective computation: applying an exact functor after the computation still gives the derived functor of the composite; the universal property gives the comparison to RG D(U). No injectivity of U(I) is used. This lemma is smaller than the item: it has no covering, localization, bicomplex, total, augmentation or refinement.

Step 1 uses precisely the column-model statement, which supplies K-injectivity for I,J and every slice restriction, and the specified resolution-unit comparisons. It also cites the small-ringed-site K-injective existence statement for the generic exact-square lemma. Both coefficients are Cartesian, so both inverse images are exact; the small-site hypotheses are present. Step 2 uses exact descent to invert T_X(a) and the Hom-to-K-injective bijection to obtain t; it never calls T_X(I) injective. Step 3 uses the actual scalar-restriction definition and the total-complex definition. The given identities on underlying abelian sheaves and their restriction compatibility suffice for each face square, and finite biproducts give the total identification. Step 4 uses the new general unit lemma and the right-derived definition, whose statement explicitly supplies naturality and unit invertibility on K-injectives. I checked the direction e_I=Rf(Qa)^(-1) eta_I, so the subsequent cancellation has the required source and target.

Step 5 proves the augmentation square on the (0,q) summands and uses step 4's equality, then reapplies the general lemma to each slice. The column-model statement supplies exactly the needed K-injectivity and quasi-isomorphisms there. Step 6 writes the signed homotopy, checking both cross-term signs and the zero negative target when q=0. The derived-category definition identifies homotopic chain maps. Step 7 uses actual refinement restrictions furnished by the column model and writes their componentwise square, before taking finite sums and localization. No Cech augmentation quasi-isomorphism or inverse of gamma is required in any step. All cited node statements were opened and read; citations.json contains their verbatim text.

I tested identity scalar restriction (the comparison is the identity under the canonical identifications), the one-point site with Z to Z/m scalar restriction (an injective Z/m module need not remain injective as a Z module, so the no-preservation hypothesis matters), K=0 with arbitrary acyclic injective resolutions, the identity covering V=1 (the unnormalized Cech differential still has repeated vertices), and the degenerate empty topos. The homotopy and restriction formulas apply in degree zero and to empty or zero terms. The new lemma also allows U=0 or V=0 and the identity square. No false extra isomorphism claim survives these tests. Every proof step is shorter than 2000 characters and has no hidden standard lemma beyond the single explicitly extracted general unit lemma.

## Not duplicates

lem-sfb-exact-square-right-derived-unit vs def-sf-normalized-derived-comparison-identifications: the existing node concerns Canonical localization identifications for normalized derived comparisons; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs def-sfb-derived-comap-lower-star-iso: the existing node concerns Derived restriction of scalars commutes with $Rf_*$; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs def-sfb-right-derived-functor: the existing node concerns Right derived functor on the unbounded derived category; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs def-weil-pbc-derived-tower-models: the existing node concerns Strict tower complex functor and universal K-injective derived model; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs def-weil-pbc-direct-image: the existing node concerns Direct image and its derived functor; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs det-lem-formal-closed-support-adjunction: the existing node concerns Sections with closed support: adjunction and fiber triangle for all coefficients; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs det-nagata-density-normalization-pushforward: the existing node concerns Proper direct image through the schematic closure; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs det-pe-wc-sections-derived: the existing node concerns Derived sections over a w-contractible affine; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-asd-clopen-geometric-sections-derived-evaluation: the existing node concerns Unbounded evaluation on finitely many clopen geometric sections; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-coef-derived-tower-counit-projections: the existing node concerns Derived constant/limit adjunction with its actual projection counit; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-coef-tower-right-derived-evaluation: the existing node concerns Unbounded right derivation of an additive tower functor commutes with evaluation; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-exc-proetale-derived-open-restriction: the existing node concerns Unbounded pro-etale direct image commutes with open restriction; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-pe-bounded-complex-direct-image-presheaf: the existing node concerns Bounded-below direct-image cohomology is a sheafified inverse-image presheaf; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-pur-comparison-global-resolution-model: the existing node concerns Resolution model for normalized global site comparison; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-pur-derived-support-comparison-direct-image: the existing node concerns Derived support sections commute with etale-proetale direct image; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-pur-proetale-direct-image-global-evaluation: the existing node concerns Normalized derived global sections after pro-etale direct image; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-pur-ringed-derived-pushforward-linear: the existing node concerns Derived ringed-topos direct image preserves compatible central scalars; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-pur-ringed-triple-resolution-formulas: the existing node concerns Common-resolution formulas for two triple direct-image paths; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-pur-sequence-adjoint-resolution-shifts: the existing node concerns Resolution-normalized identification of the sequence-site derived adjoints; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-sf-compact-support-restriction-of-scalars: the existing node concerns Finite-level compact-support direct image commutes with restriction of scalars; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-sf-direct-image-scalar-restriction-cocycle: the existing node concerns Coefficient cocycle of the normalized pro-etale derived direct-image comparison; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-sf-exact-localization-derived-triangle: the existing node concerns Natural derived triangle of an exact localization sequence; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-sf-fixed-pair-derived-forget-comparison: the existing node concerns Derived forgetting of fixed pairs and right derived functors; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-sf-kinjective-derived-map-computation: the existing node concerns Computation of unbounded derived morphisms on arbitrary K-injective resolutions; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-sf-kinjective-replacement-triangulated: the existing node concerns K-injective replacement is an exact functor to the homotopy category; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-sf-native-adic-mayer-vietoris-triangle: the existing node concerns Derived Mayer-Vietoris triangle for native adic direct image; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-sf-native-weil-basic-comparisons: the existing node concerns Direct-image and open-extension comparisons in the native Weil realization; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-sf-normalized-derived-comparison-common-resolution: the existing result assumes a supplied invertible normalized comparison; the new lemma constructs a possibly noninvertible comparison without that assumption.

lem-sfb-exact-square-right-derived-unit vs lem-sf-normalized-derived-comparison-composition: the existing node concerns Composition of K-injective-normalized derived comparisons; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-sf-weil-verdier-dual-triangulated: the existing node concerns The Verdier dual of Weil complexes is a triangulated functor; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-sfb-cech-coefficient-derived-comparison: the existing node concerns Canonical coefficient comparison on the coherent Cech total; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-sfb-derived-direct-image-open-coherence: the existing node concerns Derived direct-image comparisons commute with open restriction and reassociation; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-sfb-identity-open-derived-adjunction-normalization: the existing node concerns K-injective normalization and derived adjunction at an identity open locus; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-sfb-kinjective-direct-image-open-word-model: the existing node concerns Simultaneous K-injective models and diagram descent for direct-image/open words; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-sfb-module-derived-compositor-coherence: the existing node concerns Identity and associativity of the normalized module derived direct-image compositor; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-sfb-ordinary-proetale-direct-image-plus-comparison: the existing node concerns Ordinary intrinsic pro-étale direct image: K-injective and bounded-below comparison; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-sfb-proper-open-tower-derived-unit: the existing node concerns Derived-unit resolution calculation in a proper/open tower; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-sp-levelwise-kinjective-tower-image: the existing node concerns Levelwise K-injective towers compute additive functors applied levelwise; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-trf-module-derived-restriction-resolution: the existing node concerns Module derived restriction on injective section complexes; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-weil-kinjective-total-derived-linear: the existing node concerns K-injective total right derived functors preserve scalar linearity; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-weil-pbc-constant-tower-pushforward-normalization: the existing node concerns Constant-tower direct image and limit normalization for identified ring sheaves; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-weil-pbc-derived-exchange-module-termwise: the existing node concerns K-injective representative of the module derived exchange mate; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-weil-pbc-derived-sections-pushforward: the existing node concerns Derived global sections via comparison pushforward; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-weil-pbc-exact-adjoint-tower-models: the existing node concerns Simultaneous exact-adjoint K-injective tower and normalized Roos models; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-weil-pbc-exact-square-derived-counit: the existing node concerns Counits in an exact square from normalization on K-injectives; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-weil-pbc-flat-restriction-derived-mate: the existing node concerns FlatRestrictionDerivedMate; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-weil-pbc-flat-ringed-diagram-restriction: the existing node concerns Flat coefficient restriction and normalized derived operations on module diagrams; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-weil-pbc-flat-scalar-tower-limit-square: the existing node concerns Flat scalar restriction and the normalized direct-image strict-limit square; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-weil-pbc-kinjective-exact-square-comparison: the existing result assumes U preserves K-injectives and concludes an isomorphism; the new lemma has no such hypothesis and gives a possibly noninvertible map plus exact-postcomposition universality.

lem-sfb-exact-square-right-derived-unit vs lem-weil-pbc-kinjective-fiber-triangle-comparison: the existing node concerns Unit-normalized derived comparison of K-injective mapping-fibre triangles; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-weil-pbc-kinjective-total-derived: the existing node concerns Enough K-injectives compute total right derived functors; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs lem-weil-pbc-tower-derived-evaluation-normalization: the existing node concerns Derived tower evaluation with its unit and counit normalization; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs prop-weil-pbc-derived-inverse-image-adjunction: the existing node concerns Derived adjunction of inverse and direct image on D^+; it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

lem-sfb-exact-square-right-derived-unit vs sk-def-sfb-finite-derived-functors: the existing node concerns Derived pushforward and pullback (finite coefficients); it does not assert exact-postcomposition universality together with the noninvertible unit comparison for arbitrary additive F,G and exact U,V.

