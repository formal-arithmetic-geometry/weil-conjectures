## Files written

- dag/nodes/sec-smooth-purity/lem-pur-supported-product-localization.json: statement; repaired split, retaining the exact statement and Lean record.
- dag/nodes/sec-smooth-purity/lem-pur-external-rhom-cone-pairing.json: statement; unsplit, no Mathlib match. This is the only new node.
- citations.json: verbatim statement extracts for every citation of every parent proof step.

## Attachments

None. I searched the slopmaster2 WeilConjectures tree by the item's blueprint tag, supportedExteriorProduct, supported localization, externalHom, and coefficient support. The localization files give localization and boundary results, not this exterior-product comparison. Kunneth/Comparisons.lean's externalHom is a field of HasKunnethComparisons with constructible finite-Tor hypotheses; it neither proves this ordinary global-Hom cone comparison nor applies to the item's arbitrary bounded-below complexes. The item's existing Sheaf stage-2 record is preserved, not treated as a finished project proof.

## WANTED

None. The local Stacks sources and the current blueprint suffice; the external pairing's cone refinement is explicitly agent-formulated, rather than attributed verbatim to Stacks.

## Faults and repair

This is the dedicated repair handoff in coord/returns/Q05.md (old head 4baef11dcb4b24c3d6e27d8bc3751383cf9bc93e). The old steps 4 (2044 characters) and 5 (2802 characters) hid generic arguments. I began from the current repository proof because the sandbox had no node or report. Its earlier proof, literature citations and Mathlib searches are retained; there were no previous sandbox searches to repeat.

The old step 4's flatness argument is now an invocation of the existing lem-sfb-open-closed-flatness, specifically its finite-ring small-etale closed-direct-image and open-extension clauses. New steps 4 and 5 retain the actual coefficient sequence, its constant-section comparison maps and stalk verification. No separate coefficient-flatness or elementary finite-product node was created. I initially searched for that candidate before finding and reusing the existing result; the real searches remain in searches.jsonl, and are not represented as searches for the new Hom lemma.

The old step 5's resolution-independent evaluation pairing and comparison with both coefficient cones are now the single generic node lem-pur-external-rhom-cone-pairing, used by new step 6. New step 7 keeps in the parent the substantive specialization: the pairing is the specified supported exterior product because the constant-support quotient maps and normalized adjunction counits agree. New step 8 then identifies the support triangles and their genuine boundaries. The old sign, second-variable and naturality arguments are retained as steps 9, 10 and 11, with references updated. All parent non-elementary steps are below 2000 characters; none was merely marked elementary to evade the return.

The statement is unchanged, as required. The existing stage-2 Lean record, source, unit/chapter, ancestry and maintainer fields are unchanged. No unit or chapter route is replaced. The current main-20261015 blueprint moves the ancestor into sk-prop-an; the item's historical unit is maintainer-owned and is preserved. The refinement still serves the same two support-triangle comparisons in paragraphs 1 and 3 of lem-pur-kunneth-supported.proof.md.

## Unfinished work

The new Hom-cone lemma is intentionally statement-only: proving/splitting that independent generic input is the next DAG task. No parent clause is delegated as a restatement. It has no supports, support localization or exterior-product invertibility assertion; it isolates the general exactness mechanism that the parent specializes.

## Review by Q05

I read the current item and its old proof, the complete Q05 return, the chapter/unit records, and the current main-20261015 lem-pur-kunneth-supported statement and proof. The ancestor compares two localization triangles and identifies the first supported map; it does not justify merely choosing an unspecified third component. The repair therefore retains the explicit evaluation normalization rather than using triangulated completion as a substitute.

For the item I read Stacks etale-cohomology.tex Tag 09XP (section-cohomology-support), including the injective restriction sequence and the construction of its derived boundary, and Tag 0F1E (remark-define-kunneth-map), including both adjunction-counit descriptions. I also read Tag 095L (lemma-ses-associated-to-open) and Tag 04FX (lemma-stalk-pushforward-closed-immersion), whose stalk cases control the coefficient sequence. For the new lemma I read sites-cohomology.tex section-hom-complexes (the Hom differential and lemma-compose, Tags 0A8X and 0A90) and section-internal-hom, including lemma-internal-hom (08J9), lemma-RHom-triangulated (08JC), and its explanation using termwise split sequences. Those passages supply the Hom/tensor and cone constructions, but do not state the complete external global-Hom transformation; the new node's source explicitly marks that refinement as agent-formulated. Its statement contains the evaluation transpose, the homogeneous Koszul formula, independence of resolutions, and the two triangle compatibilities so a future worker has a precise independent task. It introduces every scheme, coefficient, morphism and boundedness hypothesis, cites existing definition nodes, and contains no proof, proof dependencies or proof-origin claim.

I opened the statements cited in every step and checked the following uses.

1. Step 1 uses def-pc-base-change and def-weil-closed-immersion only for fibre products and their affine ideal descriptions. The equalities of the three extended ideals are written out. No theorem about immersion stability is silently substituted for either definition.
2. Step 2 uses the exact-functor clause (2) of lem-pc-derived-tensor-second-factor-functor with R=A and the actual triangle stated by lem-pur-support-restriction-triangle. There is no bounded-below requirement on the resulting tensor of global sections.
3. Step 3 uses lem-weil-pbc-dplus-injective-representative for the bounded-below injectives, lem-weil-pbc-open-closed-short-exact for the coefficient sequence, and lem-weil-pbc-extension-by-zero-adjunction for the Hom/restriction kernel. The injective computation is exactly clause (2) of lem-weil-pbc-right-derived-plus-injective. The two Hom definitions give the differential and K-injective convention, not an uncited exactness assertion.
4. Step 4 uses the open-closed sequence just stated. Its closed-support stalks use the finite-stalk formula, closed-immersion finiteness, and the constant-stalk theorem. Inverse-image stalks are exactly the comparison asserted by lem-weil-pbc-global-sections-stalk-comparison. Stalk conservativity applies to the resulting comparison morphisms. I corrected the old reference to a counit: the extension-by-zero definition gives the presheaf construction, whereas the named adjunction theorem supplies the counit; both are now cited.
5. Step 5 takes flatness from lem-sfb-open-closed-flatness, which explicitly allows our finite commutative A on small etale sites, with no quasi-compact-open hypothesis there. K-flatness of bounded flat coefficient complexes and their cones is exactly clauses (1) and (2) of lem-kun-kflat-criteria. The supported-product definition specifies theta, not its inverse; the step proves that theta is invertible here by its multiplication map on stalks, using lem-pod-etale-stalk-tensor-scalar and geometric stalk conservativity. Taking B=X proves the pulled-back S_D is flat, so the exact inverse-image result really can be followed by exact tensoring. This repairs the possible implicit assumption that exact inverse image alone proves preservation of flatness. The specified maps on the coefficient sequence are checked as well as the three objects.
6. Step 6 invokes precisely the new lemma's actual three-component cone and boundary assertion. Its bounded flat coefficient and bounded-below K,L,F hypotheses were all checked against steps 4–5 and the item's explicit hypothesis on F. There is no constructibility, finite Tor amplitude of K or L, or invertibility assumption.
7. Step 7 compares the new lemma's evaluation with def-pur-supported-exterior-product's specified C_i, e_i, theta and epsilon. The common quotient normalization and uniqueness of adjoints identify the maps before forgetting support. The third term uses the actual open-extension adjunction and the ambient/coefficient comparisons explicitly defined by def-pur-supported-localization-comparisons; it is on U times Y, not on P with an implicit ambient change.
8. Step 8 uses restriction-injectives for an etale open (open-immersion-etale supplies that hypothesis), the bounded-below injective derived-functor computation, and the extension-by-zero Hom adjunction. The complex-SES triangle lemma explicitly gives a natural connecting morphism, so the step identifies the support boundary rather than just some triangle. The final K-flat resolution is the flat-term resolution promised by lem-pc-kflat-resolution; it permits degreewise exact tensoring with direct-sum totalization.
9. Step 9 is a homogeneous differential calculation using only the tensor and derived-category definitions. I checked the two source differentials: the first shifted factor gives the identity comparison; the second gives the factor (-1)^deg(x). It is appropriately elementary.
10. Step 10 retains the second-variable construction, invokes the same coefficient sequence theorem, the new lemma's second-variable clause, and the SES/support-triangle identification. Its left tensor is the right tensor exact functor conjugated by the sign symmetry explicitly in def-kun-derived-tensor. The third ambient is X times V and the boundary sign agrees with step 9.
11. Step 11 invokes the new lemma's stated coefficient and open naturality and retains the degreewise formulas for supported sections. The derived-Hom convention and canonical K-flat model comparison justify passing these equalities to derived roofs. This proves naturality of the boundary diagrams as well as of the underlying objects.

I tested the new lemma when E or H is zero, for the triangle of an identity (whose cone is acyclic), for a coefficient shifted by one in either tensor factor, and for complexes concentrated in degree zero. These give respectively zero pairings, the zero cone term, the two stated Koszul shift conventions, and ordinary evaluation. No finite global dimension of A is assumed: boundedness/flatness concerns the coefficient E,H, not the arbitrary input K,L. For the parent I checked empty supports, B=C=X (empty U), C empty, and empty X or Y. The coefficient sequence then reduces to zero/identity maps and the stated support triangle has exactly the corresponding open ambient. Nonreduced closed subschemes cause no change to the stalk calculation and are not silently treated as disjoint closed components.

The whole-DAG and blueprint searches included evaluation/cones, external Hom, coefficient sequences, and tags 04FX, 095L, 08JC. I read lem-sfb-open-closed-flatness before deciding not to create its duplicate. The existing external-Hom thick reduction and beta nodes require constructible finite-Tor inputs; the item's K,L need not satisfy those hypotheses. The single-site tensor-Hom adjunction, Hom-triangulated theorem and double-Hom cone comparison do not assert the external global-Hom evaluation transformation with these three specified components. The new id was absent from the shared DAG. Mathlib was searched by the logged msearch command with LeanFinder, Loogle, grep, LeanSearch and a second LeanFinder phrasing. Hits concern module flatness, Tor naturality, generic connecting morphisms, scheme structure-module restriction or functor-category evaluation. Their displayed types do not state this constant-coefficient external global-Hom pairing and cone compatibility. LeanSearch returned a rate-limit error and is recorded as unavailable, never as a negative mathematical search.

## Not duplicates

lem-pur-external-rhom-cone-pairing vs prop-sf-dualizable: the existing node concerns dualizability of locally perfect constructible complexes, rather than evaluation of two arbitrary bounded-below inputs against bounded flat coefficients on two sites.

lem-pur-external-rhom-cone-pairing vs lem-sf-hom-triangulated: the existing node concerns exactness of a single internal-Hom bifunctor, without the external global-Hom pairing or compatibility of its specified components.

lem-pur-external-rhom-cone-pairing vs lem-sf-even-line-hom-shift: the existing node concerns a first-variable shift square for tensoring a coefficient dual with an even shifted line, rather than the two-variable external evaluation on cone triangles.

lem-pur-external-rhom-cone-pairing vs lem-coef-rational-bidual-triangle-compatibility: the existing node concerns the map to the double dual on one ringed site, not the external pairing of Hom objects from two sites.

lem-pur-external-rhom-cone-pairing vs lem-sf-rational-thick-evaluation: the existing node concerns a rational completed-coefficient thick-subcategory evaluation criterion, not ordinary constant-A external global Hom.

lem-pur-external-rhom-cone-pairing vs thm-coef-integral-verdier: the existing node concerns integral constructible Verdier biduality over completed coefficients, not this uncompleted Hom evaluation transformation.

lem-pur-external-rhom-cone-pairing vs sk-thm-sf-kunneth-verdier: the existing node concerns invertibility of constructible finite-Tor Kunneth-Verdier maps, whereas the new node asserts no invertibility and allows nonconstructible K,L.

lem-pur-external-rhom-cone-pairing vs lem-weil-duality-pairing: the existing node concerns duality evaluation and double-dual naturality with a dualizing object, not the four-input external global-Hom transformation.

lem-pur-external-rhom-cone-pairing vs lem-sf-double-hom-cone-comparison: the existing node concerns the explicit double-Hom endofunctor of one complex and one fixed I, not a bilinear pairing across two etale sites and its derived global sections.

lem-pur-external-rhom-cone-pairing vs lem-sf-etale-local-dual-interval: the existing node concerns local finite-projective dual models and Tor bounds, not external pairing naturality or cone compatibility.

lem-pur-external-rhom-cone-pairing vs lem-coef-integral-hom-reduction: the existing node concerns integral internal Hom under reduction of completed coefficients, not ordinary constant-A external evaluation.

lem-pur-external-rhom-cone-pairing vs lem-coef-rational-retract-evaluation: the existing node concerns extension of perfect evaluation to retracts, not a general two-site global-Hom pairing.

lem-pur-external-rhom-cone-pairing vs thm-sf-dual-perfect: the existing node concerns perfectness of a dual and invertibility of the coefficient-dual tensor comparison, not this external cone pairing without perfectness.

lem-pur-external-rhom-cone-pairing vs lem-sfb-finite-field-internal-hom-finiteness: the existing node concerns finiteness of finite-field constructible Hom, rather than construction and exactness of an external global evaluation map.

lem-pur-external-rhom-cone-pairing vs lem-sfb-constructible-internal-hom-continuity: the existing node concerns filtered-colimit continuity for constructible internal Hom, not external evaluation and its boundary squares.

lem-pur-external-rhom-cone-pairing vs lem-weil-pbc-extended-cech-completion-model: the existing node concerns an extended Cech model for derived completion, not external Hom evaluation.

lem-pur-external-rhom-cone-pairing vs lem-weil-pbc-ringed-derived-complete-elements-ideal: the existing node concerns the ideal of sections with vanishing localized Hom, not the external Hom transformation.

lem-pur-external-rhom-cone-pairing vs lem-weil-pbc-ringed-internal-hom-exact-restriction: the existing node concerns single-site Hom adjunction, exactness and slice restriction, not the external global-Hom pairing across a:P to X and b:P to Y.

lem-pur-external-rhom-cone-pairing vs lem-fin-lisse-field-dual: the existing node concerns lisse field-coefficient duality, not arbitrary bounded-below constant-A Hom evaluation.

lem-pur-external-rhom-cone-pairing vs lem-weil-integral-constructible-triangulated: the existing node concerns closure of integral derived-complete constructibles under triangles, not ordinary external global Hom.

lem-pur-external-rhom-cone-pairing vs lem-pod-coefficient-dual-perfect: the existing node concerns perfectness under coefficient duality, not external global-Hom evaluation and cone compatibility.

Additional concept overlaps: lem-trf-external-hom-thick-reduction concerns the sheaf-valued beta map on finite-Tor constructible inputs; prop-trf-external-hom asserts its invertibility in that domain. Neither covers arbitrary K,L or the global-Hom transformation here. def-pur-supported-exterior-product specifies a pairing for supports, but does not state its coefficient-cone comparison. Those facts cannot replace the generic new lemma without either dropping hypotheses or arguing in a cycle.
