# Worker report: lem-per-qbar-middle-tstructure

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-qbar-middle-tstructure.json`: split statement, ten proof steps; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-qbar-dual-recollement.json`: new statement-only node; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-qbar-generic-duality-model.json`: new statement-only node; no Mathlib match.
- `citations.json`: verbatim statement excerpts for every step/node pair.

The source extracts and scripts in this sandbox are working material only. No Lean was written, compiled or built. No shared repository, source checkout or launcher was modified.

## Attachments

None. I searched the project Lean for the item tag and perverse terminology and read `SixFunctors/Etale/Perverse/Basic.lean`, `Operations.lean` and the relevant curve-perverse declarations. Basic defines conditions and their shift/isomorphism invariance. Operations has sorry declarations about functors. `DeligneLaumon/AffineLine/Perverse.lean` concerns the special curve classes, not the arbitrary-dimensional adic statement here. None states the item exactly without sorry. Searches for a lisse dualizing object and recollement also yielded no exact project declaration for either helper.

## WANTED

None. BBD, Bhatt--Scholze, ILO and the Stacks source used below are present locally.

## Issues in the inherited material

The item's statement is unchanged. It already explicitly replaces the obsolete dual in `def-per-support-condition` by the arbitrary-field relative dual of `lem-per-qbar-arbitrary-field-duality`. That qualification is essential: the older definition points to `def-trf-dualizing-complex`, whose domain is finite coefficients over the fixed algebraic closure of a finite field. Step 1 retains the item's qualification; I did not edit the definition node.

BBD 4.0 explicitly imposes a finiteness assumption on field Galois cohomology for its traditional adic category. It cannot alone justify the arbitrary-field statement for this project's categories. The proof is consequently marked `proof_origin.by = agent`: it writes BBD 1.4.10's two-fibre proof objectwise, using the existing arbitrary-field adic duality and heart nodes and the two stated structural inputs. It does not silently identify BBD's old inverse-limit categories with discrete Qbar-ell sheaves. The ILO normalized potential-dualizing-complex calculation, used by Bhatt--Scholze 6.7.20, handles the local model over arbitrary fields.

The unit is the perverse/Fourier unit; the item is a helper of its Artin--Gabber node, not its key statement. I read the chapter and unit records, the current main-20261015 Artin--Gabber proof and unit text, and the reviewed replacement proof of the ancestor. This split supplies the t-structure and extension closure invoked in ancestor Step 2 and duality in Step 3. It leaves the unit binding and route unchanged and does not revive the ancestor's invalid generating-block argument.

## What remains

The two new nodes deliberately have statements only and no proofs or proof dependencies, as required for a one-level split. Their proofs are future DAG work. The item's full proof uses their statements, not their future proofs. Nothing else in the assigned split remains unfinished.

## Not duplicates

lem-per-qbar-dual-recollement vs prop-sf-open-closed-triangle-all-stages: the latter states one localization triangle and a particular Hom vanishing; the new node supplies both adjoint triples, both localization triangles, restriction/fully-faithfulness identities and dual restrictions on the exact arbitrary-field adic common-stage categories.

lem-per-qbar-dual-recollement vs prop-weil-open-closed-recollement-adjunctions: the latter gives only two adjunctions and two units for ambient finite-coefficient ordinary categories, not the adic rational categories or extraordinary restriction.

lem-per-qbar-dual-recollement vs def-weil-open-closed-recollement: the latter defines one candidate triangle at finite torsion coefficients and explicitly asserts no existence theorem.

lem-per-qbar-dual-recollement vs lem-cbc-open-closed-recollement: the latter concerns bounded-below finite coefficients on the etale site, not rationalized derived-complete common-stage coefficients or dual restrictions.

lem-per-qbar-dual-recollement vs lem-per-qbar-ordinary-adjunction: the latter supplies ordinary pullback/direct-image adjunction only, not the other adjoints, localization triangles or dual-restriction identifications.

lem-per-qbar-dual-recollement vs lem-per-qbar-arbitrary-field-duality: the latter supplies dual anti-equivalence and duality for direct image, not the open/closed recollement and pullback/extrordinary-restriction identities.

lem-per-qbar-dual-recollement vs lem-a1-qbar-open-closed-cohomology: the latter restricts its schemes to smooth curves over perfect fields and their indicated opens/closed complements; this input is needed recursively on arbitrary-dimensional schemes over arbitrary fields.

lem-per-qbar-dual-recollement vs prop-functor-package: the latter is over the fixed algebraic closure of a finite field; it does not have the arbitrary-field domain of this item.

lem-per-qbar-generic-duality-model vs lem-per-qbar-arbitrary-field-duality: anti-equivalence does not itself state the generic shifted rank-one local form or its lisse-cohomology degree calculation.

lem-per-qbar-generic-duality-model vs lem-per-adic-heart-pullback-fibres: finite lisse stratifications are already available there and are reused; the new content is the local normalized dualizing object and its degree-reversing cohomology formula.

lem-per-qbar-generic-duality-model vs lem-per-adic-lisse-cohomology-calculus: that node gives tensor exactness and the coefficient dual of a lisse sheaf, but no generic relative dualizing object or dual of a bounded lisse-cohomology complex with its dimensional shift.

lem-per-qbar-generic-duality-model vs lem-zl-lisse-cohomology-derived-dual: the latter computes the coefficient dual over the fixed algebraic closure of a finite field; it gives neither the arbitrary-field generic dualizing-object model nor the relative 2d shift.

lem-per-qbar-generic-duality-model vs cor-pur-adic-and-rational-smooth-dualizing-complexes: the latter assumes smoothness over the fixed finite-field algebraic closure, whereas the generic pieces here need not be smooth over an imperfect ground field.

lem-per-qbar-generic-duality-model vs lem-a1-qbar-curve-duality: the latter concerns dimension-one smooth schemes over perfect fields; it does not cover the induction's arbitrary-dimensional and possibly nonreduced schemes.

Neither helper is a restatement or a clause of the item's t-structure conclusion. Neither asserts orthogonality, existence of perverse truncations, boundedness of the perverse structure, or extension closure. All of that is proved in the item. Neither helper depends on perverse-class definitions.

## Review by Q06

I read BBD 1.4.9--1.4.10, including its octahedron and four restriction calculations; 2.2.10--2.2.19 concerning constructibility refinements and rational coefficients; and 4.0, including the field-cohomology restriction and support formula. I read Bhatt--Scholze 6.7.2, 6.7.6--6.7.7, 6.7.19--6.7.20, 6.8.14 and 6.8.15. For the generic helper I additionally read ILO XVII 2.4.4.1, 5.1.1 and the proof of 6.2.2.1: after reduction and shrinking to a connected regular open, the potential dualizing complex is the coefficient unit twisted by delta(eta) and shifted by 2 delta(eta). Here delta(eta) is trdeg over k, hence the dimension d of that component. This uses regularity of the reduction, not generic smoothness over k. The rank-one orientation sheaf in the new statement avoids imposing any extra trivialization. Passing the compatible finite-level rank-one systems to completed integral coefficients, rationalization and a common finite field gives exactly the asserted local form. Its cohomology formula is the locally finite-projective linear-dual calculation with that 2d shift. It is stated separately rather than hidden behind the word “standard”.

For the recollement helper, the operations are explicitly those in the item's category. The cited Bhatt--Scholze results give constructible direct image, compact support, exceptional pullback and duality in the required excellent, ell-coprime setting. A finite-type scheme over any field is excellent; its open/closed immersions are separated and finitely presented. At finite coefficients the open/closed adjunction maps give localization; reduction, derived completion, rationalization and common finite stages preserve these triangles and adjunction identities. This is the smaller structural statement isolated in the helper, not a citation of a mere definition of recollement. I corrected the draft source reference “Lemma 6.7.3” to 6.7.2: 6.7.3 is a remark. No prohibited SGA source is used.

I opened the statement of every cited node. In Step 1, the shift and biduality assertions are actually in arbitrary-field duality; the class definitions give the sign convention. Step 2 uses the heart node's constructible nonzero-fibre locus and exact restriction formula, and only the first inequality of the dimension node. Applying it to each locally closed stratum gives equality between the dimension of the stratum and its closure; the reverse inequality and finite-union maximum are elementary topological chain arguments written in the step. This handles closed support, not just the stalk locus. All strata are finite-type k-schemes, so that inequality applies. The recollement helper explicitly gives cohomology restriction. Step 3 uses precisely its two dual-restriction identities, with index -n.

Step 4 uses the generic helper's actual degree formula: r corresponds to a = -r-2d, giving the lower cutoff a >= n-d, not n+d. The heart node provides conservative fibres and bounded ordinary truncations. The sum-of-open-extensions comparison for a finite disjoint union is verified on those fibres, so no unproved identification of Hom categories is assumed. Step 5 sets up induction for all schemes of smaller dimension before applying it to the reduced closed complement. Its generic open is chosen for the two given objects, not assumed to carry a fixed stratification stable under every direct image. The two Hom groups vanish by ordinary orthogonality and the induction hypothesis, respectively; the helper explicitly has the adjunctions required to identify them. The exact Hom sequence is justified using the existing covariant Hom-exactness node after the exact dual anti-equivalence, so I do not take contravariant Hom exactness from a node which states only the covariant case.

Steps 6 and 7 use the existing Verdier-axioms theorem, whose statement explicitly includes cones and octahedra on the common-stage category. Ordinary truncations on the lisse open retain lisse cohomology, and closed perverse truncation is available by induction, not by assuming this item. I checked the domains and order of both fibre maps. The octahedron has triangle Ri_* C_Z -> B -> Rj_* B_U. Its four restrictions give j^* A = A_U, i^* A = tau_Z^{<=0} i^* K', j^* B = B_U and i^! B = C_Z, exactly as needed in Steps 2--3. The vanishings i^!Rj_*=0 and j^*Ri_*=0 are in the helper's statement, not inferred from a definition.

Step 8 takes independent ordinary upper bounds b for K and c for DK; arbitrary-field duality explicitly puts DK in the bounded constructible category. The inequalities b+e and -c-e are then immediate support bounds. Step 9 proves the right orthogonal characterization rather than claiming it is an axiom: in the truncation triangle the vanishing assumption kills A -> K, and Hom(A,B[-1])=0 kills id_A by the exact sequence, so A=0 and K is isomorphic to B. The signs of the shift were checked. Step 10 is exactly the existing abstract extension-closure Mathlib leaf applied after the t-structure has been proved.

I checked small cases: the empty scheme (all fibres and complexes zero), a point over an arbitrary field (d=0, ordinary t-structure), a rank-one lisse sheaf on a dimension-d smooth scheme shifted by d (both bounds zero, dual shift -2d correct), a punctual sheaf on a positive-dimensional scheme, and components of unequal dimensions (different local ordinary cutoffs). Nonreduced schemes are allowed because the generic local model is on their etale/pro-etale coefficient category and makes no regularity claim about their structure sheaf. Over an imperfect field a purely inseparable zero-dimensional component still has d=0 and a rank-one degree-zero relative dualizing object; no generic-smoothness hypothesis was introduced.

The Mathlib searches were run with msearch.py and read as returned. Each node has a natural-language semantic search, Loogle, grep, LeanSearch and a second semantic phrasing. There were no relevant matches; standard derived t-structures, ordinary sheaf adjunctions and topological density do not state either helper. The lisse/dualizing grep had only unrelated text hits, not an adic dualizing-complex theorem. The item retains the prior worker's searches and appends this run's searches. I searched the whole DAG, blueprint and project Lean before creating either helper and compared the candidates listed above. Every citation quote was copied from the node's statement; no quote was manufactured from its proof or source. All ten proof steps are under 2000 characters, and none hides an additional local comparison beyond the two explicit helper statements. B1--B10, C1--C8, D1--D5 and E1--E7 have been checked against these concrete statements and sources. Server check_dag and review_split passed before the final delivery dry run.
