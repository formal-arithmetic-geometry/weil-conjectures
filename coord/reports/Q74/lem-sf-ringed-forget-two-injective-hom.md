# Q74: lem-sf-ringed-forget-two-injective-hom

## Files written

- dag/nodes/sec-six-functors/lem-sf-ringed-forget-two-injective-hom.json: statement, split into eight steps using existing nodes; no Mathlib match for the whole item.
- citations.json: one entry for each of the 19 step/node citations, quoting that node's statement verbatim.
- searches.jsonl: actual msearch output log; the six new queries are appended to the item's existing Q48 searches.

No new nodes and no new Mathlib leaves. prepare.py is a sandbox-only preparation script, not a delivery file.

## Attachments

None. I searched the live WeilConjectures source for the blueprint tag and for derivedHom/two-injective constructions. ProEtaleWeilSheaf.derivedHom (WeilSheaf/DerivedHom.lean:111) is a definition of the native chosen-representative functor. It does not prove the item's general ringed forgetting comparison, source-resolution invariance, or both-variable naturality. The live BifunctorHom.lean definitions are likewise construction material, not an attachment of this theorem.

## Literature wanted

WANTED: none for this split. The pre-existing action-site lemma records its own missing exact non-SGA reference; I use its public statement, not an asserted external theorem about twisted sites.

## Statement error: STATEMENT-DISPUTED

The imported assertion that the standard-sign Hom complex is "exactly the native model" is false at the chain level. The live CochainComplex.BifunctorHom.d (WeilConjectures/Algebra/Homology/BifunctorHomComplex.lean:54-70) and bifunctorHomObj_d_π (146-151) use

(d_nat f)^p = (-1)^p (d_I f^p - f^{p+1} d_J),

whereas the item specifies d_std(f)^p = d_I f^p - (-1)^n f^{p+1}d_J. For an explicit small case over Q, take J to be Q in degree 1, and I the contractible complex Q --id--> Q in degrees 1 and 2. These are K-injective complexes (J is a shifted injective Q-module; I is contractible). For n=0 and f^1=id, the standard differential has component +id and the native differential has component -id. Thus the identity on product components does not identify the complexes.

I repaired only this identification: native and standard complexes are canonically chain-isomorphic by (S^n f)^p=(-1)^(np)f^p. Step 8 checks both coefficients and S squared equals one, with no division or characteristic restriction. Naturality and contragredient equivariance are checked as well. The derived internal-Hom assertion and every hypothesis are retained; the correction makes the intended native derived identification explicit. I added def-sf-native-weil-derived-framework as a statement dependency to fix the coefficient interpretation. I did not cite def-sf-derived-weil-category-and-operations: its dependencies already go through the parent native closed-forgetful package and would make this split circular.

The imported blueprint ancestry is maintainer-created and has no blueprint id: tools/blueprint_refs.py ancestor prints None. I retained that null ancestor and its existing concrete from.place, and recorded the concrete cor-coef-verdier-weil-equivariance proof paragraph in split_report.blueprint. Searches of the whole imported blueprint for "two K-injective", "RHom well defined", and "internal Hom", and of DAG tags 0A95 and bifunctorRHom, found no duplicate of this general comparison. The broad internal-Hom search includes finite-coefficient/pullback/constructible results, not this item.

## Unfinished work

None in the item's split. Existing dependencies remain their own stage-1 items. No Lean was written, no compiler or Lake command was run, and the shared repository and launcher were only read.

## Not duplicates

No new nodes were created. The existing lem-pur-rhom-well-defined is the general two-variable source/target quasi-isomorphism invariance needed here; its statement is reused directly. lem-sf-weil-derived-hom-single-resolution covers a source in degree zero and a bounded-below target, so it does not supply this unbounded, arbitrary-source comparison. The two homotopy and exact-derived-functor Mathlib nodes are cited rather than recreated.

## Review by Q74

I read the current six-functors chapter, the sk-prop-sf-biduality-general unit and the concrete main-20261015 cor-coef-verdier-weil-equivariance proof. This item supplies the internal-Hom Frobenius comparison used in that paragraph and does not replace its geometric biduality argument. I read Stacks sites-cohomology.tex, lemma-RHom-into-K-injective (0A94), lemma-RHom-well-defined (0A95), and section-internal-hom (08J7), including the construction with an arbitrary source and a K-injective target. I read derived.tex, lemma-K-injective (070I) and lemma-adjoint-preserve-K-injectives (08BJ). For the native convention I read the live WeilSheaf/DerivedHom.lean, CategoryTheory/DerivedCategory/BifunctorHom.lean, Algebra/Homology/BifunctorHomComplex.lean and WeilSheaf/TateTwistCohomology.lean's ihom_obj_str. The last definition really gives conjugation by the target action and inverse source action. No SGA source is used.

Step 1 uses def-pur-derived-internal-hom for the representative model and lem-pur-rhom-well-defined for the actual precomposition quasi-isomorphism; def-weil-abstract-derived-category inverts it. I opened all three statements. In 0A95 the source need not be K-injective or K-flat, and the target map is id_I between K-injectives. This checks the often missed distinction between internal sheaf Hom and global Hom.

Step 2 uses precisely the Hom bijection and the homotopy-equivalence consequence in lem-weil-pbc-kinjective-hom-derived. It does not assume a chain comparison is unique. It is its homotopy class which is unique. I checked the two explicit chain homotopies against def-pur-hom-complex: source homotopies use (-1)^n f h and target homotopies use h f. Their differentials cancel the mixed terms. Uniqueness of homotopy classes gives the cocycle and all naturality claims on arbitrary derived morphisms.

Step 3 uses lem-sf-exact-functor-derived-triangulated only for the induced termwise functor, which its statement asserts. Additivity and exactness are hypotheses of the item. Preservation of K-injectives is also an explicit hypothesis at this point. The two UI/UJ objects therefore meet def-pur-derived-internal-hom's representative requirements without any assumption that U commutes with a chosen replacement functor.

Step 4 uses def-pur-hom-complex's product, differential and componentwise functoriality. The product comparison is available because U preserves the actual countable products, which are small in the stipulated universes. I wrote its components and checked the differential against each product projection, using the given natural sheaf-Hom comparison and additivity. Product universal properties and this two-term calculation are elementary; no extra product-exactness theorem is being used.

Step 5 uses def-pur-hom-complex for the componentwise b f a maps, lem-pur-rhom-well-defined for their quasi-isomorphism cases, and def-weil-abstract-derived-category to invert those maps. I wrote the naturality equation before localization and explained explicitly why it continues to commute after inversion. Step 2 accounts for chain homotopies and representatives of arbitrary derived maps. Thus this is naturality, not only a collection of objectwise isomorphisms.

Step 6 opens and uses the whole relevant statement of lem-sf-twisted-action-ringed-site: the small ringed presentation, product-creating exact forgetful functor, the exact additive LEFT adjoint Ind, and the natural conjugation sheaf-Hom. I checked the orientation against lem-weil-pbc-right-adjoint-preserves-kinjective: its u is U and its v is Ind, so it is exactness of Ind that is needed. This is the only new hypothesis check for the Frobenius specialization. These are statement citations, not appeals to proofs hidden in those nodes. The latter generic theorem is declared as an off-unit tool in split_report, as is the generic 0A95 node. The Mathlib Hom-bijection and exact-functor leaves need no route exception.

Step 7 reads def-sf-native-weil-derived-framework for the precise coefficient sheaf and fixed-pair category. The elementary finite-basis/compositum argument checks equality with this item's finite-subextension coefficient sheaf, including the local and quasi-compact conditions. No constant discrete coefficient substitution is made. The actual chosen-representative native definitions were read, not inferred from their docstrings. Existence of resolutions is explicitly supplied by def-pur-derived-internal-hom, and full faithfulness by lem-weil-pbc-kinjective-hom-derived, so the source replacement equivalence is justified. The conjugation structure is supplied by the action-site statement used here and in step 6.

Step 8 uses only the signed differential explicitly stated in lem-sf-bifunctor-homotopy-exact and the standard differential of def-pur-hom-complex; it takes no triangulated conclusion from that lemma. I checked the coefficient of each of d_I f and f d_J. Scalar signs commute with every map and action in question. This corrects the one error found in the imported statement.

I checked B1-B10 against the files: there are no new unsplit statements or invented Mathlib leaves; recorded new searches are exactly the six calls in searches.jsonl, all with actual available responses. The leanfinder service was queried in two distinct phrasings. I read the relevant Mathlib SheafHom.lean, RightDerived.lean and DerivedCategory/ExactFunctor.lean hits; they provide ordinary sheaf Hom, bounded-below resolutions or termwise derivation, not this comparison. Old Q48 search entries are retained as required by the brief and are not claimed as my own calls.

For C1-C8 I opened every cited statement, generated a verbatim statement quote for every use, checked that no cited dependency reaches this item, and declared the off-unit generic tools. For D1-D5 the argument is eight explicit assembly/calculation steps, not clauses moved into children; there are zero new nodes. For E1-E7 I checked the hypotheses and tested zero source, zero target, the empty site, identity U, identity resolutions, unbounded representatives, negative indices, characteristic 2, and trivial Frobenius. The sign correction becomes the identity in characteristic 2 and still works for negative n,p. With trivial Frobenius, the action site is the ordinary Z-action module category, and the comparison still uses exact orbit induction; it does not mistakenly identify its derived category with fixed pairs after derivation. Every step has fewer than 2000 characters, and none hides a separate non-elementary comparison lemma. No remaining uncertainty about a hypothesis was resolved by strengthening the statement.
