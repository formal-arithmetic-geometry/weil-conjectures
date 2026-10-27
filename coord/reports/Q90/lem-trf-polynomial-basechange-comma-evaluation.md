## Files written

- dag/nodes/sec-trace-formula/lem-trf-polynomial-basechange-comma-evaluation.json — statement, split into six proof steps using existing nodes; no Mathlib match for the whole item.
- citations.json — verbatim statement excerpts for all six step/node citations.
- searches.jsonl — authentic msearch.py output records for the item; existing upstream search records in the item are retained.

No new nodes or Mathlib leaves were created. The sandbox was initially empty of node files or reports.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and polynomial/comma/tensor notions, and checked related lean/Sheaf references. No project declaration states this item with every clause. The existing polynomial-top theorem supplies only its polynomial-target input, not this comma equivalence and augmentation comparison.

## WANTED

None.

## Problems and corrections

The item previously had no proof. Its statement and statement dependencies are retained verbatim. Stacks cotangent.tex, 08QW (lemma-triangle-compute-lower-shriek), case i=3, identifies the comma category and coefficient presheaf, but prints C_{Qbar/C} where the required category is C_{Qbar/B}. The item already corrects this typo; the proof uses D_H (polynomial B-algebras augmented to H), followed by composition with delta. This is a source typo, not a new statement dispute.

The important additions are the morphism equation alpha'=alpha h, its equivalence to gamma'=gamma q, and the identification j(b_W)=a. The last identity fixes the actual augmentation, beyond merely identifying a derived-colimit object. No flatness, polynomiality of C, or extra coefficient condition is inserted.

## Unfinished work

None at this stage. Proofs of the cited existing non-Mathlib nodes remain their own items. No Lean was written or compiled.

## Review by Q90

I read the worker contract, the three blueprint levels in SETUP.md, GOAL.md, the chapter and unit records, the current main-20261015 unit and locality-ancestor proof, and delivery-errors B–E in full. This item is an existing auxiliary cotangent input; its inherited blueprint provenance is retained, and this split does not replace a unit-level step. I read cotangent.tex at 08QW, case i=3, including the coefficient formula and the mistaken subscript, and the full 08QV proof and statement. I also read sites-cohomology.tex 08PG/08PH for the bar-model and reindexing conventions. No SGA source is used.

For Steps 1 and 2 I opened lem-weil-pbc-algebra-tensor-pushout-universal-property and read all three clauses. Its statement supplies a map on tensor products, its pure-tensor formula, and uniqueness from its two factor restrictions. Applied over P with the algebra maps Q→H and B→H, these give exactly alpha(q tensor b)=gamma(q)b. In Step 2, the underlying algebra morphisms reverse direction: Q'→Q gives T_U'→T_U. Substitution on pure tensors gives alpha'=alpha h if and only if gamma'=gamma q; tensor uniqueness proves the converse. No lemma about a different comma category is being substituted. The existing node is a Mathlib leaf, so this off-unit algebra input is a permitted generic tool. I read its productMap and ext source declarations as well.

Step 3 uses only the explicitly defined categories and precomposition: delta alpha equals the original augmentation, on maps as well as objects. No hidden sheafification or general inverse-image theorem is required on these identity-cover sites. It has no theorem citation.

For Step 4 I opened lem-trf-derived-colimit-bar and read its entire statement, including the canonical chain formula, identity/composition laws and natural-transformation homotopy clause. These are exactly the assertions used to get a derived isomorphism from mutually inverse reindexings, also when skeletons give only an equivalence. Its smallness hypothesis holds because the item chooses a common bound and small models. Its coefficient ring is arbitrary commutative R, as here; the coefficient map is the identity on K(uU). The cited theorem gives the derived object and the actual canonical map, not just an ordinary colimit comparison.

For Steps 5 and 6 I opened lem-trf-cotangent-lower-shriek-polynomial-top and read its statement. It explicitly specifies the augmentation as reindexing followed by the arrows from the identity-augmented polynomial target. Thus Step 5 uses the node's statement, not an unnamed feature of its proof. The same bar node gives the degree-zero generator formula. I checked that b_W is opposite to alpha, that j sends its domain to V and its codomain to uU, and hence that G(b_W)=K(a). Both chain maps vanish in every negative degree, so this proves equality of the augmentations. Step 6 instantiates the cited theorem with C there equal to H here, F there equal to j^{-1}K here, and the same A, B, R. Its polynomial hypothesis is exactly H=B[E]; it imposes no condition on the original C. The specified augmentation is therefore an isomorphism in D(R), hence represented by a quasi-isomorphism. Naturality follows from the displayed generator maps.

I tested empty generator sets (including H=B), infinite bounded variable sets, zero coefficient ring, zero presheaf, identity ring maps, and a non-flat map such as Z→Z/2Z. All constructions are valid: the tensor universal property has no flatness hypothesis and the polynomial-top theorem has none. If B is the zero ring, compatible targets and tensor maps are still covered by the same formulas. C need not be polynomial: delta can land in an arbitrary B-algebra, and only H enters the polynomial-top application.

The searches were run with the required msearch.py command, in two semantic phrasings and with Loogle, LeanSearch and source grep. I read the hits, including Presentation.tensorModelOfHasCoeffsEquiv (Core.lean:207), TensorProduct.toIntegralClosure_mvPolynomial_bijective (IntegralClosure.lean:128), and lanEvaluationIsoColim (Functor/Flat.lean:302). They concern algebra tensor models, integral closure, or ordinary Kan extensions, respectively; none states the item. The whole-DAG and blueprint searches located the already existing tensor-pushout leaf; using it avoids an unnecessary new lemma. No new statements require duplicate comparisons. Every non-elementary input is a cited node and every citation has a verbatim statement excerpt in citations.json. No step exceeds 2000 characters; the elementary steps are explicit identity, restriction and generator calculations, with the non-elementary tensor/bar/polynomial inputs separately cited.
