# Q90 stage-1 delivery

Item: lem-per-normalization-field-extension-homeomorphism.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-normalization-field-extension-homeomorphism.json: statement, split; unchanged statement, eight proof steps following Stacks 0C3N.
- dag/nodes/sec-deligne-laumon-a1/lem-per-reduced-total-fractions-field-extension.json: statement, unsplit; no Mathlib match. This is the ambient-ring comparison used by the proof, with no assertion about normalization or universal homeomorphisms.
- citations.json: one verbatim quote for every cited node in every step (31 entries).
- searches.jsonl: actual msearch records. work.py is a sandbox-only writing aid, not a project file.

One new node, zero Mathlib leaves.

## Attachments

None. Searched WeilConjectures/ in the read-only slopmaster2 source by the exact blueprint id and by normalization, field extension, homeomorphism, and normalization/base-change combinations. Read WeilConjectures/Mathlib/AlgebraicGeometry/Normalization.lean and the relevant Frobenius declarations. The former proves existence, finiteness, birationality and related integral-scheme normalization facts; neither source declares the present arbitrary-field comparison. The finite-field power endomorphism theorem in AlgebraicGeometry/Morphisms/Frobenius.lean is narrower than the needed ring-map criterion. Master was also searched for the exact item id; its declarations are not used as evidence of finished proofs.

## WANTED

None. All sources used are present.

## Audit and corrections

The sandbox initially contained only brief markers, with no node, report, searches or interrupted delivery process. I copied the current repository item into the sandbox. Its statement is correct as written; it is the integral finite-type specialization of Varieties Tag 0C3N, label lemma-normalization-and-change-of-fields. There is no statement dispute and no change to the unit or chapter route.

The existing reduced-algebraic-normalization-field-change node gives an isomorphism only for separable extensions. It must not be cited for the universal-homeomorphism assertion for inseparable extensions. The proof instead uses its separable conclusion after the finite-coefficient/Frobenius reduction of the source. A second possible error was to treat the base change as integral or reduced: the proof retains the reduced total quotient ring, all its components, and the nilpotent kernel. A third was to claim an exponent for every element of an infinite extension; step 6 chooses it for a specific finite coefficient set only.

The new node is statement-only, not a relocated normalization theorem. Its content is that reduced scalar-extension maps preserve regular denominators, induce injective maps on total quotient rings, and give the indicated nil-kernel tensor map. These assertions use the behavior of minimal primes under flat scalar extension, beyond merely naming a localization. An eventual proof can use flat going-down and the reduced Noetherian total-fraction decomposition: minimal primes contract to minimal primes; regular elements avoid all such primes; nilpotent elements are precisely the kernel of reduction; localization then gives the displayed map and its kernel. The one-line compatibility statements belong with these canonical maps.

## Searches and blueprint

Read stages/1-dag.md, the three blueprint levels in SETUP.md, coord/brief-stage1.md, coord/delivery-errors.md B--E, GOAL.md and coord/dag-sync.md, and the item's chapter and unit records. Read the current main-20261015 ancestor text at sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.md. This is an auxiliary algebraic-geometric input to the regular-curve trace below that ancestor, not a new perverse-sheaf proof route. The existing blueprint.from place is retained and made explicit in the split report; the new node prepends the item to via.

Before creating the new node, searched the entire DAG by 0C3N, normalization and field extension, total quotient/fraction rings, nonzerodivisors and field extension, and all the other relevant source tags. Ran blueprint_refs.py searches for normalization, normalization field extension homeomorphism, total ring of fractions, fractions, reduced total fractions field, 035P and 0BRA; no blueprint node states the new ambient-ring lemma. Existing total-fraction decomposition, componentwise normalization charts, separable normalization comparison, separable-first fields, transcendence basis and power-generated spectrum nodes were opened and reused.

Ran msearch.py for the item and new node using LeanFinder (two phrasings each), Loogle, grep and LeanSearch. The exact queries and actual hit summaries are in the JSON and searches.jsonl. The Loogle query containing Algebra.TensorProduct was rejected as an unknown identifier; the corrected TensorProduct query ran and returned rank lemmas. No absence conclusion is based on the rejected query. Read the nearest relevant Mathlib hit, TensorProduct.toIntegralClosure_injective_of_flat, at Mathlib/RingTheory/Smooth/IntegralClosure.lean:39--56: it concerns integral closure inside an unreduced tensor product and does not identify the reduced total quotient rings. Other hits concern rank, localization or relative-normalization universal properties. None gives this item or the new node by one-line specialization. The item's inherited search records from its creation are retained.

## Not duplicates

lem-per-reduced-total-fractions-field-extension vs lem-per-normalization-field-extension-homeomorphism: the former constructs ambient reduced total-quotient ring maps and proves their injectivity/nil-kernel properties; the latter constructs a normalization comparison and proves it universally homeomorphic, using finite coefficient descent and Frobenius in addition.

lem-per-reduced-total-fractions-field-extension vs lem-weil-pbc-reduced-algebraic-normalization-field-change: the existing node describes normalization and its comparison for separable extensions; the new node applies to arbitrary field towers and gives maps between ambient quotient rings, without an integral-closure or normalization assertion.

lem-per-reduced-total-fractions-field-extension vs lem-trf-normalization-inseparable-base-change: that node assumes two finite purely inseparable extensions and geometric normality of a previous normalization, and concludes a normalization isomorphism plus a closed-subscheme assertion; the new node assumes no geometric normality and makes no normalization claim.

lem-per-reduced-total-fractions-field-extension vs lem-weil-pbc-reduced-noetherian-total-ring-fractions: that node decomposes one reduced Noetherian total quotient ring into fields, with no scalar-extension maps or nil-kernel tensor map. It is reused rather than duplicated.

lem-per-reduced-total-fractions-field-extension vs lem-weil-pbc-total-fraction-fiber-decomposition: that node localizes an arbitrary algebra at the nonzerodivisors of a fixed reduced base; it does not compare reduction and nonzerodivisors after extension of the coefficient field.

## Tool uses requested

The split_report lists generic tools from other units needing reviewer acceptance: lem-weil-pbc-reduced-noetherian-total-ring-fractions supplies the product of component fields; lem-weil-pbc-reduced-algebraic-normalization-field-change supplies restriction to opens and the separable comparison; def-weil-pbc-reduced-normalization specifies the same componentwise object as in the item; lem-pur-power-generated-spectrum-homeomorphism supplies the general 0BRA criterion. These are algebraic-geometric tools used inside the source proof, not a replacement of any unit-level sheaf-theoretic step. No top-level tool_uses or reviewed field was written.

## Review by Q90

I read Varieties Tag 0C3N (varieties.tex, label lemma-normalization-and-change-of-fields, including its entire proof). I checked the new node against its second proof paragraph, which explicitly identifies the map out of the tensor product of the old total fraction ring and states that its kernel consists of nilpotents. The tower maps and localization compatibility are the same fraction construction, with regular denominators preserved under the flat field extensions. I also read Fields Tag 030K, label lemma-separable-first, and Algebra Tag 0BRA, label lemma-p-ring-map. I read the current ancestor and the item's parent's normalization step to check why this lemma is needed.

Step 1 uses the finite-type definition to choose a cover whose rings are already finitely generated, and the integral-scheme definition to make the nonempty charts domains. The finite-type-over-Noetherian statement applies over fields; the tensor and its reduction are still finitely generated. The componentwise-chart statement identifies exactly the normalization of the reduced scheme, and the reduced-Noetherian total-fraction statement identifies its component fraction fields. The normalization and integral-closure definitions then give the two affine integral closures; the coordinatewise monic-equation argument is written out. No irreducibility of the field base change is assumed.

Step 2 uses the new fraction-ring maps only for their stated map and compatibility properties. The integral-closure definition gives the monic-equation argument. The integral-closure-localization theorem states the localization equality needed on principal refinements, and the reduced-algebraic-normalization-field-change statement expressly gives compatibility with every open restriction. Hence the gluing is of the indicated maps, not merely of homeomorphic spaces. The resulting map has the over-X_K equation because each affine ring map extends A tensor K.

Step 3 uses the actual theorem that every module over a field is flat, so tensoring the inclusion A' into Frac(A) is injective. It uses exactly the nil-kernel clause of the new node after this inclusion. This proves nilpotence in A' tensor K itself; it does not assume that tensor product is reduced or that the comparison is injective.

Step 4 applies the existing separable comparison to X, which is reduced and finite type; the reduced-normalization definition identifies its single summand with the item's integral normalization. The perfect-field separating-basis statement covers characteristic zero, and the separably-generated-implies-separable statement gives the field-theoretic meaning needed here. Thus the residual case really has positive prime characteristic. The universal-homeomorphism definition immediately covers the isomorphism case.

Step 5 is the elementary finite-support argument from the source: choose actual lifts of the numerator, denominator and monic coefficients, and take the field of their scalar coefficients. The tensor-product statement says pure tensors generate, and the new node gives both reduced-ring and quotient-ring injectivity. I explicitly checked descent of the nonzerodivisor condition and of the equation, rather than claiming finite-presentation descent without hypotheses. The integral-closure definition supplies the equation that is descended.

Step 6 uses the finite-transcendence-basis theorem for H/k (H is finitely generated by construction), then applies the separable-first theorem only to the algebraic extension H/k(t). Its statement actually supplies the purely inseparable pointwise power conclusion. The transcendence-basis definition and the separably-generated-implies-separable theorem show E/k is separable. Taking a maximum of the finitely many exponents and the characteristic-p binomial identity puts the specified powers into E. This works even if one does not first prove a finite bound for the whole purely inseparable extension.

Step 7 uses the new node's embeddings to reflect regularity of the denominator and equality of the Frobenius-raised equation. The integral-closure definition therefore places u in B'_E. The existing separable normalization statement applies for the possibly nonalgebraic E/k, as its statement explicitly permits; it identifies the canonical affine comparison as an isomorphism. The tower-compatibility clause of the new node identifies its image in Q_K with b^q. This is the step proving power-surjectivity, rather than moving that conclusion into the new node.

Step 8 applies the existing power-generated-spectrum statement with both hypotheses checked: the nil kernel from step 3, and p-power images from step 7. Its second requirement p^n b in the image is zero in characteristic p. Its conclusion is already a universal homeomorphism, with arbitrary ring base changes. The universal-homeomorphism definition then gives the global conclusion by the written open-cover inverse-gluing argument.

I checked the small cases A=k (including a purely inseparable nonreduced scalar extension of a nontrivial finite residue field after changing k), K=k, characteristic zero, a geometrically normal chart, and a base change with several reduced components. For a concrete nilpotent case take k=F_p(s), A=k[u]/(u^p-s), K=k(s^(1/p)): A is a field, while A tensor K is K[epsilon]/(epsilon^p). The comparison goes from Spec K to this nonreduced point, its kernel is nil and the pth-power condition holds; it need not be an isomorphism. For a component-splitting example take k=R, A=C, K=C: the tensor product and its normalization are C times C. Neither example is incorrectly treated as a domain after base change. The empty normalization chart is omitted from the chosen nonempty cover, and its restriction is automatically the empty morphism. The new node's domain hypothesis excludes the zero algebra; no false zero-ring fraction-field claim is made.

All eight steps are below 2000 characters (1148, 887, 468, 658, 796, 816, 896, 834 when written). I reviewed the field-core and fraction-power arguments for hidden independent comparisons; their only non-elementary inputs are the existing field theorems and the new ambient quotient-ring lemma. I checked delivery-errors B--E: new node self-contained and statement-only; sources by correct tag and label; search claims backed by logs; no elementary or duplicate new node; all cited conclusions actually in the cited statements; no off-route replacement, added hypothesis, missing component, silent statement change, or unsupported transport. The quote file copies each cited statement verbatim and the paragraphs above identify the used clauses.

## Unfinished work

Nothing remains within this one-level split. The new unsplit ambient-ring statement is intentionally a later stage-1 item. Required dry-run and push results will be recorded after the tools return.
