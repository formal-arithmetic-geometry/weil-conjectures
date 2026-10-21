# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/def-sfb-tensor-symmetry-pure-equation.json`: definition; no exact Mathlib predicate found. Retained its statement and existing Lean ownership. Added the existing native complex-constraint node to statement dependencies and a stage-1 split report; preserved earlier searches and appended the NP searches actually run.
- `citations.json`: empty list, since a definition has no proof steps.
- `report.md`: this report. No new nodes, no Mathlib leaves, no unit changes.

## Attachments

No ATTACH claim. The exact existing definition is `CategoryTheory.RingedDerivedNative.symmetryPure`, `lean/Sheaf/Algebra/Homology/RingedTensorComplexConstraints.lean:31`. It is already recorded on the item. It is under Sheaf, whereas the brief requires an attachment declaration under WeilConjectures. Searching WeilConjectures for the exact blueprint tag, symmetryPure, pure-section symmetry, and Koszul/braiding terminology found no exact definition there. Generic complex braiding declarations do not define this project-specific Prop. The separate `complexConstraints` theorem in the recorded Sheaf file has `sorry`; it is not a proof attachment for the equation.

## WANTED

None. All sources needed for this definition were available locally.

## What needed correction

The item was already marked split when this session began, but had no stage-1 split_report or review. Its mathematical statement is correct and is retained verbatim. The canonical braiding it names now has the explicit statement dependency `lem-sf-ringed-tensor-complex-constraints`, whose statement introduces the native braiding on precisely these complexes. This does not turn the predicate into an assertion of the formula. All other fields owned by the maintainer, including source, Lean record, audit, import flags and ancestry, are retained. No theorem is hidden in a definition body.

## Unfinished

No mathematical work remains for this one-level definition split. The truth of the signed equation belongs to the separate tensor-constraint theorem; this item deliberately only defines the proposition. No Lean was written or compiled.

## Not duplicates

No new node was created. DAG searches for Koszul, braiding, symmetry, pure-section terminology, 06YU and 0FPQ, and whole-blueprint searches for Koszul, braiding, symmetry and pure.section found no second blueprint node defining this same predicate. In particular `lem-sf-ringed-tensor-complex-constraints` asserts four formulas, whereas this item defines one Prop without asserting it. `lem-pur-total-tensor-signed-coherence` constructs and compares chain isomorphisms and shifts; it does not define this named pure-section predicate. Neither warrants a new node.

## Review by NP

I read Stacks `sites-cohomology.tex`, definition-derived-tor (06YU), and the commutativity display immediately after it. That display is derived; I did not mistake it for a proof of a statement about arbitrary complex sections. For the underived meaning I read sites-cohomology-lemma-symmetric-monoidal-cat-complexes (0FPQ), and `more-algebra.tex`, section-symmetric-monoidal (0GWN), particularly the homogeneous commutativity formula and its differential calculation. The source uses the sign (-1)^(pq) on the (p,q) summand, which is exactly the expression this predicate records. These sources are not SGA. The chapter and restricted-functors unit were read; this auxiliary definition supplies the one-K-flat transpose calculation below that unit and changes neither route nor statement.

There are no proof steps: the item's kind is definition and its proposition is not asserted. Accordingly proof, proof_deps and citations.json are empty. I checked each statement dependency by opening its JSON statement. `def-weil-sheaf-of-modules-category` supplies the module structures on sections and linear maps. `def-pc-tensor-complex-sheaves` supplies the direct-sum total and its signed differential for arbitrary integer-indexed complexes. `def-coef-ringed-tensor-hom-model` explicitly says that a pure tensor generator uses the actual sheafification unit and total-complex summand inclusion, not a chosen map. I use just that generator construction, not the K-flat representative comparison in the same node. Finally `lem-sf-ringed-tensor-complex-constraints` introduces the native braiding for independent object, arrow and coefficient sizes, and for arbitrary unbounded complexes under exactly the sheafification hypotheses in the item. Its mathematical formula is a separate assertion, not a proof step smuggled into this definition. Thus no citation takes a fact absent from the cited statement (C4), and there is no uncited non-elementary proof step (C1).

I also read the literal body of symmetryPure at lines 31-38 of its recorded module. Its quantifiers are P,Q,p,q,n,h,h',U,x,y, with no K-flatness or boundedness assumptions. Its scalar is `(p*q).negOnePow` acting on the target module sections. The module abbreviation at RingedDerivedTensorNative.lean:346 is the commutative ring sheaf viewed as a ring sheaf and SheafOfModules in max(c,v,u). The generator body at CoefficientRingedTensorHomModel.lean:139-156 is a presheaf pure tensor followed by the sheafification unit, inverse tensor-sheafification comparison, and total summand inclusion. It has no K-flatness binder. Thus using its generators does not import any hypothesis about a derived comparison. Both degree witnesses are necessary as explicit types for the two summand inclusions; commutativity of integer addition supplies the second whenever the first holds, without restricting the complexes.

Small cases checked: p=q=0 gives the unsigned swap; p=q=1 gives a minus sign; p=-1,q=1 still gives a minus sign; if either degree is even the sign is positive. Negative exponents mean integer parity, equivalently Int.negOnePow, so they are meaningful. In characteristic two the scalar -1 equals 1; no exclusion of that case is present. Zero sections, the zero ring, and zero complexes give an equality of zero sections. Arbitrarily unbounded complexes still have their single (p,q) summand inclusions, so no finite-support condition on the complexes is needed. Since this is a predicate definition, none of those checks asserts its truth using the sorried constraint theorem.

For the Mathlib audit I read all returned hits. The first LeanFinder query gave generic sheaf braided/symmetric structures and HasTensor/HasGoodTensor predicates; the second gave tensorObj, iotaTensorObj, tensorHom, and summand reindexing. These are ingredients, not the quantified ringed-site equation on actual sheafified sections. LeanSearch gave unrelated opposite-complex and homology results. Both grep searches returned no match. Loogle rejected two expected identifiers; the records say so and are not treated as evidence of absence. The two distinct semantic phrasings and independent grep searches establish the limited no-exact-predicate verdict. Earlier recorded searches were retained rather than fabricated or overwritten.

Against B-E: there are no new nodes to be elementary, duplicate, or restated clauses, no new statement-only records to audit, and no long proof steps. The item introduces every quantified object, preserves all universe and sheafification hypotheses, uses the actual constructed maps, and does not strengthen or weaken any theorem. No source error or STATEMENT-DISPUTED correction was needed. The only dependency repair was making the already existing native braiding source explicit; no replacement theorem or copied construction was introduced.
