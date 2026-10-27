# Q131: lem-sp-etale-sheaf-fold-scalar

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-etale-sheaf-fold-scalar.json`: statement, now split into seven steps; no Mathlib match.
- `citations.json`: a verbatim statement excerpt for every citation in every step.
- `searches.jsonl`: five actual msearch results, retained unchanged.
- `report.md`: this report.
- `write_split.py`: sandbox preparation script, not a delivery node.

No new nodes; no Mathlib leaves.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, fold/counit terminology, and summation. Read `SixFunctors/Etale/LowerShriek/EtaleMap.lean`: `AlgebraicGeometry.Etale.etaleLowerShriekUpperStarAdjunction` supplies an adjunction, but does not state the ordinary scalar-extension identity or its cochain clause, so it is not an attachment for this item. Existing declarations for the general bilinear sheafification lemmas are already attached to their own nodes; those nodes are reused.

## WANTED

None. All sources used are in the read clone.

## Corrections and scope

The imported statement is mathematically sound. Its literal doubled TeX command escapes were normalized, with no change to objects, hypotheses or conclusions. Its source place now distinguishes Definition 03S3 from Exercise 03S4. Neither the statement nor the proof uses an SGA source. No Lean file or compiler was used.

The source exercise asks for the adjunction proof rather than supplying it; the steps write out the direct finite-sum argument. The coefficient identity is an agent-written generator consequence of that construction. `proof_origin.by` is therefore `agent`. No non-elementary assertion is passed off as a source exercise's omitted proof.

The original text speaks of constant-ring modules. Section coefficients in the proof mean sections of the constant ring sheaf, not just globally constant elements of the coefficient ring. In particular the tensor is over A_V(W), and restriction along a lift identifies B_V(W) with B_U(W,s). We never assert that tensor sheaf sections are globally pure tensors or that the sum presheaf is already a sheaf.

## Unfinished work

None at stage 1. Existing cited general lemmas remain their own independent items; no proof was moved into a new statement-only node.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs to distinguish. Whole-DAG keyword/tag searches included 03S3, 03EL, sheafification/tensor, fold, and sum-extension; blueprint searches included sum extension, fold, sheafification, tensor pullback, counit, and summation. The open-immersion adjunction `lem-weil-pbc-extension-by-zero-adjunction` is narrower than the etale morphism here; it was read but not used as though it covered the item. `lem-sp-etale-sum-counit-scalar` is the derived parent and was not cited, which would make a cycle. The existing generic bilinear extension, its uniqueness, the tensor universal property, and the independent ordinary inverse-image tensor comparison cover all the auxiliary needs. The dependency closure of the cited nodes contains no back edge to the item.

## Mathlib searches

Preserved all five inherited item searches. Ran five additional searches through the required Q131/item msearch command: LeanFinder twice with different phrasings, Loogle, grep, and LeanSearch. Each record added to the item is exactly a query in searches.jsonl. Read the returned declarations and their displayed types. The direct source inspection of `Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:303` shows a counit for an adjunction of site pushforwards induced by an adjunction of site functors; it does not give the etale sum fold or the coefficient equation. LeanFinder returns general sheafification adjunctions and the presheaf tensor restriction formula. Neither is a one-line specialization proving all the item's clauses. No new node needs a search record.

## Review by Q131

I read the full B--E checklist in coord/delivery-errors.md and compared the proof with the actual statements cited, rather than using an existing node's proof as its interface. The mathematical source for the item is etale-cohomology.tex, Tag 03S3, especially equation-j-p-shriek and the paragraph identifying inverse image with restriction, and Tag 03S4, exercise-jshriek-direct. I read sites-modules.tex at Tag 03CY (module sheafification), Tag 03EL (ordinary tensor/pullback), and Tag 0GMW and the following Hom/Bilin display. I also read the main-20261015 Charts paragraph of det-sp-reduction-exceptional and the chapter/unit records: this proof realizes precisely integral summation commuting with coefficients in the unit's second step. There is no change of route to a purity or trace theorem.

Step 1 cites the actual abelian etale restriction theorem, the module inverse-image theorem, and the sum-extension definition. I checked that the abelian restriction citation alone would not establish the coefficient action; the module theorem supplies both the constant-ring comparison and the transported action. Its clause (1) applies for R=A and R=B, with no finite-ring assumption. The sum-extension definition is exactly the sum over lifts being used.

Step 2 uses the universal factorization clause of module sheafification to replace sheaf maps by presheaf maps. The remaining argument is written explicitly: restrict to injections, sum a compatible family on a finite-support vector, and check the two composites on injections. Objects and arrows over U give exactly the needed compatible families. This is an elementary direct-sum and definition argument, not an uncited general Kan-extension theorem. Step 3 then takes the identity family to identify the counit; the same universal factorization proves its naturality. Thus the fold has actually been identified with this adjunction's counit, not merely with some natural summation map.

Step 4 uses the statement of lem-pur-independent-inverse-image-tensor-comparison, which explicitly gives an ordinary tensor isomorphism and its pure-tensor behavior for an algebraic inverse-image lift. The sites are small relative to the coefficient universe and the geometric inverse image is a finite-limit-preserving left adjoint. The module inverse-image theorem gives the algebraic lift and constant A and B identifications. This is precisely the ordinary setting of the generic lemma; the derived comparison and pro-etale comparison nodes were not used. Restriction identifies the actual section tensors at (W,s) and W, giving the formula needed later. Its B-linearity follows by applying the same pure-tensor formula to multiplication in the second factor.

Step 5 cites the actual existence-and-uniqueness bilinear extension statement, not only a sheafification definition. The base ring map for this application is the identity of the sheaf A_V, which is locally bijective; the presheaves are P_AH and B_V; the target is the A_V-module underlying the specified B_V-module sheaf. The formula is additive and balanced and commutes with every restriction, as checked termwise. The tensor universal property's statement gives a map from the ordinary A_V tensor. B-linearity and naturality follow by uniqueness on the original inputs; for a coefficient section over W the same equality is tested after all restrictions over W. No flatness or sheaf-level global generator claim is needed.

Step 6 cites the separate bilinear uniqueness statement and the sheaf tensor Hom/Bilin bijection. I checked that these citations state exactly the equality test being used: two natural pairings which agree after both sheafification units agree, and equality of pairings is equality of tensor maps. Both sides send the same section i_s(x) tensor b to the unit image of x tensor b; the middle arrow is the normalized comparison from Step 4. This explicitly checks the compatibility rather than saying it transports automatically.

Step 7 cites the cochain-complex definition, whose morphism clause is exactly the displayed naturality equation at each differential. All functors here are additive by their stated section formulas. No resolution, derived tensor, totalization, or exchange of an infinite sum with a limit is used.

I tested the empty source U (zero sum and zero fold), the identity etale map (one lift and the identity fold), a two-copy finite etale map (ordinary addition on two summands), the zero module and zero ring, and a nonflat coefficient map such as Z to Z/2. The calculation remains x tensor b on both paths in each case. The empty test object has zero sections and causes no exception. An unbounded complex presents no additional operation beyond the degreewise formula. There are no new statements to test and no long step exceeding 2000 characters; the longest step is the explicit balanced-pairing construction. I checked each citation quote verbatim and retained all inherited search records and blueprint fields.

The off-unit statements in split_report.tool_uses are generic tools: etale inverse image/restriction and its coefficient actions, ordinary inverse-image tensor compatibility, bilinear extension and uniqueness, and the tensor universal property. None replaces a geometric step of the unit. No tool_uses field reserved for the maintainer was added to the node itself.
