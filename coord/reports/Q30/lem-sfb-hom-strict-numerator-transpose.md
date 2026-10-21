# Q30: lem-sfb-hom-strict-numerator-transpose

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-hom-strict-numerator-transpose.json: statement, split; no exact Mathlib match. Seven proof steps, statement unchanged.
- citations.json: 29 step/node pairs with verbatim excerpts from the cited statements.
- searches.jsonl: actual required search-command results; retained separately from the node's inherited Q53 searches.

New nodes: 0. Mathlib leaves: 0. No unit record changed: this is a strict-model tool below the unit's statement, not its key node.

## Attachments

None. Searched WeilConjectures for the exact blueprint id and for strict/numerator/transpose, and inspected the Hom/tensor source candidates. No declaration states every clause of this arbitrary-module normalized comparison with its fixed inverse augmentation. Existing closed currying/naturality ingredients alone are not an attachment.

## WANTED

None. The Stacks sources needed for the calculation are present.

## Problems found and corrections

The imported statement is sound with its existing word "compatible" for coefficient maps: these are supplied coefficient comparisons respecting evaluation and the fixed replacement augmentations. Step 7 makes their exact semilinear equation explicit. No arbitrary scalar-extension isomorphism with infinite Hom products is asserted. No statement was changed.

The subtlety is the representative-inversion clause for non-flat T: preservation of quasi-isomorphisms by T tensor - cannot be used. Step 6 instead uses K-injectivity of Hom(P,J), quasi-isomorphism invariance of Hom and the K-injective comparison principle to obtain homotopy equivalences; tensoring their homotopies with T is legitimate. This additional justification is necessary for the final naturality clause and is recorded in the proof rather than being hidden under "naturality".

The initial node had no proof. The existing lem-sfb-hom-kflat-chain-transpose already states the general one-sided model needed here, with arbitrary source A. It is reused, not duplicated or restated as a new node. The item retains the strict numerator calculation: construction of h, differential cancellation, normalized chain-map identity, inverse-augmentation cancellation, and explicit compatibility squares.

## Not duplicates

No new nodes. Whole-DAG searches for 08J9, K-flat transposition and tensor/Hom representative calculations found the already-existing chain-transpose result; whole-blueprint searches "tensor Hom", "chain transpose", "internal hom", "evaluation", "K-flat" and "normalized comparison" found no node equal to this fixed normalized numerator statement. The ancestor is lem-sfb-dc-hom-preserves, whose final coefficient-descent paragraph is realized through the existing evaluation-roof and filtered-colimit nodes. The chapter and unit routes are unchanged.

## Review by Q30

I read the stage-1 contract, SETUP's chapter/unit/node distinction and delivery-errors B--E, then the chapter and unit records. For the item I read Stacks sites-cohomology.tex, lemma-internal-hom (08J9): its proof uses arbitrary K, K-flat L, K-injective I and the chain Hom/tensor identification. I also read lemma-RHom-well-defined (0A95) and lemma-RHom-from-K-flat-into-K-injective, the tensor-sheaf definitions in sites-modules.tex section-tensor-product (03EK), and derived.tex lemma-K-injective (070I). The strict normalized numerator is an agent refinement of these sources, not a literal assertion of 08J9; proof_origin says agent. There are no new-node sources to review.

Step 1 uses the actual statement of prop-pur-kinjective-resolutions-exist for functorial K-injective replacements and natural quasi-isomorphic units; the existing chain-transpose statement with A=B, E=J and f=identity gives evaluation. def-coef-hom-representative-evaluation explicitly fixes the inverse localized augmentation, so its use to reach QC is justified. No second replacement is chosen.

Step 2 uses the actual tensor-sheaf, total-tensor and product-Hom definitions. I checked the two Koszul terms cancel with degrees n and m and that T's degree is zero. Balanced bilinearity, restrictions, the tensor/sheafification adjunction and the total coproduct universal property construct h and extend the equality from generators. This elementary step does not mistake local tensor generators for all global sections.

Step 3 uses precisely the Normalized formula in def-sfb-internal-hom-strict-models and the unique comparison fixed by def-sfb-internal-hom-strict-roof. The actual Hom projection, evaluation on the slice identity, tensor units and summand maps match those of the item. The explicit equality, then the same universal properties as step 2, proves the chain identity. Neither a theorem hidden inside a definition's proof nor an unsupported sheafification model is used.

Step 4 checks every hypothesis of lem-sfb-hom-kflat-chain-transpose: P is flat-term K-flat, E=I(N) K-injective, A arbitrary. Its statement expressly allows non-K-flat A and computes the tensor with only the right K-flat factor. The inverse unit required by def-coef-hom-representative-evaluation cancels [eta_N]. This is the strict normalized numerator argument, not merely citation of a new clause of the item.

Step 5 writes all three generator squares for T, P and C. The tensor and Hom definition statements supply their functoriality; the resolution theorem supplies the natural augmentation equation; the chain-transpose statement supplies natural representative comparisons and transposition. Step 6 checks the stronger inversion assertion using lem-pur-rhom-well-defined, lem-pur-hom-kflat-into-kinjective and the final sentence of lem-weil-pbc-kinjective-hom-derived. I read each statement in full: all are for unbounded complexes, the first has the correct K-injective targets, and the last is for any abelian category. A tensor homotopy with T[0] is explicitly 1_T tensor s, so no flatness is used. Commutative squares invert by multiplication with inverses.

Step 7 checks the compatible-coefficient clause on the same actual generators, using the explicit semilinear evaluation equation and augmentation compatibility. This is a direct substitution and universal-property argument, not an unproved base-change theorem. These are the supplied compatible comparisons of the statement; it neither constructs nor assumes isomorphisms for incompatible scalar extensions. Identity and composition are checked by substitution as well.

I checked B1--B10: no new node, no disguised proof in a fresh statement, no hollow data, no attachment or Mathlib match overclaimed; inherited searches are retained, new searches are logged exactly, and blueprint fields are filled. C1--C8: all non-elementary inputs are existing cited statements, every uses pair has a verbatim quote, and the off-unit generic tools are declared in split_report.tool_uses. D1--D5: the actual strict calculation remains in the item, with no new relabelled clauses or circular dependencies. E1--E7: no hypothesis is silently added, the arbitrary source and unbounded degrees are allowed, signs and comparison orientations are checked, and the naturality/transport equations are written out. Every step is under 2000 characters; none conceals a separate generic lemma.

Edge cases checked: T=0 and P=0 give zero maps; T=R gives ordinary evaluation; a non-flat module Z/2 over the constant ring Z still satisfies the balanced evaluation and differential identities. P with a single nonzero term and nonzero differentials in J checks the sign convention; arbitrary negative degrees obey the same (-1)^n cancellation. An arbitrary non-flat T does not preserve a general quasi-isomorphism, which is why step 6 uses homotopy equivalences between the correct K-injective representatives. No finite generation, boundedness, continuity or interchange of tensor factors is used.

## What remains unfinished

Nothing in the one-level split. Existing dependencies remain owned by their existing nodes. No Lean was written or compiled, no agents were started, and only this item's sandbox was written.

## Dry-run repairs

The first dry run rejected the excerpt for step 6 / lem-pur-rhom-well-defined as too short. I replaced it with the full verbatim statement, displaying the K-injective and quasi-isomorphism hypotheses and the actual Hom comparison. The proof and statement did not change.
