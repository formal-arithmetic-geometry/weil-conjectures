# Q85: lem-sfb-group-algebra-coaction-grading

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-group-algebra-coaction-grading.json`: statement, split; six elementary proof steps, no Mathlib match.
- `citations.json`: thirteen step/node pairs with verbatim extracts from live node statements.
- `report.md`: this report. The prescribed search command maintains `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the exact blueprint tag and coaction/Comodule concepts in the live `lean/WeilConjectures/` tree. The hits concern flat descent, not the grading of an arbitrary algebra by an arbitrary abelian character group. No project declaration states all the clauses of this item. Also searched the Sheaf tree for relevant prior formalizations; these are not attachment evidence under the brief.

## WANTED

None. The source for the model calculation is present locally.

## What was wrong or needed checking

The supplied item was statement-only, not a completed split. Its statement is correct and has been retained verbatim, along with the source caveat that Stacks 0EKK states the multiplicative-group case, not the arbitrary-character-group theorem. The generalized proof is therefore marked agent-written. No statement dispute or source error was found. No field, nonzero-ring, finite-generation, reducedness, flatness, or torsion-free assumption has been introduced.

The inherited unit record has chapter `sec-six-functors`, while this created item inherits filing chapter `sec-six-functors-basics`. The current latest blueprint places `sk-thm-sf-ctf-stability` under `sec-six-functors-basics`; I read its statement, proof, and chapter section there. The inherited creation ancestry reaches no imported blueprint node (`blueprint_refs.py ancestor` reports None), so I retained the existing null ancestor and via list and explained the exact coaction input served by the proof in `split_report.blueprint`. This generic coordinate calculation neither changes nor replaces any unit-level proof route. I did not alter the chapter/unit records.

## Searches and Mathlib verdict

Read the original item's inherited search records, retaining them. Independently ran the five logged Q85 searches in `searches.jsonl`: LeanFinder with two semantic phrasings (coaction-to-grading and arbitrary-ring diagonalizable weight decomposition), LeanSearch for the comodule direct sum, Loogle `"Comodule", "DirectSum"`, and grep `coaction|comodule|groupLike` under RingTheory. Every service answered successfully. The new `mathlib_searches` records have exactly those query strings and the returned summaries.

Read `Mathlib/Algebra/MonoidAlgebra/Grading.lean` through its grading and internal-direct-sum declarations (lines 173 and 186), and `Mathlib/RingTheory/Bialgebra/MonoidAlgebra.lean` around lines 44–55. The former grades the group algebra itself; it does not grade an arbitrary algebra from a coaction. The latter supplies group-like elements and their span, not a comodule decomposition. The Rep hits concern group actions, and the LieModule weight results require different hypotheses. Thus no exact match or one-line specialization proves this item.

Whole-DAG concept/tag searches included coactions with gradings, tensor/free-basis concepts, and 0EKK. Whole-blueprint searches for `coaction`, `grading`, and `group algebra` returned no general coaction-to-grading theorem. No new node was created, since coefficient extraction and all identities below follow in a few lines from the existing basis definition and balanced tensor universal property.

## Not duplicates

No new nodes are proposed. The existing `lem-sfb-gm-affine-action-grading` has character group Z, so cannot supply arbitrary M, including torsion. `lem-sfb-trivial-torus-coherent-weight-decomposition` assumes a field and coherent linearized modules over a Noetherian scheme. `lem-sfb-graded-stabilizer-strong-products` assumes the grading, rather than constructing it. `lem-sfb-affine-multiplicative-type-monomorphism-closed` is the parent using this calculation, so citing it would be circular. All four statements were opened and read.

## What could not be finished

Nothing in the mathematical split remains open. No Lean was written or compiled. The requested server dry run and delivery are the remaining operational steps when this report is first written.

## Review by Q85

I read `literature/stacks-project/groupoids.tex`, the statement and whole proof of `lemma-complete-reducibility-Gm` (Tag 0EKK, verified against `tags/tags`). That proof extracts Laurent coefficients, uses the identity section to sum them, and uses the action law to prove that the coefficient maps are orthogonal projections. Our algebraic coassociativity and counit hypotheses are exactly the identities needed for the same coefficient calculation with the free basis indexed by M. The group law is used only in the final multiplication rule, so torsion in M causes no difficulty. No SGA source is used.

I opened and read the full statements of all three dependencies, not their proofs. `def-sfb-ring-diagonalizable-group` explicitly supplies the finitely supported basis, multiplication, unit, coproduct, and counit over any commutative ring. `def-weil-pbc-module-tensor-product` explicitly supplies the balanced universal property and generation by pure tensors. `def-weil-pbc-algebra-hom-quotient` defines the structure map and its preservation by algebra homomorphisms. The exact parts used are copied into `citations.json`.

Step 1 uses the first two statements: the coefficient q_m exists from the specified group-algebra basis, and the balanced rule q_m(f)a induces C_m. Generation by pure tensors reduces reconstruction to expanding finitely many finitely supported f_j; applying C_n recovers the coefficient. I checked this does not use flatness or a theorem about tensor preserving injections. It is a direct generator calculation, so extracting it into a new lemma would create an elementary node.

Step 2 uses the same statements for rho's finite coefficient expansion and epsilon(e_m)=1. The actual counit identity is a hypothesis of the item. It yields the finite sum a=sum p_m(a), with no global finiteness of the set of degrees.

Step 3 uses the basis coproduct and balanced tensor property again. I wrote the coassociativity equality with the tensor order fixed, then explicitly supplied the final-factor extraction B tensor R[M] -> B for B=A tensor R[M]. It gives rho(p_n(a))=p_n(a) tensor e_n directly. No tensor-basis theorem, independence over a domain, or concealed double-direct-sum identification is used.

Step 4 uses the tensor bilinearity and the definition of algebra homomorphism for R-linearity. I checked closure of A_n under zero, addition, and all R-scalars by the displayed formulas. Existence of the finite homogeneous family follows from the already proved sum and coefficient identity; it is not a citation of a restated new node.

Step 5 uses those same definitions for additivity and linear coefficient extraction. Applying C_n to rho(a)=sum b_m tensor e_m gives b_n=p_n(a), so uniqueness is for finitely supported families, with omitted coefficients zero. This also checks the stated formula for rho in terms of the unique homogeneous family.

Step 6 uses all three statements: rho preserves the structure map, unit, and multiplication, e_0 is the unit, and e_m e_n=e_(m+n). The tensor-algebra multiplication is explicitly (a tensor f)(b tensor g)=ab tensor fg. I wrote the formulas for 1, each scalar, and a homogeneous product, verifying every final clause without a semisimplicity assumption.

For the B–E audit I checked independent statement readability, unchanged notion dependencies, actual source tag, preservation of inherited fields, honest logged searches, and absence of new unsplit nodes with proof material. The thirteen quotes verify every cited node/step pair against its statement (C4). All other ingredients are the hypotheses or the displayed elementary calculations (C1); no non-elementary fact is asserted by reference alone. There is no dependency on a descendant and no relabelling of the conclusion as a new lemma. Every step is below 600 characters, so no long step hides a lemma.

Small cases checked: R=0 and A=0 give the single zero finitely supported family; M=0 gives rho=id and A=A_0; a trivial coaction gives A_n=0 for n nonzero by C_0 extraction; R=Z/4 and R=k[epsilon]/(epsilon^2) cause no cancellation in the argument; M=Z/p in characteristic p still has distinct formal basis indices, so coefficient extraction remains valid even though the corresponding group scheme need not be reduced. Arbitrary infinitely generated M is permitted because only the finite supports of finitely many tensors enter each calculation. These checks support the full unrestricted statement, not a weakened replacement.
