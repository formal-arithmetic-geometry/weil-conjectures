## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-joint-adjunction-model-embedding.json`: existing statement, now split into six elementary steps. Added the existing additive-functor definition to statement dependencies and its reference to the statement. Mathematical hypotheses and conclusion unchanged. Mathlib verdict: no exact match or one-line specialization after five fresh logged searches, including two semantic phrasings.
- `citations.json`: verbatim statement quotes for all seven step citations.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: this item is a subordinate categorical lemma, not the key node of its unit.

## Attachments

None. I searched the actual read clone's WeilConjectures source for the exact blueprint tag, joint zero detection, products of adjunction units, and the relevant names. `AlgebraicGeometry.ProEtale.CondensedRing.mono_pi_lift_unit_upperStarLowerStarAdjunction`, in `WeilConjectures/SixFunctors/ProEtale/ModuleObject/ConstructibleEmbedding.lean:70`, has a proof without a local sorry, but states only the finite geometric-family case for condensed module objects and identity local models. It does not state this item's arbitrary abelian-category / set-indexed-family theorem, so it is not an attachment. The adjacent presentation-family theorem likewise has more specialized hypotheses. I did not claim their transitive closure to be closed.

## Literature wanted

None. All sources used here are present and were read locally; no downloads were needed.

## What needed repair

The imported node had a statement and earlier searches, but no proof. Its generality is sound. I kept its existing source, blueprint ancestry, created metadata and earlier search records. The only statement-text addition is a reference to the existing definition of additive functor; this does not change the mathematical claim.

The current blueprint's Essentially small paragraph is a compressed gluing assertion, not itself a proof of this categorical lemma. I supplied the isolated kernel argument and marked the proof origin as agent. The specified adjunction bijections are part of the item's own hypotheses, so no external adjunction theorem or triangle-identity node is being tacitly assumed. Kernel preservation is also a hypothesis, not inferred from left adjointness.

## Unfinished work

None for this stage-1 item. No Lean was written, compiled or built. All writes are inside the assigned sandbox.

## Not duplicates

No new nodes were created. Whole-DAG title/statement searches for kernels, zero objects, monomorphisms, additive functors and adjunctions reused the existing definitions. Whole-blueprint searches `joint.*zero`, `jointly`, `adjunction.*product|product.*adjunction`, and `adjoint.*monomorphism|monomorphism.*adjoint` found no second statement of this generic embedding lemma. The ancestor command returned `det-brown-hypotheses-small`, as already recorded in the item's blueprint field.

## Review by Q59

I read the chapter record, the Brown-hypotheses unit record, the live item's statement and its blueprint source `main-20261015/.../sk-lem-brown-hypotheses-small.proof.md`, especially the Essentially small paragraph. The argument continues the specified global-gluing route. I also read Stacks `categories.tex`, Tag 0037 (`definition-adjoint`), with its natural bijections and the following unit/counit formulas; `homology.tex`, Tags 0106 (`definition-kernel`), 00ZY (`definition-preadditive`) and 0109 (`definition-abelian-category`). These are the primitive definitions needed for the calculation. There are no new-node sources to review. The proof is marked agent-written because the assembled categorical argument fills the blueprint's omitted details.

For step 1 I opened `def-weil-category-product`: it explicitly supplies projections, the unique map with prescribed components and their equations. I opened `def-sp-abelian`: it explicitly supplies kernels. Their quoted statements justify choosing the product components and a kernel; the zero-composite equation is then the defining equation of that kernel. I spelled out its existence-and-unique-factorization property using Tag 0106.

For step 2 I opened `def-weil-pbc-additive-functor`: it says the map on every Hom group is a homomorphism, so it sends zero to zero. I opened `def-weil-preadditive-category`: its bilinearity makes every zero composite zero. The rest of this step is exactly naturality of the bijections that the item assumes: apply it to k and to the zero arrow with the same source K. The two adjuncts are both zero, so bijectivity equates their preimages. Composing with the inverse of the hypothesized isomorphism e_i gives F_i(k)=0. No faithfulness, reflection property, additivity of G_i, or unsaid exactness theorem is used.

For step 3 the kernel-preservation hypothesis applies specifically to the kernel of u, not to an arbitrary monomorphism. The mapped kernel's uniqueness equates id and zero because its inclusion was shown to be zero in step 2. The only cited statement is `def-weil-preadditive-category`, which supplies the zero maps and bilinearity used to show directly that every arrow to or from F_iK is zero. Thus the assertion that F_iK is a zero object is proved inline, rather than taken from a zero-kernel or normal-monomorphism lemma.

For step 4 I checked that the hypothesis is joint detection of zero objects, precisely what step 3 supplies for K. It gives that K is zero. Uniqueness of an endomorphism of a zero object gives id_K=0 and bilinearity from the cited preadditive definition gives k=0. The argument needs no smallness assertion about a family of categories.

For step 5 the cited preadditive definition supplies subtraction and the equation u(a-b)=ua-ub. The previously chosen kernel factors this difference. Since k=0, a=b follows; this proves the cancellation definition of monomorphism explicitly. Step 6 merely substitutes identities, so has no citations. I checked the domain and codomain of every displayed composite, including Phi_{K,B_i}, e_i F_i(k), and the kernel of F_i(u).

Against delivery-errors B, the item remains self-contained, the only additional notion uses an existing definition, and no statement-only child or relabelled clause is created. Against C, I opened every cited statement, used no proof-only content, supplied a literal quote for every step/node pair, and verified the dependency union. All citations are existing definition Mathlib leaves, so there is no off-unit proof route and no tool-use approval to request. Against D, the steps themselves perform the argument; none invokes the conclusion under another name. Against E, no product-preservation, nonempty-index, finite-index, exactness, or individual-faithfulness hypothesis is added. Each step has fewer than 700 characters; there is no long hidden comparison lemma.

For small cases: if I is empty, the stated zero-detection hypothesis forces every object of A to be zero, so u into the empty product is monic; the proof's universal quantification works unchanged. For a singleton identity adjunction on Ab, u is the chosen isomorphism e. For A=Ab x Ab and the two coordinate projections, each left adjoint can kill a nonzero object, yet the pair detects zero; the product of their right adjoints recovers M, illustrating why a single-faithful-functor leaf cannot replace the argument. Extra zero functors in a detecting family cause no problem. Nonidentity e_i is handled by its actual inverse in step 2. Infinite I requires only the particular product assumed in the item, not arbitrary products or preservation of it.

I read the fresh search hits and inspected Mathlib `Adjunction/FullyFaithful.lean:57`, `Functor/EpiMono.lean:244`, and `Generator/Basic.lean:410`. The first assumes a single faithful left adjoint; the second individual reflection of monomorphisms; the third a coseparating class and a product over all its test arrows. Obtaining these hypotheses or identifying those products would require further arguments, so none is a one-line specialization of the item. The other hits concern adjoint triples, reflective categories, zero preservation or exact functors. The exact queries and returned names are retained in searches.jsonl and the item. No invented query or failed service is represented as a successful search.
