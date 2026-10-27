## Worker report

Files written: dag/nodes/sec-six-functors-basics/lem-sfb-finite-hilbert-stack-descent.json (statement; split; no Mathlib match). citations.json supplies 11 checked verbatim excerpts for the six steps. searches.jsonl records seven new searches, all read. No new node files; zero Mathlib leaves.

Attachments: none. The project-source tag search and Hilbert-stack / finite-Hilbert concept searches in lean/WeilConjectures returned no declaration stating the item. The upstream sorry declarations are not accepted proofs.

WANTED: none. All sources needed for this split are present locally.

The imported item had no proof. Its statement agrees with examples-stacks.tex Tag 05WB (lemma-hilbert-d-stack), with the construction before Tag 05WC (definition-hilbert-d-stack); no statement correction was needed. The source's sentence “Details omitted” leaves the arrow sheaf condition and the comparison gluing calculation to the reader; both are written here. The source's printed cartesian-map formula in the preceding construction has its base symbols reversed; the existing definition node already uses the correct formula Z = T ×_(T') Z', and this split uses that definition without changing it.

The inherited blueprint.from.node was null. blueprint_refs.py ancestor reports that null, although from.place and the entire via chain explicitly anchor this prerequisite to det-thm-sf-ctf-stability-direct-images. I restored that ancestor, retaining the chain. I read the latest blueprint file at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.md: it states direct-image preservation as clause (3) and contains no proof paragraph. The split records that distinction rather than inventing a current paragraph. Chapter and unit are unchanged.

Unfinished work: none for the one-level split. The reused finite-cover descent theorem is already an unsplit DAG node, to be processed independently.

## New nodes

None. The whole-DAG keyword and Tag 05WB / lemma-hilbert-d-stack searches found lem-sfb-finite-locally-free-fppf-descent, whose statement supplies precisely the finite-cover pullback, effective descent, and isomorphism descent used here. I read that entire statement. The existing Hilbert-lci and relative algebraicity nodes are consumers or refinements and cannot replace the stack-condition proof. Whole-blueprint searches for 05WB, Hilbert, and finite locally free found no equivalent imported statement: the Hilbert-functor nodes are set-valued embedded closed subschemes, whereas this item retains automorphisms and arbitrary stack objects.

## Not duplicates

No new node pairs. The existing lem-sfb-finite-locally-free-fppf-descent is cited, not recreated. Its theorem has no x, y, or alpha components, so citing it does not relabel a clause of this item as a new lemma.

## Mathlib searches

Seven new msearch.py invocations were made: two LeanFinder phrasings, a LeanSearch query, two Loogle queries, and two grep patterns. Their exact text and returned summaries are in the item's mathlib_searches and searches.jsonl. All services answered. I read the hits: Scheme.GlueData and RelativeGluingData handle open-cover gluing, not effective fppf descent of covers with stack objects. The generic Pseudofunctor.IsStack constructors and isEquivalence_toDescentData require an existing stack or descent-equivalence hypothesis; they do not establish it for H_d(F). I opened Mathlib/CategoryTheory/Sites/Descent/IsStack.lean, including the class at lines 48ff and the equivalence and constructor below it. The analytic finite Hilbert-basis hit is unrelated. The old Mathlib records were retained as historical searches, and the new actual queries appended.

## Review by Q14

I checked delivery-errors B–E against the six steps and the local sources. For the item I read examples-stacks.tex from the definition of H_d through the proof of lemma-hilbert-d-stack and definition-hilbert-d-stack (Tags 05WB/05WC). For the existing finite-cover input I read its statement and descent.tex lemma-affine (0245), lemma-descending-property-finite-locally-free (02VO), and lemma-fpqc-universal-effective-epimorphisms (023Q). In particular 02VO descends constant degree as well as finite local freeness. The existing input already states the fppf specialization, so this delivery does not silently assert that an arbitrary non-quasicompact fppf family is an fpqc family. There are no new-node sources to audit.

Step 1 cites def-sfb-relative-finite-hilbert-groupoids for the actual arrow equation, composition, and pullback construction, and lem-sfb-finite-locally-free-fppf-descent for stability of the finite-cover objects under pullback. Cartesian lifts and inverses are checked componentwise. The fibred groupoids and their coherent pullbacks are hypotheses already spelled out in the item's statement and definition. I do not take a theorem on arbitrary stack pullbacks from a definition node.

Step 2 uses the isomorphism-descent sentence of lem-sfb-finite-locally-free-fppf-descent, not merely its object clause: it supplies the scheme isomorphism g. The target-object isomorphism b glues by the explicit assumed isomorphism-sheaf condition for Y. I checked that this also applies after any V → T, as required for the entire presheaf and not only its value at T.

Step 3 cites the Hilbert definition for F(a) alpha = g^*(alpha') b and def-weil-pbc-sites-and-cohomology for the base-change covering axiom. I opened that definition and verified it really states the needed axiom (iii). Thus the X isomorphism sheaf can be used on the fppf cover Z ×_T T_i of Z. Both sides of the compatibility equation belong to the same Y isomorphism sheaf. Its separatedness proves equality and uniqueness componentwise; it is not descent of a morphism into an unrepresented stack by an uncited scheme lemma.

Step 4 cites the object-effectiveness sentence of the finite-cover node and the Hilbert definition to extract the scheme datum. Its hypotheses hold: all Z_i/T_i have the fixed degree d, the cover is fppf, and the scheme part of the original cocycle gives the required theta cocycle. I explicitly kept the overlaps Z ×_T T_ij, avoiding the incorrect Z_i ×_T Z_j overlap (which includes two independent points of Z). The finite-cover theorem applies because it allows every d ≥ 0, including this d ≥ 1.

Step 5 uses the stated fppf effectiveness of Y on T and X on Z, each exactly once, with the cocycle equation supplied by the corresponding component of phi. The covering axiom in def-weil-pbc-sites-and-cohomology supplies the needed covering of Z. The cited Hilbert definition specifies these components. Pullbacks of F commute up to their canonical comparisons because F is a morphism of the given fibred groupoids; no representability, flatness, finite presentation, or faithfulness of F is introduced.

Step 6 uses the Hilbert arrow equation in def-sfb-relative-finite-hilbert-groupoids to verify the displayed equality of the transported alpha_i on each overlap. The calculation uses a_j = a_ij a_i and b_j = b_ij b_i with consistent directions, and inverts F(a_ij) before cancellation. It then invokes precisely the assumed Y isomorphism-sheaf condition, so the glued comparison remains an isomorphism. The local triples rho_i,b_i,a_i satisfy the arrow equation and recover the supplied phi_ij. Nothing is inferred from a proof rather than a cited statement. Each of the eleven citations has a literal sentence excerpt in citations.json.

Edge cases: d = 1, empty T with its empty covering, arbitrary automorphism groups in X and Y, nonfaithful F, and a nonsmooth nonreduced degree-d cover are allowed. The proof never treats X or Y as a set of isomorphism classes. The empty-cover case is covered by the stated stack hypotheses and finite-cover descent theorem, whose conclusions include the empty scheme. No scheme intersection is assumed affine and no base finiteness is assumed. No additional hypothesis is needed and no conclusion is weakened. All six non-elementary steps are below 2000 characters (maximum 1144); none hides an auxiliary lemma. The algebraic descent theorem is an existing node, and remaining gluing statements are direct uses of the stack hypotheses with their cocycles written out.

No cross-unit theorem is introduced: the finite-cover theorem is in the item's own unit. The other proof citations are definitions. There are no new unsplit nodes with proof sketches, no duplicated lemmas, no SGA sources, no Lean edits, and no compilation.
