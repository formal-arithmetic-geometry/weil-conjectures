## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-independent-torus-character-values.json`: statement, split. Five proof steps, 2245 characters total. No exact Mathlib match for the item; its two substantial inputs already have DAG nodes. Statement and statement dependencies unchanged; inherited searches and provenance retained.
- No new nodes and no new Mathlib leaves.
- `citations.json`: four entries, one for each use in steps 1, 2, 3 and 5; quotes copied verbatim from the cited statements.

## Attachments

None. Searched the project `lean/WeilConjectures/` for the item id and the torus/character notions. The only torus occurrences concern an analytic trace-bound argument or the different notion of a split torsor. No project declaration states this item. No Lean was written or compiled.

## Literature wanted

None.

## What was wrong or missing

The item had an empty proof. Its statement is true as written; no statement dispute or correction is needed. I read Milne, *Algebraic Groups* (2017), Proposition 23.7 on printed p.486, Sections 12(a)--(c), in particular Proposition 12.3 and Lemma 12.4 on pp.231--232, and Theorem 12.9(a) on pp.233--234. The requested general independent-character assertion is not the literal statement of Theorem 12.9, as the item's existing source metadata already correctly says. I give an agent-written lattice extension argument supplying the choice used in 23.7. The full character anti-equivalence is not needed as an additional citation: the existing matrix-correspondence statement already gives exactly the character coordinates and their group law.

I read the chapter record, the recorded unit, and the current `literature/blueprint/latest/` chapter, unit and direct-image proof. This item serves the inherited proof-(3) alteration/moduli chain and does not replace any unit step. Its `blueprint.from.node` is already null: `tools/blueprint_refs.py ancestor` reports null because the upstream created-item chain ends in a Lean module name. I retained that inherited provenance and its nonempty place and via list. Blueprint searches for `torus`, `Smith` and `independent characters` return no blueprint matches; `same_as` remains empty.

The route needs roots even for a nonprimitive character. Assuming the independent characters extend to an integral basis would be false: on the rank-one torus the character with exponent 2 is independent, but is not a basis of its character lattice. The proof instead uses the existing general Smith-basis leaf, retaining all nonzero diagonal integers and solving the corresponding power equations. No smoothness or separability of these power maps is asserted.

## Unfinished work

None for this one-level split. Its dependencies are existing nodes. No child statements are being deferred by this delivery.

## Not duplicates

No new nodes were created. `lem-sfb-split-torus-hom-matrices` supplies the full exponent-vector description, so I reuse it. `lem-sfb-pid-submodule-smith-bases` already supplies the general submodule statement, so I reuse that leaf instead of creating an abstract extension or diagonalization node. `lem-sfb-torus-finite-character-separation` only separates finitely many characters at one point; it does not prescribe their values. `lem-sfb-torus-endomorphism-kernel-dichotomy` concerns square endomorphisms and a scheme-theoretic dichotomy; it is not the present rectangular prescribed-values result.

## Review by Q11

I checked the split against delivery-errors B--E with the actual cited statements open. There are no new-node shape or source obligations: the only delivered node is the item, and its statement and notions are preserved. The proof is an argument, not a list of clause restatements or new lemmas carrying its conclusion. Each step is below 600 characters; there are no long steps hiding a further lemma. The field-root, homomorphism and finite-basis calculations are written explicitly. No SGA source is used.

Step 1 uses `lem-sfb-split-torus-hom-matrices`, whose statement explicitly gives an isomorphism of abelian groups between integer matrices and group-scheme homomorphisms, with the displayed formula on every scheme's points. Specializing target rank to one applies over our field F, with no characteristic hypothesis. Composition with the chosen isomorphism from the standard torus preserves all character identities. Consequently independence transfers to integer vectors. Subtracting expressions proves uniqueness in their span, and adding coefficients proves that the displayed formula for h_N is a homomorphism. Those are direct calculations, not an unquoted extension theorem.

Step 2 uses `lem-sfb-pid-submodule-smith-bases`. I read its entire statement and the exact Mathlib declaration `Submodule.exists_smith_normal_form_of_le`, `Mathlib/LinearAlgebra/FreeModule/PID.lean:492--497`. It allows arbitrary N contained in O in a finite free ambient module and supplies both finite bases and the diagonal equality, exactly as used. Here the ambient module is Z^r, O is the entire module, N is an actual submodule, and Z is a PID (the standard integer instance for this Mathlib specialization). The node does not require equal ranks or a saturated submodule. The proof deliberately avoids any extra theorem comparing basis cardinalities: its indices n and o need not be identified with m and r. The nonvanishing of each diagonal entry follows immediately from its corresponding basis vector being nonzero.

Step 3 uses only `def-weil-algebraic-closure`, whose statement expressly says every nonconstant polynomial over an algebraically closed field has a root. For each diagonal integer I checked that its absolute value is strictly positive, that the chosen polynomial has degree that positive number, and that its constant term is nonzero because d_j lies in F^times. Thus every chosen root is a unit. For a negative diagonal integer the polynomial uses d_j^{-1}, giving w_j^{a_j}=d_j with the correct sign. No theorem on divisible groups is used. The checks remain valid when the characteristic divides the diagonal integer: repeated roots do not prevent existence.

Step 4 cites no node because it explicitly defines the value on each unique finite basis expansion. The integer-power identity proves multiplicativity, and the written expansion of an arbitrary element of N proves restriction equals h_N. This is a basis calculation, not an assumed general theorem about extending homomorphisms.

Step 5 reuses the precise monomial formula in `lem-sfb-split-torus-hom-matrices`. Evaluation at the standard coordinates h(e_k) gives the displayed character values by the homomorphism law. The source of the matrix theorem is Milne Theorem 12.9(a); the statement supplies evaluation on all test schemes, so it in particular supplies F-points. I checked the trivial-rank case and the empty-family case explicitly: in rank zero independence forces the index family empty, and the trivial torus has its unique point. In all other ranks with an empty family the identity point suffices.

Additional small cases checked: the single exponent 2 over an algebraically closed field; exponent -2; exponent p over an algebraically closed field of characteristic p; and the independent nonprimitive pair (2,0),(1,3) in Z^2. In the last case h_N is well-defined although the original vectors do not form an ambient basis; the Smith diagonal equations handle the finite-index obstruction. Algebraic closedness is essential (over R the square character cannot attain -1), and independence is essential (two equal characters cannot attain 1 and 2 simultaneously). Neither missing hypothesis is silently supplied in the proof.

I searched the whole DAG for the character, lattice and Smith facts before selecting the existing nodes, and checked their combined statement/proof dependency closures do not reach the item (71 and 2 nodes respectively). I recorded actual Q11 Mathlib queries using msearch.py, including two phrasings, and read their results. The abstract divisible-group extension results found by LeanFinder/LeanSearch do not directly state the torus item; they were not turned into a duplicate node. The actual Smith leaf is already in the DAG. All new search entries copy the query/tool and logged result exactly; there were no unavailable services. Inherited Q70 searches are preserved separately.

I generated each citations.json quote from the cited node's statement and checked substring membership. The proof-dependency list is exactly the union of step uses. Statement dependencies are unchanged and no additional objects are introduced in the statement. No off-unit tool use is needed: the monomial theorem belongs to the same unit, the Smith theorem and algebraic-closure definition are Mathlib leaves. Nothing from the proof of a cited node is used in place of its statement.
