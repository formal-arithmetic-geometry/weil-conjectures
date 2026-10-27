## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-symmetric-invariant-frobenius-projection.json`: item, statement split into seven proof steps; original statement and statement dependencies retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-tensor-product-basis-coordinates.json`: statement, Mathlib leaf. `Basis.piTensorProduct` (line 33), `Basis.piTensorProduct_repr_tprod_apply` (line 42), `Basis.piTensorProduct_apply` (line 49), in `Mathlib/LinearAlgebra/PiTensorProduct/Basis.lean` give all clauses.
- `citations.json`: a verbatim statement quotation for every dependency of each numbered proof step.

## Attachments

None. Read-only searches of `lean/WeilConjectures/` for the blueprint id, invariant tensors, orbit sums, Verschiebung and Frobenius twists found no declaration stating the item, or the new general tensor-coordinate lemma. The matrix orbit-sum and coefficient-sheaf Frobenius results concern other objects.

## Wanted sources

None. Milne's supplied PDF and the pinned Mathlib source suffice. No SGA source is used.

## Changes and source scope

Read Milne, *Algebraic Groups* (iAG2017), Section 11(i), printed pages 224–225 (PDF pages 236–237), specifically the invariant-tensor diagram, Definition 11.39, its functoriality and product clauses, and Proposition 11.40. Milne states the lambda arrow and pure-power normalization but suppresses its basis-level verification. The proof is therefore honestly marked agent-written: it supplies those calculations rather than attributing them to a nonexistent Stacks theorem. The Stacks sources of the reused leaves were also checked: Fields Tag 09FN (`lemma-vector-space-is-free`); Algebra Tags 00CX (tensor universal property) and 05G3 (module base change); the existing scalar-extension-basis node is a Mathlib leaf whose exact declaration was read.

The latest blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` was read, including `_section.md` and the direct-images proof. This item is a general linear-algebra prerequisite on its inherited Milne/Haboush/alteration chain, not a replacement for a unit step. The chapter/unit records remain untouched. `blueprint_refs.py ancestor` prints `None` for this already-created item; its original long `from.place` and `via` chain were preserved, and the new leaf inherits that exact null ancestor with the item prepended to `via`. All blueprint searches found no equivalent imported statement.

A broad DAG search found the already-existing `lem-weil-pbc-free-module-base-change-free`: it gives arbitrary bases after arbitrary ring maps, including the Frobenius map over an imperfect field. I reused it instead of creating the initially contemplated second leaf. The completed split creates only one node. Extra exploratory searches for orbit bases, multinomials and scalar extension remain in the genuine search log; they do not represent additional delivered nodes. Failed Loogle patterns were only exploratory, and the successful queries recorded in the node were read. The item retains its original Q43 search history and appends the searches actually run here.

## Not duplicates

lem-sfb-finite-tensor-product-basis-coordinates vs lem-sc-tensor-product-free-basis: the existing statement requires two finite bases. The new statement permits arbitrary infinite basis sets, a finite set of factors, and gives the coordinate product formula. Those extra hypotheses and formula are essential for arbitrary-dimensional M,N in the item, and the new statement is a direct Mathlib leaf.

lem-sfb-finite-tensor-product-basis-coordinates vs lem-sfb-tensor-word-basis: the existing statement identifies the entire tensor algebra with a free associative algebra. It neither states a basis or coordinate formula for the fixed finite tensor product nor provides the identification of a homogeneous tensor power needed here. The new statement is exactly the indexed tensor basis and coordinate formula in Mathlib, without a tensor algebra.

lem-sfb-finite-tensor-product-basis-coordinates vs lem-weil-pbc-free-module-base-change-free: that node concerns extension of scalars of one free module, not a tensor product of several arbitrary modules and its coordinate product formula. It is reused separately in steps 3 and 6.

Whole-DAG searches covered the statement text and declaration names (`Basis.piTensorProduct`, `Module.Basis.baseChange`), tensor bases, orbit sums, permutation modules, and factorial/multinomial formulas. Blueprint searches included `invariant tensors`, `permutation module`, `Frobenius projection`, `tensor basis`, `tensor product basis`, `finite tensor product`, `tensor coordinates`, `base change basis`, `scalar extension basis`, and `extension of scalars basis`. None states the new leaf. There is no shared Stacks tag on the new Mathlib-source leaf.

## Review by Q69

I checked the statement against Milne's lambda diagram, with the tensor ordering explicitly fixed by the node's relation `(am) tensor c = m tensor a^p c`. The item is true over imperfect fields; no inverse Frobenius is used. It is not restricted to finite-dimensional spaces. No source or statement correction is needed.

Step 1 uses the actual statement of `lem-weil-pbc-vector-space-free` for the existence of bases and the new leaf for the word basis. Invariance is coefficient constancy on orbits. Because each vector has finite support, grouping it by disjoint finite orbits is legitimate even for an infinite basis. This supplies spanning and independence, not merely a reference to a purported averaging projection. The permutation-basis proof is written in the step; no hidden group-representation theorem is assumed.

Step 2 uses no cited theorem: its entire finite-counting argument is written out. Count pairs of a word and a position occupied by a chosen letter in two ways. Transitivity of position permutations gives equal fibers. Thus r times the orbit size is p times an integer. Primality and 0<r<p imply divisibility of the orbit size by p. Only this elementary integer fact is used, with its hypotheses explicit. The proof never divides by p, p!, or a possibly vanishing scalar.

Step 3 reads the ring-homomorphism clause of `def-weil-ring-frobenius`, the arbitrary-ring-map basis conclusion of `lem-weil-pbc-free-module-base-change-free`, and the tensor balancing and scalar formulas of `def-weil-module-base-change`. These are precisely what this step needs. Specifying images on the orbit basis defines a real linear map, and the displayed diagonal coefficient formula is the actual definition. In particular a coefficient a in m becomes a^p in m tensor 1.

Step 4 uses the new leaf's pure-tensor coordinate formula, tensor generation from `def-weil-pbc-module-tensor-product`, and the induced scalar-extension map from `def-weil-module-base-change`. I checked the full coefficient of a constant target word: every source word in an orbit contributes the same product of the h_{ji}. For mixed source words the scalar is |O|=0 in k; for a constant source word it is h_{ji}^p. The equality with h(b_i) tensor 1 follows from step 3. This proves naturality for every linear map, including zero and noninjective maps, before basis independence is invoked.

Step 5 is the literal specialization h=id of step 4, allowing different source and target bases on the same vector space. This proves basis independence without a circular appeal to the already-canonical map. No external statement is used.

Step 6 uses the new leaf with a two-element factor set for arbitrary B,C, the existing scalar-extension basis leaf on M tensor N and on each factor, and the bilinear scalar-extension clause actually stated in `def-weil-module-base-change`. Those basis formulas prove that kappa is an isomorphism with the specified order and scalar ab. Tensor universality constructs interleaving and its unpairing inverse, and the written permutation equation proves invariance. Step 7 uses only the new leaf's coefficients and the definitions from earlier steps: the constant paired-word coefficient is the product of the two constant-word coefficients. Comparing the finite sums proves the requested tensor identity. The final balanced unit map and its inverse are both explicit, so the unit clause does not hide a perfection hypothesis.

For the new leaf I read Mathlib lines 25–54, including all three declarations. Finite refers to the factor index set; the basis index sets have no finiteness hypothesis. Its empty-factor clause is included in the same declarations. Its statement introduces every object, references basis and tensor definitions, carries no proof sketch, and is delivered with empty proof and proof-dependency arrays as a Mathlib leaf. The statement-only rule and B1–B10, C1–C8, D1–D5 and E1–E7 were checked against these actual files. The new leaf is general infrastructure; it is not a clause of the projection theorem. All other non-elementary inputs are cited existing Mathlib leaves; none imports an off-route unproved result. Citations quote verbatim node statements.

Small cases checked: M=0 or N=0 gives empty tensor-word bases for p>0 and zero maps; M=k gives the required unit. In characteristic 2, the orbit sum b tensor c + c tensor b maps to zero even after b is replaced by b+c. Over an imperfect field F_p(t), the scaling relation has t^p, exactly as required, and no pth root is taken. Infinite bases cause only finitely many coefficients in any calculation. As an additional arithmetic check, finite enumeration verified the diagonal coefficient formula for every binary word orbit and every 2 by 2 matrix over F_2, F_3 and F_5. For the new leaf, zero factors, an empty basis in a nonempty factor set, and infinite bases all satisfy its precise Mathlib hypotheses. All seven proof steps are below 2000 characters; none conceals a comparison lemma behind 'transport'.

## Completion

No unresolved mathematical work, no Lean files, no compiler/build commands, and no writes to the shared repository or launcher. Validation is through the required server checks and delivery dry run.
