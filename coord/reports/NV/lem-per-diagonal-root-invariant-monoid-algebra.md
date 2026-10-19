# Stage-1 report: lem-per-diagonal-root-invariant-monoid-algebra

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-diagonal-root-invariant-monoid-algebra.json`: statement node, split into eight proof steps; the statement is unchanged. Five current logged Mathlib searches supplement the inherited searches. No exact Mathlib match was found for the item.
- `citations.json`: a verbatim statement quotation for every node cited by each proof step.
- `report.md`: this report.

There are **0 new nodes and 0 new Mathlib leaves**. The proof reuses the existing monic-quotient and free-module-base-change Mathlib leaves, plus existing definitions. `searches.jsonl` is the search command's own log, preserved as written.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id and for diagonal invariants, invariant monoid algebras and root power bases. There is no project declaration stating the item. The monic root power-basis ingredient is already a Mathlib leaf (`lem-weil-pbc-monic-quotient-free`), not an attachment for the item.

## WANTED

None. The ILO PDF, local Stacks source and pinned Mathlib sources used in the review are present.

## Problems found and changes

The imported item had no proof. I kept its statement, its rational-lattice convention, the original source, `created` and blueprint ancestry, and all inherited searches. The proof now explicitly proves the invariant-ring assertion, rather than relying on ILO's asserted identification over a regular local base. Since the residue-box proof and coefficient argument are supplied by me, `proof_origin.by` is `agent`, with the exact ILO place being expanded recorded there.

There is a provenance issue worth distinguishing from a statement error. The inherited `blueprint.from.place` refers to historical Step 3 of `lem-per-artin-gabber-affine-curve`, a uniformization input. The current ancestor has a reviewed BBD proof whose Step 3 is adjunction, and the main-20261015 blueprint file contains the ancestor's statement with no such uniformization proof. I preserved the item's ancestry and explicitly recorded this in `split_report.blueprint`; I did not silently claim the current ancestor Step 3 states this algebra lemma. The direct parent is still `lem-per-prime-to-order-snc-kummer-charts`, whose assigned descendant this item is. No unit or chapter record is changed.

A zero coefficient ring needs separate treatment before saying a monic polynomial has degree n: over the zero ring the usual degree of the zero polynomial is not n. Step 3 disposes of the zero-ring algebra assertion first. For the nonzero branch, the power-basis induction keeps every intermediate root algebra nonzero, so the degree-n use of the monic-quotient leaf has its hypotheses. This corrects a potential proof gap without changing the statement.

No new node is needed for the finite-generation/saturation argument, invariant coefficient calculation, or comparison of the two explicit bases: those arguments are written out in the proof. No clause is moved into a child with a renamed statement. I also did not introduce a separate multivariable basis node; the short induction from the existing monic-quotient leaf supplies it.

## Searches and reuse

I read the chapter and unit records, `coord/brief-stage1.md`, `stages/1-dag.md`, SETUP's three levels, GOAL, dag-sync, the worker role and delivery-errors B--E. I used `tools/blueprint_refs.py ancestor` and the whole-blueprint searches for `monic`, `monoid`, `Kummer`, `monoid algebra` and `diagonal root`. The last two searches returned no matching blueprint node. Whole-DAG keyword searches, followed by inspection restricted to actual statements (to avoid matches in old search results), found the existing monic-quotient leaf, free-module-base-change leaf and the definitions used. The existing triangular field normal-form node has field/localization hypotheses and is unnecessary; the existing monic tensor presentation can also be bypassed by the short direct induction.

The five new searches are exactly the queries in this sandbox's `searches.jsonl`: two LeanFinder phrasings, Loogle, grep and LeanSearch. I read the returned types. They give general invariant-subalgebra definitions, field-only Kummer automorphisms, cyclotomic characters, Lie root-system weight spaces and unrelated invariant notions. None proves this arbitrary-ring parameter-root quotient/monoid-base-change identity, let alone its fs sharp lattice clauses. All services answered; no failed service is reported as a negative search. The full pre-existing search record is retained.

## Review by NV

I read ILO Expose IX Proposition 2.1 and its proof on printed pp.133--134 (PDF pp.139--140), Expose VI 1.1 on printed p.69, and VI 2.2--2.3 including (2.a) on printed pp.72--73. The specific input used from IX is the displayed root-algebra invariant identification and the standard Kummer chart; the source's separate normalization, log-regularity, and tame-cover theorems are not taken as algebraic lemmas. This proof establishes the displayed identity directly over the more general ring of the item. No outside theorem concerning tame covers or resolution is used.

For Step 1, I checked the homomorphisms defining L, that every integral vector has zero character, and that reduction of the numerator modulo n embeds L/Z^r in a genuinely finite product. All claims follow directly from the definitions; no structure theorem for lattices or finite abelian groups is implicit.

For Step 2, I opened `def-trf-fs-log-blowup` and checked its actual definition: finite generation, injection into group completion and the positive-multiple saturation condition. Only this monoid clause of the definition is used, not any of its locally Noetherian log-scheme setting. Division of each nonnegative numerator by n gives a unique residue-box representative and a nonnegative integral remainder. Shifting any element of L by a sufficiently positive integral vector proves Q generates L. Equality of fractions is equality of cross sums in the embedded monoid. Coordinate signs prove both saturation and sharpness. Thus no uncited Gordan lemma, normality theorem or structure theorem hides here.

For Step 3, I opened both the polynomial evaluation definition and the algebra/quotient definition and verified that they give exactly the generators and relations used for the successive quotient identification. I opened `lem-weil-pbc-monic-quotient-free`, whose statement explicitly supplies the powers below the degree as a basis. I read `AdjoinRoot.powerBasis'` and its `basis_eq_pow` in the pinned Mathlib `RingTheory/AdjoinRoot.lean` (around lines 633--646), and the local Stacks power-basis passage in `algebra.tex`, `lemma-affineline-special`. The induction includes its base, spanning and coefficient-by-coefficient uniqueness. I checked the base ring changes to B_j at each application, and handled A=0 before making any degree assertion. Neither a field hypothesis nor invertibility of any parameter is used.

For Step 4, the two cited definition nodes really supply the polynomial substitution and quotient data; the basis used is the already-proved Step 3. The H-action preserves every relation because zeta^n=1 and is independent of representatives modulo n. The coefficient identity is written down, with a particular h chosen separately for each nontrivial residue character. The hypothesis making 1-zeta^c a unit is applied only at 1<=c<n. This is valid over rings with zero divisors, and it does not appeal to semisimplicity or to commuting invariants with base change.

For Step 5, I checked the bijection P times S -> Q as a bijection of sets with P-action, not an assertion of a product of monoids. The statement already defines monoid-ring elements as finite integral sums. Grouping that basis by its unique residue-box representative proves the free Z[P]-module assertion directly, so no freeness claim is inferred merely from finite generation.

For Step 6, I opened `lem-weil-pbc-free-module-base-change-free`; it gives exactly the displayed basis after arbitrary ring base change, without a flatness assumption. I read `Module.Basis.baseChange` and `baseChange_apply` in `LinearAlgebra/TensorProduct/Basis.lean` (around lines 64 and 73). I also opened `def-weil-pbc-module-tensor-product` and read local Stacks Tag 00CX, `algebra-lemma-tensor-product`, checking its bilinear universal property and the generation by pure tensors. The monomial map has invariant image by the definition of L, agrees with the specified structure map on every z^m for m in P, and hence is balanced. Its multiplicativity is checked on pure tensors using the explicitly written product, then extended by distributivity. No tensor/invariants interchange theorem is used.

For Step 7, the only cited node is the tensor definition: its balancing relations give the parameter identity. The inverse is explicitly the inverse coefficient expansion between the two bases already constructed in Steps 4 and 6. This proves bijectivity of the particular algebra map rather than asserting an unspecified isomorphism. The nth-power formula uses nq in P and holds for every q, with no cancellation of a parameter.

Step 8 checks r=0 and n=1 directly. I additionally tested H=0 (all reduced monomials survive), H=(Z/nZ)^r (only b=0 survives, giving A), and n=2, r=2, diagonal H (the surviving residues are (0,0) and (1,1), with (x_1x_2)^2=t_1t_2). With A=Z/9Z, n=2, zeta=-1 and t_i=0 the parameters and roots may be nilpotent, but the same coefficient calculation still works. The zero-ring case is treated separately in the text. All remaining hypotheses are exactly those in the item; invertibility of n is retained even though the explicit coefficient proof does not need it beyond the stated root assumptions.

Against delivery-errors B: there are no new statement-only nodes to mis-state, duplicate or leave unsearched; every added statement dependency is an existing definition of the notion actually used. JSON TeX is encoded once. Against C: I opened every cited node's statement, quoted it verbatim in citations.json, and matched each use to the clause described above. The only non-elementary ingredients are the monic power basis and base change of a basis, both existing Mathlib leaves; generic definitions and all coordinate computations are written out. Against D: the parent carries the full argument and has no new children, no self citation and no circular induction. Against E: I checked the actual coefficient ring at each power-basis application, the unit cancellation, the exact exponents in the lattice and algebra maps, and all boundary cases. No non-elementary proof step exceeds 2000 characters; the longest step is about 1150 characters and its induction is explicit.

## What could not be finished

Nothing in the mathematical split remains unfinished. The required remote dry run and delivery are the remaining procedural checks when this report is first written.
