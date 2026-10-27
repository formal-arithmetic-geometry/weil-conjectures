# Worker report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-binomial-monoid-tensor-universal-property.json: split item, statement and statement dependencies unchanged, six explicit proof steps.
- dag/nodes/sec-trace-formula/lem-trf-integer-monoid-algebra-universal-property.json: one new statement, Mathlib leaf. AddMonoidAlgebra.lift over the integers supplies the bijection; lift_single and lift_apply' supply the basis and finite-sum formulas; lift_unique' supplies uniqueness. No proof is put into this leaf.
- citations.json: one verbatim statement quotation for each node cited by each proof step.

## Attachments

None. Searches for the item tag, binomial/monoid-algebra language, and the generic monoid-algebra declarations in lean/WeilConjectures and dag/lean_names_upstream.json found no project declaration proving every clause of the item. Mathlib's general lifting statement is a leaf, not an attachment. The parent's sorry declaration is not a completed proof of this more general arbitrary-monoid item.

## WANTED

None. I read ILO Expose VI Proposition 1.9, printed p. 71, PDF page 77, and the pinned Mathlib source. ILO omits these affine-ring calculations, so the item's proof_origin is agent, with ILO identified as context rather than a source claiming the general calculation verbatim. No external document was downloaded.

## Problems found and corrected

The item was an unsplit statement with no proof. Its statement is correct as written and was preserved: no cancellation or fine/saturated assumption is needed for the quotient evaluation. The existing search records belong to its creation by Q112 and were retained. Additional actual Q64 searches and their recorded results were appended; no prior search was misrepresented as a Q64 query. The sandbox was empty of item/report/search data when work started.

The historical ancestry of this item passes through the ILO nearby-cycle route below lem-trf-local-term-locality. I read the current literature/blueprint/latest files (main-20261023-1620) for the chapter, sk-i-curve-zero, and lem-trf-local-term-locality and its proof. The current unit and ancestor follow contracting correspondences. This delivery only proves the already-created algebraic auxiliary item used by lem-trf-nodal-divisorial-chart; it does not replace or rewrite the current unit route. The blueprint.from chain was retained, and the new leaf makes its historical context explicit. No SGA source is used.

The first broad grep for AddMonoidAlgebra lifting returned multiplicative-namespace declarations because the search wrapper caps results per file. I narrowed the actual logged grep until it returned the additive declaration at line 607 and its evaluation at lines 613 and 633; I also read lines 600--652 directly. Some remote service answers use older tensor theorem naming; matching was assessed against the local pinned source, not names alone.

## Not duplicates

lem-trf-integer-monoid-algebra-universal-property vs lem-trf-congruence-polynomial-kernel: the new leaf extends an arbitrary monoid homomorphism to the integer monoid algebra; the existing node computes the kernel of the algebra map induced by a quotient congruence and its relation generators. Neither computes the other's statement.

lem-trf-integer-monoid-algebra-universal-property vs lem-trf-ideal-monomial-relation-congruence: that node proves that a relation defined by monomial differences lying in an ideal is a congruence and gives a generated-congruence containment test. The new leaf neither mentions ideals nor asserts any congruence criterion.

lem-trf-integer-monoid-algebra-universal-property vs lem-weil-pbc-algebra-tensor-base-change-universal-property: the existing Mathlib leaf concerns maps from a tensor product of two already supplied algebras; it is reused in step 5. The new leaf constructs a map from the free integer monoid algebra before this tensor property applies.

lem-trf-integer-monoid-algebra-universal-property vs lem-trf-binomial-monoid-tensor-universal-property: the item handles a particular generated congruence, compatibility with the nontrivial Z[R] action, two generators, and xy=beta(b). The general monoid-algebra leaf supplies only the linear extension in step 4; it is not the item or a clause renamed as a lemma.

I searched the whole DAG by monoid-algebra/congruence/universal-property concepts and Mathlib declaration names, and ran tools/blueprint_refs.py searches for monoid algebra, monoid congruence, free commutative ring and monoid. No blueprint node states the new leaf or the item. No shared Stacks tag is introduced: the new leaf's precise source is Mathlib, and no Stacks tag states the specialized nodal calculation.

## Review by Q64

I read the item alongside ILO VI Proposition 1.9 on printed page 71: the source defines Q by the cocartesian square N -> N^2 and N -> Z x P and then asserts the affine monoid-algebra square is cartesian. The arbitrary-monoid beta formulation here is the isolated affine-ring calculation underlying that assertion; I checked it directly rather than importing the fs conclusion or a logarithmic smoothness theorem. I read the new leaf against AddMonoidAlgebra.lift at 607--611, lift_apply' at 613--614, lift_single at 633--635, lift_unique' at 641--643, and lift_unique at 647--651. Set the coefficient ring to Z and use Multiplicative M; the displayed basis and finite-sum formulas then say exactly what the leaf claims. The free abelian group description is the finite-support integer module defining this algebra, and no comparison theorem is hidden in the match. I read def-weil-pbc-free-module: it states exactly the basis expansion and its uniqueness, and the new leaf cites it with coefficient ring Z. The first full dry run requested a definition-node citation; I repaired that omission by writing free Z-module with this citation, without changing the mathematical statement or adding a node.

Step 1 cites lem-weil-pbc-algebra-tensor-pushout-universal-property. I opened its statement: clause (1) supplies exactly the commutative tensor ring, the displayed pure-tensor multiplication, and both canonical ring maps. Both factors here are commutative B=Z[R]-algebras, so its hypotheses apply. Taking A as the left factor gives the claimed A-structure; no flatness is used.

Step 2 cites def-weil-pbc-module-tensor-product, whose statement explicitly gives the bilinearity relations and generation by pure tensors. I checked which scalar acts on each side: [r] acts on A by beta(r) and on T by [g(r)], giving 1 tensor [g(r)] = beta(r) tensor [0]. Multiplication and u+v=g(b) then give the product relation. A representative of any q is (i,j,r), and expanding the finite integer support in T proves the two-generator assertion. This is the written elementary calculation from that definition, not an appeal to a flatness or presentation theorem.

Step 3 cites no theorem: it writes the monoid map, its multiplication and unit, and the kernel equivalence relation. Its additive compatibility is multiplication by f(w), which never needs f(w) to be invertible. Since the relation contains the defining pair, the definition of generated congruence as an intersection gives containment. Evaluation is consequently independent of every representative, not just one rewriting move. This uses neither a normal form nor cancellativity.

Step 4 cites the new Mathlib leaf with M=Q_b and C the given commutative target. Its hypotheses are exactly step 3's multiplicativity and unit. Its statement supplies the ring map with the required basis values. The proof then checks h gamma = iota alpha on each basis element of Z[R] and explicitly extends to finite integer sums. This is why the next step is allowed to treat h as a B-algebra map; no compatibility is assumed without proof.

Step 5 cites lem-weil-pbc-algebra-tensor-base-change-universal-property. I opened its full statement: the target must be an algebra over the new base and, by restriction, over the original base. Here those are A and B respectively; the target is the supplied A-algebra C and step 4 proves the required compatibility of h. Its inverse has the exact formula lambda tensor z -> iota(lambda) h(z). I also checked the general t in B balancing relation explicitly, rather than checking just the monoid basis. Thus the generated congruence and all additive and balancing relations are accounted for separately.

Step 6 is an elementary application of step 2's actual finite monomial expansion: any A-algebra map is fixed by its values on U_D,V_D and on scalar coefficients. It proves both uniqueness for the constructed evaluation and the assertion about arbitrary pairs of homomorphisms; it does not merely cite an abstract generation slogan.

I tested R=0, b=0, where the relation is uv=1; R=N, b=1 with beta(1)=0, where the relation is uv=0; and a noncancellative idempotent monoid R={0,e}, e+e=e, with beta(e) an idempotent. In the last case beta(e)^2=beta(e) verifies exactly the extra monoid relation, and the same kernel-congruence proof still works without cancellation. If A is the zero ring, every unital A-algebra C is also zero, and all formulas and uniqueness remain valid. For the new leaf M=0 gives Z and its unique integer algebra map; idempotent or torsion monoids require only the multiplicativity already assumed of f. No unit, nonzero, finite, or saturation hypothesis was introduced. Every proof step is below 2000 characters, and none hides a separately asserted comparison or identification. I checked B1--B10, C1--C8, D1--D5 and E1--E7 of delivery-errors against the files and the source, in particular the content of every cited statement (C4) and the sole non-elementary extensions (C1).

The two off-unit citations in steps 1 and 5 are existing Mathlib leaves, generic algebra tools rather than replacements of a unit step. The module tensor product is an existing definition/Mathlib leaf. No new off-route theorem is used.

## Unfinished work

None in this stage-1 item. No Lean files were written and no compiler, Lake or build tool was run. The new node is a Mathlib leaf, with no unsplit child. Server dry-run and push results are supplied by the delivery tool.
