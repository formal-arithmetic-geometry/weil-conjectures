# Q37: lem-sfb-central-diagonalizable-derived-intersection-finite

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-central-diagonalizable-derived-intersection-finite.json: item, statement retained exactly, split into four proof steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-diagonalizable-representation-weight-grading.json: one new statement-only node, unsplit; actual semantic, Loogle and source searches found no Mathlib match.
- citations.json: verbatim statements for every proof-step citation.

The sandbox also retains the extracted Milne text, actual search outputs, searches.jsonl and the script that wrote the JSON files. No repository, launcher or Lean files were written. No compiler or Lake command was run.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, diagonalizable/diagonalisable, faithful representations, central/derived terminology and related group-scheme notions found no completed declaration stating the item or the new lemma. Abstract-group commutator and Lie algebra results do not state this group-scheme assertion. The item had no lean_audit attachment and no released repair note.

## WANTED

None. The relevant source is present: literature/milne-algebraic-groups_iAG2017.pdf, Theorem 4.9 and Corollary 4.10 (printed p.87), Theorem 12.12 and Remark 12.13 (pp.234–235), and Proposition 12.46(a) and proof (pp.245–246). These are Milne sources, not Stacks claims; no Stacks tag or SGA reference is being attributed to them.

## Corrections and scope

The statement was not disputed or changed. The unsplit item had no proof or proof dependencies. Milne 12.46(a) is literally stated for a central torus and argues using rational points. The item's advertised extension to arbitrary diagonalizable C is valid, but requires scheme-valued weight spaces and scheme-theoretic determinant identities. The split supplies these and finishes with an explicit finite-dimensional coordinate quotient. It does not try to separate characters on C(F), which would fail for nonreduced diagonalizable C. The proof_origin is marked agent because this is an extension of the source argument.

The existing node lem-sfb-central-torus-faithful-weight-blocks already gives a faithful representation for any affine finite-type G by taking its allowed rank-zero torus. Creating a new faithful-embedding theorem would duplicate that conclusion. The new node is instead the missing general representation theorem for D(M) with torsion M. It is strictly smaller than the item: it concerns representations only, with no central inclusion, smoothness, derived group or finiteness conclusion.

I read the chapter record, unit record and current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The item is a deep supporting input to the inherited alteration/moduli/representation route under direct-images step (3), not the unit's key statement. No unit record or higher route was changed. The inherited blueprint.from.node is null (also the result of tools/blueprint_refs.py ancestor); its existing precise place and via chain are preserved, and the new node extends that chain by this item. Searches with blueprint_refs.py for diagonalizable, diagonalizable representation, weight decomposition, faithful representation, central torus, comodule and grading found no blueprint theorem stating the new lemma. Whole-DAG statement/title searches and Lean-source searches likewise found no general arbitrary-diagonalizable weight-grading theorem.

## Not duplicates

lem-sfb-diagonalizable-representation-weight-grading vs lem-sfb-split-torus-representation-weight-decomposition: the existing node assumes D(Z^r); the new node allows arbitrary finitely generated M including p-primary torsion, and gives base-change and commutant clauses for that generality. The existing split cannot be cited for those hypotheses.

lem-sfb-diagonalizable-representation-weight-grading vs lem-sfb-gm-representation-weight-basis: the existing node treats the multiplicative group, not arbitrary diagonalizable group schemes with torsion character group.

lem-sfb-diagonalizable-representation-weight-grading vs lem-sfb-central-torus-faithful-weight-blocks: the existing node embeds an ambient group and decomposes a central split torus representation; it does not decompose representations of nonreduced diagonalizable groups.

lem-sfb-diagonalizable-representation-weight-grading vs lem-sfb-comodule-finite-subcomodule: the existing node places a finite set in a finite-dimensional subcomodule; it does not identify a comodule with the sum of its homogeneous character spaces.

lem-sfb-diagonalizable-representation-weight-grading vs lem-sfb-diagonalizable-group-geometric-criteria: the existing node classifies group schemes and their smoothness/connectedness, not their representations. A product decomposition of the group does not itself state the representation theorem.

lem-sfb-diagonalizable-representation-weight-grading vs lem-sfb-split-torus-subgroups-diagonalizable: the existing node classifies closed subgroups, not representations. No source Stacks tags collide.

## Review by Q37

I checked B–E of coord/delivery-errors.md against the actual files and the source. The new node introduces its field, character group, Hopf algebra, group scheme, representation, vector space and all test algebras, and defines its weight spaces by all algebra-valued points. Its statement dependencies actually define the displayed notions. Its proof, proof_deps and proof_origin are empty; its intended argument is recorded here, not hidden as a proof in its statement. It has the required blueprint origin and actual Mathlib searches, with the complete returned hits preserved. Both semantic phrasings were read: Rep.diagonal is an abstract-group construction, AddMonoidAlgebra.grade gives a grading of the algebra itself, and the Coalgebra/GroupLike hits do not assert a weight decomposition of an arbitrary coaction. Loogle found no Comodule/DirectSum match and both relevant source greps found no match. The item's commutator hits likewise concern abstract groups or characteristic-zero Lie algebras.

For the new lemma I read Milne 12.12(a) implies (b),(d), and Remark 12.13. The proof expands the coaction as theta(v)=sum_m p_m(v) tensor e_m. Coassociativity gives theta(p_m(v))=p_m(v) tensor e_m, the counit gives sum_m p_m(v)=v, and coefficient extraction gives orthogonal projections p_m. Supports of finitely many spanning vectors give finitely many nonzero weights. These projection formulas remain valid after every algebra extension because the group algebra still has the basis e_m. To verify the commutant clause over A, evaluate the universal C-point in A[M]: commutation gives (u tensor 1)theta_A=theta_A u. Comparing coefficients of e_m gives u p_m=p_m u. This proves preservation of each base-changed weight space without assuming A reduced, C smooth or characters distinct on rational points. This is the non-elementary representation input isolated as the single new node.

Step 1 cites the full statement of lem-sfb-central-torus-faithful-weight-blocks. It explicitly allows r=0, assumes only affine finite type for the ambient group and supplies nonzero V and a closed-immersion representation. I checked the trivial subgroup is closed by the counit and central by the identity law, so no unavailable torus theorem is being invoked. Its statement, not its internal proof, is used.

Step 2 cites exactly the new grading statement. It supplies the finite decomposition, scalar action and preservation by every endomorphism commuting after all algebra extensions. Centrality in the item has precisely that all-algebras strength, so each g and its inverse meet the commutant hypothesis. Restricting a block-diagonal matrix representation is a regular group homomorphism by its coordinate entries, with inverse the corresponding block of the given inverse; this is the explicit elementary assembly, not an extra centralizer theorem.

Step 3 cites def-sc-general-linear-group for the determinant homomorphism, which its statement explicitly provides, and lem-sfb-smooth-connected-derived-subgroup for vanishing of every homomorphism to a commutative affine group. G is smooth, connected, affine finite type over the algebraically closed F, just as required. The target G_m is commutative affine by its displayed group law. This is scheme-level vanishing, so after restriction to K the functions satisfy a_i^(d_i)=1 even when K is nonreduced. The determinant of a scalar matrix is directly its scalar to the positive block dimension.

Step 4 cites the definitions of a closed subgroup and affine closed immersion, and the explicit coordinate algebra of GL. Closed subschemes of an affine scheme have quotient coordinate rings; their intersection is cut out by the sum of their ideals. The two resulting surjections compose, giving the surjection from the displayed GL coordinate algebra onto F[K]. Every matrix entry has the stated scalar-block restriction, and the determinant inverse is 1 using step 3. Hence the a_i generate the entire ring, not just a subalgebra of it. Reducing exponents in the displayed finite-generator quotient gives the finite spanning family explicitly. The final step is elementary algebra from these cited definitions and the preceding identities; it hides no finite-points-to-finite-scheme theorem or separate finiteness lemma.

For C trivial or G commutative, the argument gives a trivial intersection, as it should. For C=G_m central in GL_n, it gives K=mu_n. For G=SL_p and C=mu_p in characteristic p, it allows the single standard-representation weight block of dimension p and the nonreduced algebra F[t]/(t^p-1), so it does not incorrectly conclude etaleness or order prime to p. For the grading node, M=0 gives only weight zero; V=0 gives an empty support; M=Z/p with k of characteristic p still has distinct basis elements e_m in k[M] and the projection proof works. The zero test algebra also causes no exception. Each d_i used in exponent reduction is strictly positive because only nonzero weight blocks are enumerated and V is nonzero. These checks expose the exact place where rational-point reasoning would have been insufficient and confirm the replacement.

Every proof citation has its full verbatim statement in citations.json. All non-elementary steps are below 2000 characters. No off-unit theorem replaces the route: the two existing theorem citations have the same unit; the remaining existing nodes are definitions. No tool_uses declaration is needed. There are no uncompleted mathematical parts of the split; the new statement-only lemma is deliberately left for its own later split.

## Validation

The required server dry run exited successfully: OK (not pushed), commit d918b71307f, preflight passed (including check_dag and review_split). The delivery push runs the same gates again. No mathematical or node-file change was made after that dry run.
