# Q115 stage-1 delivery: lem-sfb-smooth-diagonal-additive-crossed-vanishing

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-diagonal-additive-crossed-vanishing.json: item, statement unchanged, four-step split; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-diagonal-prime-to-characteristic-torsion-density.json: new statement-only supporting lemma, unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for every citation of every item step.
- searches.jsonl: genuine msearch.py query records; the search command wrote this file.
- report.md: this report.

## Attachments

None. Searched the read-only live WeilConjectures tree both for the exact blueprint tag and for crossed homomorphisms, diagonalizable groups, additive subgroups and torsion density. No declaration gives the item or the new geometric lemma. Abstract cocycle declarations do not give this assertion about regular scheme morphisms.

## Literature

No WANTED documents. I read Milne, Algebraic Groups (2017), Proposition 15.3 and its proof, printed p.303, and its preceding definition of principal crossed homomorphisms, p.302. For the new node I read Proposition 12.3, Remark 12.5 and the group-algebra construction, pp.231–232, and Theorem 12.32 with its proof, p.242. I also read the existing additive-subgroup polynomial quotient node, including its complete statement and proof; its source is Milne Exercise 14-3(a), Example 14.40 and Theorem 15.34(d). No SGA source is used.

## Defects found and changes

The imported item is true as stated; its statement and statement dependencies are unchanged. Its proof was empty. Milne 15.3 is formulated for group varieties, whereas this item allows nonsmooth additive subgroup schemes; simply citing the proposition would not justify that extension. I kept the averaging proof and supplied division inside the actual N(F), using the already existing additive-polynomial node. Thus no use of a possibly unproved reduced-subgroup construction is needed.

Milne's displayed descending sets M(n) require a divisibility-directed choice of indices: consecutive integers do not have nested torsion kernels. Rather than reproduce a literal M(n) superset M(n+1), I explicitly compare indices through lcm(n,n0). For a nontrivial scalar character, a torsion point at which it is nontrivial uniquely fixes the averaged element. For a trivial character, averaging already gives zero on every torsion subgroup. This supplies the compatibility required by the source's argument. It does not change the item's statement or its unit route.

## Blueprint and duplicate searches

Read the chapter and unit records and the three levels in SETUP.md. Read the current latest blueprint sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially proof (3). The long inherited alteration/moduli chain is an existing prerequisite chain; this split only expands its algebraic-group input. tools/blueprint_refs.py ancestor returns None, so both item and new node retain a null ancestor; the new node prepends this item to the inherited via chain and names the exact local Milne step.

Ran whole-DAG statement/source searches for diagonalizable groups, additive subgroups, crossed homomorphisms, rational-point density, prime-to-characteristic torsion, Milne 12.32 and 15.2. Ran tools/blueprint_refs.py search for crossed homomorphism, diagonalizable, dense rational, torsion density, multiplicative type, torsion, roots finite, and prime-to-characteristic torsion. No node states finite torsion kernels together with their schematic density. The blueprint rational-point density lemma does not give density of torsion points. Searched current latest blueprint text as well. No existing node can replace the new node.

## Not duplicates

lem-sfb-smooth-diagonal-prime-to-characteristic-torsion-density vs lem-pc-rational-points-dense: the existing node gives topological density of all rational points of a smooth scheme over a separably closed field; it neither restricts to prime-to-characteristic torsion nor gives finite kernel orders or schematic density.
lem-sfb-smooth-diagonal-prime-to-characteristic-torsion-density vs lem-sfb-multiplicative-character-antiduality: the existing node gives character anti-equivalence, descent and base-change identifications, not the torsion-density theorem.
lem-sfb-smooth-diagonal-prime-to-characteristic-torsion-density vs lem-sfb-smooth-diagonal-additive-crossed-vanishing: the new lemma mentions no action, additive subgroup or cocycle and supplies only the finite averaging index sets and a geometric regular-function detection theorem. All cocycle averaging and assembly remain in the item.
lem-sfb-smooth-diagonal-prime-to-characteristic-torsion-density vs lem-sfb-additive-subgroup-polynomial-quotient: one concerns torsion in diagonalizable groups; the other concerns additive polynomials and a quotient of the additive group. The latter is reused, not recreated.

## Mathlib searches

All added records are exact queries run through msearch.py and read before writing the verdict. Both semantic phrasings for the item returned abstract group-cohomology or Galois Hilbert 90 declarations; these concern different actions and do not assert regular cocycle vanishing for algebraic groups. The Loogle IsCocycle/AddMonoidAlgebra query and the crossed-hom/diagonalizable grep had no hits. For the new node, both semantic phrasings returned number-field, abstract torsion, finite-field sum, model-theoretic or ordered-topological density results. They do not give geometric density on a diagonalizable group scheme. The IsZariskiDense/torsion Loogle query and AlgebraicGeometry grep had no hits; the broader grep found only unrelated convex geometry lines. LeanSearch also ran successfully, returning abstract torsion definitions. No service outage was recorded as a negative search. The new node has no proof or proof dependencies.

## Review by Q115

I checked the four steps against Milne and opened every node actually cited. In step 1 the new torsion node explicitly gives each finite H_n and the order prime to the characteristic, so the scalar e_n is invertible in F, also in characteristic zero. The subgroup definition explicitly puts N(F) inside the additive group of F. The additive-polynomial quotient node explicitly states that the proper subgroup is the kernel of its monic additive P; repeated additivity proves P(e_nb)=e_nP(b). Consequently division by e_n preserves N(F). This uses only the quoted parts of the cited statements, not any construction hidden in their proofs. N=Ga is treated separately, because the polynomial node requires a proper subgroup.

Step 2 is elementary: a finite permutation of the summation index and cancellation of the nonzero field scalar. I checked the sign: s=e f(x)+chi(x)s gives f(x)=(1-chi(x))(s/e), exactly the sign in this item. All values s and a_n lie in N(F). No claim is made that N is a vector subspace.

Step 3 uses the regular-function vanishing clause explicitly stated in the new node. The coordinate y and the correspondence between ring maps and affine scheme morphisms are stated by def-sc-gm-ga and def-weil-affine-spectrum. It proves equality as regular functions, so the conclusion holds over every algebra, including algebras with nilpotents, not merely on field-valued points.

Step 4 again uses precisely that regular-function test, first on chi*(t)-1 and then on the difference of the two additive coordinates. A nontrivial character has nonzero coordinate difference by the affine-spectrum and Gm descriptions. I checked the lcm inclusions and invertibility of 1-chi(h); this proves equality of the averaged a_m and the fixed a without assuming a nested sequence of all positive indices. Finally scalar stability and the subgroup definition put both sides in N(A), whose injection into A identifies the equality. The element a was already in N(F); an ambient scalar alone would not have sufficed.

For the new lemma, Milne 12.3 decomposes D(M) into Gm and mu_d factors; Remark 12.5 excludes characteristic-primary finite factors under smoothness. Therefore the n-torsion kernels for n prime to the characteristic are split reduced finite schemes with group orders prime to that characteristic. Theorem 12.32 states the schematic density. The regular-function formulation follows because a function zero at every point of a split reduced finite kernel is zero in its product-of-fields coordinate algebra. This last implication is part of the new statement and is not assumed without an interface in the item.

Tested D=1 and M=0 (all H_n singleton); D=mu_l with l prime to p (eventually H_n=D); a disconnected torus times mu_l; N=0; N=alpha_p and ker(T^(p^r)); N the constant additive F_p subgroup; chi trivial and chi with finite nontrivial image; and characteristic zero. Smoothness of D is essential to the supporting prime-to-characteristic density statement: D=mu_p would have trivial H_n for all allowed n while its scheme is nontrivial, so it is deliberately excluded. Neither connectedness of D nor smoothness/reducedness of N was inserted. No new statement is a restatement of a clause of the item. All four proof steps are shorter than 2000 characters.

## Validation and unfinished work

The standalone server review_split check passed. The first full dry run rejected the phrase “the item’s convention” as a self-containment flag; I replaced it by the explicit sign formula without changing the argument. The full deliver.py dry run and final delivery are run after writing this report. This is a one-level stage-1 split; the single new lemma remains statement-only for later work. No Lean was written and no compiler, Lake or build tool was run. Nothing was written to the read-only repository or launcher.
