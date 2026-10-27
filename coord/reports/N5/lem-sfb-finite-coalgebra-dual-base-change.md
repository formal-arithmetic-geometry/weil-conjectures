# N5: lem-sfb-finite-coalgebra-dual-base-change

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-coalgebra-dual-base-change.json: item, split, six proof steps; complete original assertion retained, with the finite-dimensionality definition added to stmt_deps.
- dag/nodes/sec-six-functors-basics/lem-sfb-convolution-linear-map-algebra.json: statement, Mathlib leaf. LinearMap.convRing and convAlgebra; product, unit and scalar formulas checked in Convolution.lean:55–68,174–193,212.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-free-tensor-dual.json: statement, Mathlib leaf. TensorProduct.dualDistribEquiv in Contraction.lean:462, with forward formula dualDistrib_apply in Dual/Lemmas.lean:1099.
- citations.json: one exact statement quote for every node cited in every proof step.

## Attachments

None. Searched lean/WeilConjectures for the item's blueprint tag, coalgebra, convolution, dual comparison names and groupLike. No declaration there states the full assertion. The general categorical convolution source is only a component; the Fourier convolution declarations concern different objects.

## WANTED

None. Milne's Algebraic Groups PDF, the latest blueprint and the relevant Stacks sources are present. No SGA source used.

## Audit of the imported item and sources

The original item is mathematically correct, including zero-dimensional D and noncocommutative coalgebras. Its initial dependency list omitted the finite-dimensionality definition; added the existing definition node without changing the statement. There was no previous sandbox split, report or search log to recover. The imported Mathlib searches were retained, and fresh searches recorded by msearch.py are appended, verbatim by tool and query. No search result was invented. The new-node searches are copied from searches.jsonl, and their candidate declarations were opened in the current source. Semantic services sometimes locate dualDistribEquiv in an old file; the current checked declaration is in Contraction.lean, not Dual/Lemmas.lean.

Read Milne §9(d), printed pp.174–175, the dual convolution construction, and equation (77) and Theorem 12.18, printed pp.237–238, including its pairing calculation and the characters producing group-like elements in (c)⇒(d). Those passages justify the route but suppress finite linear-algebra details; I supplied the separation argument and the scalar product calculation. proof_origin.by is therefore agent. Read Stacks fields.tex Tag 09FN (lemma-vector-space-is-free) and more-algebra.tex Tag 07VI (lemma-dual-perfect-complex), whose finite-projective termwise dual argument underlies the already-existing bidual node. The two new leaves use general module algebra, not results specific to algebraic groups.

Read the chapter and unit records, GOAL.md, worker rules, the three blueprint levels, and latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images proof. This algebraic input remains in the inherited alteration/linear algebra prerequisite chain below direct-images (3); it replaces no chapter or unit route. The blueprint ancestor command returns null for this old imported prerequisite chain; retained null with the existing detailed place and via chain, extending it for the new leaves. Blueprint searches for coalgebra, convolution algebra, dual, dual tensor, dual modules, tensor product of dual, and base change for the dual found no matching blueprint theorem. No unit realization fields are changed because this item is not the unit's key statement.

## Not duplicates

lem-sfb-convolution-linear-map-algebra vs lem-sfb-finite-coalgebra-dual-base-change: a general R-coalgebra-to-B convolution algebra, with no finite-dimensionality; it supplies the algebra structure only, not biduality, characters, or scalar comparison. It is a verified Mathlib leaf.
lem-sfb-finite-free-tensor-dual vs lem-sfb-finite-coalgebra-dual-base-change: a linear tensor-dual isomorphism for two arbitrary finite free modules; it neither mentions coalgebras nor states any clause of the item, and is a verified Mathlib leaf.
lem-sfb-finite-free-tensor-dual vs lem-trf-finite-free-map-coefficient-support: the latter is a dual-tensor-to-Hom(P,N) isomorphism plus least coefficient support; it does not state the dual of M tensor N. Deriving tensor duality requires another tensor-Hom identification, so no direct statement specialization is available.
lem-sfb-finite-free-tensor-dual vs lem-sf-exact-pairing-tensor: the latter constructs a dual pair in a general monoidal category; it does not identify the ordinary module dual or state the canonical ordinary dual tensor map is bijective.
lem-sfb-finite-free-tensor-dual vs lem-zl-finite-projective-module-dual-pairing: the latter identifies P tensor P-dual with End(P) and gives triangle identities; it does not state duality of a tensor of two different modules.
lem-sfb-finite-free-tensor-dual vs lem-sfb-finite-dimensional-perfect-pairing: the latter assumes two-sided nondegeneracy of a given pairing; our leaf states the specific canonical tensor-dual isomorphism without that hypothesis.

The proposed dual-base-change leaf was not created: lem-trf-projective-exterior-scalar-comparisons already states precisely its map under more general hypotheses. Other sheaf, derived and exterior-power comparisons found by the DAG search have different objects. The two surviving leaf statements introduce their own objects and have no proof sketch or proof dependencies.

## Review by N5

I checked delivery-errors B through E against the actual sources and all cited statements. In Step 1, lem-weil-pbc-vector-space-free gives a basis, and the finite support argument turns it into a finite basis. lem-weil-pbc-vector-space-projective states projectivity, so lem-sf-finite-projective-dual applies with all its finite generation and projectivity hypotheses verified; its statement gives finite duality and exactly evaluation, not just an unspecified isomorphism. The new convolution leaf applies with R=B=k and C=D, and its unit is epsilon. This is a direct Mathlib specialization, not the creation of a new unresolved copy of a clause.

Step 2 is the displayed two-line evaluation of product and unit and scalar multiplication. There is no tacit commutativity of A. Step 3 uses finite-free tensor duality solely for surjectivity onto every linear functional on D tensor D. The cited tensor definition explicitly says pure tensors generate. Thus killing all product functionals kills every functional; lem-weil-pbc-vector-space-dual-separates explicitly applies to an arbitrary vector space and proves that this forces the tensor to be zero. I checked that the tensor dual node's formula and the separation node's statement actually provide those precise facts. The already established evaluation isomorphism gives the unique vector representing a character, rather than assuming a coalgebra theorem about characters.

Step 4 uses the ordinary dual clause of lem-trf-projective-exterior-scalar-comparisons. I opened its entire statement, including the displayed bb'lambda(v) formula. The identity retract on the finite free D verifies its direct-summand hypothesis; its rings are k and F. No flatness assumption is required or silently used. The formulas for Delta_F and epsilon_F and their identities are scalar extension of the given identities, checked on spanning generators using the cited tensor definition. The convolution leaf applies again over F. I declared the trace-formula node as a generic tool in split_report.tool_uses: only the ordinary module statement is used, and the unit has no replacement scalar-dual lemma.

Step 5 explicitly compares the two products on a tensor a tensor f, c tensor g evaluated at b tensor x. Both give acb sum f(u_i)g(v_i). Bilinearity and spanning are exactly the cited tensor definition; the unit and F-scalar compatibility are written separately. The scalar extension and all sums are finite tensor expressions; there is no unjustified exchange of infinite sums. Step 6 checks the zero-dimensional edge: the zero convolution algebra is allowed, both sets of characters/group-like vectors are empty, and the comparison remains the unique linear isomorphism of zero modules. No nontrivial-algebra condition is introduced.

For each new leaf I read the current Mathlib source, checked every hypothesis and checked the precise formula. Convolution needs no cocommutativity, permits C=0, and works for arbitrary associative B. Tensor duality is valid for arbitrary commutative R and finite free M,N, including a zero module or the zero ring. As a noncommutative test, take D to be the dual coalgebra of M_2(k): its dual algebra is M_2(k), both character and group-like sets are empty, and scalar extension yields M_2(F). As a positive test take the diagonal coalgebra on a finite set: convolution is k^n, and the characters and group-like vectors are precisely coordinate evaluations and basis vectors. The n=0 case agrees with Step 6 in every characteristic.

Every proof step has length below 1000 characters; no step triggers the 2000-character hidden-lemma audit. The only non-elementary tools used are the cited statements; the two newly created statements are Mathlib leaves, and the item retains the argument for its character and multiplicativity clauses. All citation quotes are verbatim full statements. No compiler, Lake, Lean-writing, repository-writing, launcher edit, local DAG check, or agent spawning was performed.

## Unfinished work

None in this one-level split. The required remote dry run and delivery are the remaining mechanical actions; their final outcomes are recorded below when obtained.

## Validation

The required deliver.py --no-push exited successfully: OK (not pushed), preflight passed, dry-run commit 9ad761d16d7. The remote checks included check_dag and review_split. This is the author's direct delivery as authorized by the dispatch brief; the maintainer supplies the independent mathematical review.
