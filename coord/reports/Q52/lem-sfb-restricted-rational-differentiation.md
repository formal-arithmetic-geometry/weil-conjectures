# Q52 stage-1 delivery: lem-sfb-restricted-rational-differentiation

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-restricted-rational-differentiation.json`: statement item, split into seven explicit steps; statement unchanged; Mathlib searches do not match the whole theorem.
- `dag/nodes/sec-six-functors-basics/lem-sfb-associative-jacobson-identities.json`: one new statement-only node, unsplit; the general associative-algebra Jacobson formulas, absent from the checked Mathlib API.
- `citations.json`: one verbatim statement quotation for each of the ten step/node citations.
- `report.md`: this report. Search evidence is retained in `searches.jsonl`. `milne.txt` and `write_split.py` are sandbox working files, not delivery files.

New nodes: 1. New Mathlib leaves: 0. The already existing Mathlib leaf `lem-sfb-convolution-linear-map-algebra` is reused.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint id and by invariant derivations, restricted Lie algebras, coactions, p-Lie and Jacobson formulas. The invariant-field extension declarations in `AlgebraicGeometry/GroupScheme/Cartier.lean` give tangent extensions, not this restricted structure, functoriality, and arbitrary-comodule theorem. The mixed-commutator definitions in `AlgebraicGeometry/GroupScheme/Lie/Bracket.lean` do not cover its p-operation or coaction clauses. Thus there is no full attachment claim.

## WANTED

None. The needed source is present as `literature/milne-algebraic-groups_iAG2017.pdf`.

## Corrections and scope

The imported statement is correct and is retained word for word. No STATEMENT-DISPUTED correction is needed. It had no proof. The new proof supplies the actual algebraic calculations rather than taking finite-dimensional differentiation as a black box and silently extending it to all modules. It does not assume smoothness, reducedness, perfection of the field, cocommutativity of the coordinate coalgebra, or finite dimension of W.

The existing statement dependency `lem-sfb-restricted-pbw-basis` supplies the specified convention for the restricted identities and s_i; its PBW theorem is not used as a proof premise. That node's statement was read: s_i uses the coefficient of t^(i-1) in ad(tx+y)^(p-1)(x), with 1 <= i < p. The new Jacobson statement uses precisely this convention. Expanding the preceding word definition in Milne §10k verifies agreement, including the examples for p=2 and p=3. Milne's printed Definition 10.39 has an endpoint typo in the displayed summation; the item already uses the correct 1 through p-1 convention from Proposition 10.38. No statement is changed on that account.

The current blueprint was read at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`, including its unit statement and direct-images proof (3). This item is a generic representation-theoretic input below the existing alteration/GIT/Haboush route; it does not replace a unit step. The inherited nearest blueprint ancestor is null (`blueprint_refs.py ancestor` prints None); that field is preserved, and the new node prepends the item to the exact inherited via list. No unit or chapter file is edited.

## Unfinished work

The single new node intentionally remains statement-only for a future stage-1 split, as required by the one-level rule. There is no unfinished argument in the item's seven-step assembly proof. No Lean was written, compiled, or built.

## Not duplicates

lem-sfb-associative-jacobson-identities vs lem-sfb-restricted-rational-differentiation: the new node is about arbitrary associative algebras, with no group scheme, tangent space, invariant derivations, differential or coaction; it supplies the noncommutative power identities used in two steps, while the item proves every group/coaction assertion.

lem-sfb-associative-jacobson-identities vs lem-sfb-restricted-pbw-basis: PBW assumes a restricted Lie algebra and proves a basis and generator presentation for its quotient; it does not prove the associative Jacobson formulas used to construct a restricted operation.

lem-sfb-associative-jacobson-identities vs lem-sfb-convolution-linear-map-algebra: convolution constructs an associative algebra of linear maps; it has no prime-characteristic power identities or s_i polynomials.

lem-sfb-associative-jacobson-identities vs lem-sfb-unipotent-restricted-enveloping-augmentation: the latter assumes a semisimple group, Borel and unipotent radical and concludes augmentation properties; it does not state the general associative identities.

The searches of all DAG statements and the whole imported blueprint for Jacobson formulas, invariant derivations, restricted Lie and p-Lie found no duplicate. There is no Stacks tag for this Milne algebra result; source locations are Proposition 10.38(a),(b), pp.205–206, rather than an invented Stacks citation.

## Mathlib evidence

All recorded new searches were run through the required msearch.py command and their original results are in searches.jsonl. Two natural-language phrasings for the new node found the ordinary commutator Lie algebra, scalar restriction, and commuting-power/Frobenius formulas. Loogle `LieAlgebra.ad, "pow"` found `ad_pow_lie`, the binomial Leibniz formula for iterated brackets, not the Jacobson sum formula. Grep over Algebra/Lie and then the whole Mathlib source found no restricted operation or Jacobson sum polynomial API. Read `Mathlib/Algebra/Lie/OfAssociative.lean` (including lines 50–106 and 304–324) and `Mathlib/Algebra/CharP/Lemmas.lean` (the Commute formulas and their prime-characteristic specializations): the Lie structure and commuting sums are genuinely partial matches and do not give the new node in one specialization.

For the item, semantic searches in two formulations found manifold left-invariant derivations, finite-group Tannaka constructions and Hopf antipode identities; Loogle `Bialgebra, Derivation` returned no hits. Read the manifold derivation hypotheses: they concern smooth normed manifolds, not an affine coordinate algebra in arbitrary positive characteristic. Searches for iterated Leibniz rules found calculus, polynomial and LieDerivation formulas, not the item. These results are logged as searches, not misrepresented as attachments or leaves. All services used here responded; no failed service is recorded as a negative mathematical result. Prior imported search records are retained.

The reused convolution leaf's source was checked at `Mathlib/RingTheory/Coalgebra/Convolution.lean`: convMul_apply (63), convOne_apply (179), convAlgebra (187), convAlgebraMap_apply (192), convRing (212). These have exactly the multiplication and unit asserted in the cited node; WithConv only changes the algebra structure carried by the linear-map type.

## Review by Q52

I read Milne §10d, equations (59)–(63) and Theorem 10.23 (pp.192–194), §10k Proposition 10.38 and its proof, Definition 10.39 and the quotient universal property (pp.204–207), §10l (pp.207–208), §11e Theorem 11.25/Proposition 11.26 (pp.217–218), and the restricted-operation paragraph immediately preceding Proposition 11.36 (p.223). The latter mentions invariant derivations but omits calculations; I wrote those calculations and marked the proof origin as agent. The sole new node states Proposition 10.38, with its coefficient convention obtained by expanding the word definition. No SGA source is used.

For step 1 I opened `def-sc-group-scheme` and checked that its associativity and unit diagrams give precisely the coassociativity and two counit equalities used. I expanded D_x(ab), computed epsilon D_x=x, and applied the invariant equation followed by id tensor epsilon to obtain the inverse D -> epsilon D. I do not take a derivation theorem from the definition node: the step proves the derivation assertion from the product rule.

For step 2 I opened the full statement of `lem-sfb-convolution-linear-map-algebra`. It allows C without cocommutativity or finite dimension and B=F, and explicitly supplies convolution and unit epsilon. The triple tensor formula computes the order R_phi R_psi=R_(phi*psi); applying epsilon proves injectivity, so no unquoted faithful-action lemma is used.

For step 3 the new Jacobson node states the exact ad(D)^p=ad(D^p) identity needed in End_F(C). With M_a multiplication by a, the successive commutators are M_(D^n(a)); evaluating the pth identity at b proves the full Leibniz rule for D^p. I separately expanded the commutator Leibniz rule and the invariance equation for a composition. This avoids hiding a general iterated-Leibniz theorem or incorrectly treating D(a^p) as D^p(a).

For step 4 I opened `def-wf-lie-algebra`: its statement explicitly says End(V) with the commutator, and every bracket-closed subspace, is a Lie algebra. The new Jacobson node supplies the two nontrivial restricted identities for the endomorphism algebra; scalar semilinearity is an elementary composition calculation. The inverse in step 1 and faithful regular-coaction map in step 2 reflect these identities, including each coefficient of s_i. Neither theorem is taken from the proof of its cited node.

For step 5 I again checked the convolution leaf with B=F[t,s]/(t^2,s^2); it permits this commutative F-algebra. The group definition supplies B-points with their group multiplication. The maps epsilon+tx and epsilon+sy are algebra maps by the tangent product rule. Four-factor multiplication gives the displayed ts coefficient; this fixes the left/right and commutator sign without assuming smoothness or faithful embedding in GL_n.

For step 6 the group definition gives compatibility of a homomorphism with multiplication, and its group-valued points imply compatibility with identity. I pulled back these diagrams and wrote the convolution-preservation equation. The convolution leaf identifies the operations to be preserved, and step 4 identifies tangent powers with convolution powers. The inverse group automorphism gives an inverse differential, so no unproved bijectivity assertion is hidden.

For step 7 the convolution leaf again supplies the algebra E, while the actual coaction hypothesis of the item supplies the displayed S_phi S_psi calculation. I checked that composition has the same order as convolution, and that counitality sends epsilon to id_W. The tensor-word construction is multilinear, multiplicative by concatenation, kills exactly both displayed classes of relations, and hence descends to a unital action. It uses no finite-dimensional distributions theorem. Every individual coaction value is in an algebraic tensor product, so it is a finite sum even when W has arbitrary dimension.

I tested the conventions at p=2 and p=3 on the noncommuting matrices E_12,E_21: the coefficient definition of s_i gives exactly (a+b)^p-a^p-b^p, and ad(a)^p=ad(a^p). These finite matrix calculations were executed in Python without Lean. At p=2, s_1=[y,x]=[x,y] and all minus signs have the correct characteristic-two meaning. For Ga and alpha_p, the invariant generator d/dt has zero pth iterate; for Gm and mu_p, t d/dt has pth iterate t d/dt. Thus the proof does not erroneously identify the restricted operation with zero for every group. W=0 and infinite direct sums of rational modules satisfy the same coaction computations. Over an imperfect field the formula for cx is c^p x^[p], with no extraction of pth roots. The zero algebra is also harmless in the new general associative statement.

I checked delivery-errors B–E against the files: the new node is self-contained and statement-only, its notions are inline or have a definition dependency, source places and TeX are explicit, no duplicate or item-clause relabelling is introduced, and each non-elementary fact is a quoted node. Every proof step is below 1000 characters, so no long step conceals another lemma. The item follows the inherited route and adds no hypotheses. I corrected the initially tempting iterated-Leibniz black box by using the multiplication-operator calculation from the already needed Jacobson identity instead. All citations.json quotations are literal substrings of the corresponding node statements.
