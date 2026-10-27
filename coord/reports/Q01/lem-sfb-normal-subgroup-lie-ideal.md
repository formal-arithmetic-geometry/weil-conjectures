# Stage-1 report: lem-sfb-normal-subgroup-lie-ideal

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-normal-subgroup-lie-ideal.json`: split; unchanged statement; no Mathlib match.
- `citations.json`: a verbatim statement extract for every step/node pair.
- `report.md`: this report. Search outputs and the write script are sandbox research aids.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searching `lean/WeilConjectures/` by the blueprint tag and by normal/Lie terminology found no declaration stating the whole item. The monodromy file has theorems for its particular monodromy groups and refers to `lie_mem_range_lieAlgebraMap`; it does not state the arbitrary-field group-scheme assertion with the commutative clause. The attachment criterion is therefore not met.

## WANTED

None: Milne's 2017 Algebraic Groups and Stacks are present locally.

## Corrections and route

No statement correction was needed. In particular the arbitrary-field, possibly nonreduced statement is true; there is no need to add characteristic zero or smoothness. The item initially had no proof. The split supplies the actual normality argument, rather than replacing its conclusion by a new lemma.

I read the chapter and unit records, the latest blueprint's `sk-thm-sf-ctf-stability` unit and its direct-images proof, and the latest `sk-p-comparison` unit's two-parameter matrix calculation. This remains a supporting algebraic-group input in the inherited alteration/moduli route. I do not use the characteristic-zero invariant-subspace assertion from the comparison unit. `tools/blueprint_refs.py ancestor` returns `None` for this item: the inherited created-item chain ultimately names `Sheaf.SixFunctors.CtfStabilityDirectImages` rather than an existing DAG node. I retained the inherited null ancestor, precise place and via list, rather than inventing an ancestor. Searches `adjoint representation`, `normal subgroup`, `Lie functor`, and `commutator tangent` found no blueprint node stating this item. `same_as` is empty.

The generic closed-immersion criterion from another unit is declared in `split_report.tool_uses`. It supplies precisely the coordinate-ring surjection needed to check factorization through the closed subgroup, not a different mathematical route.

## Mathlib searches

The five actual Q01 msearch invocations and their results are saved as `search-result-0.txt` through `search-result-4.txt` and recorded in `searches.jsonl`; the item appends those exact tool/query pairs and output. Two LeanFinder phrasings, LeanSearch, Loogle, and source grep were run. None was unavailable. I read the source of Mathlib's abstract ideal definition and normalizer result: `LieIdeal`, `LieHom.IsIdealMorphism` and `LieSubalgebra.exists_nested_lieIdeal_ofLe_normalizer` require a Lie algebra or the bracket-stability input already. They do not derive that stability from normality of a subgroup scheme. The other semantic hits about manifold group Lie algebras require a nontrivially normed field and charts. They are not one-line specializations to arbitrary field group schemes. The original Q77 search records are retained as history, not presented as Q01 searches.

## Not duplicates

No new nodes were created. The whole-DAG statement search found the existing `lem-sfb-affine-group-lie-tangent-calculus`, `lem-sfb-affine-group-dual-number-calculus`, and `lem-sfb-affine-group-faithful-linear-representation`, which are reused. `lem-wf-mixed-commutator-tangent` concerns two vectors in a single matrix subgroup; it does not state that a commutator with one vector from a normal subgroup belongs to that subgroup. I write that short argument explicitly instead of creating a duplicate or a clause of this item.

## Review by Q01

I read Milne, Algebraic Groups (2017), printed pp.188--194: 10.6 identifies the tangent kernel and augmentation cotangent dual, 10.11 gives its additive operations, 10.14 gives subgroup tangent injection, 10.19 gives algebra-valued infinitesimal points, and 10.22--10.23 construct the functorial bracket and compute it for matrices. I also read Lemma 23.68 on printed p.506, where the normal commutative subgroup has an abelian Lie ideal. The supplied proof is marked agent-written because it expands that assertion using the two independent parameters, rather than claiming the omitted normality proof is written out in the book. Stacks Tag 01QO was checked against `tags/tags` and `morphisms.tex`, label `lemma-closed-immersion`: its first two equivalent conditions give the exact affine surjection used. No SGA source is used.

For step 1 I opened the statements of the tangent calculus and dual-number calculus nodes. The former gives finite dimensionality, linearity and bracket preservation without smoothness, and the latter explicitly gives tangent injection for a closed subgroup and naturality on all algebra-valued dual numbers. These are exactly the claims taken from them, not properties hidden in their proofs.

For step 2 I opened the faithful-linear-representation node: its statement gives a closed embedding into GL_m for every affine finite-type group over any field and injectivity on every algebra's points. The dual-number node therefore gives injectivity of its differential. The tangent calculus statement gives both the matrix formula for tangent points and preservation of the matrix commutator bracket. I checked the four-factor multiplication with epsilon squared and delta squared zero, including the order of the factors and the sign: it is 1 + epsilon delta (XY - YX). No division by 2 or use of the printed one-parameter cubic expansion is involved.

For step 3 I opened the normal-subgroup definition, the closed-immersion criterion, the affine-spectrum definition, the dual-number calculus statement and the Lie-ideal definition. Normality is for every commutative k-algebra, so it applies to the nonreduced algebra A. The criterion gives N = Spec(C/J), while affine-spectrum functoriality identifies a point with its algebra map. I did not infer factorization merely from the point's image: I proved the ring map C -> D kills J, using the explicit injective map D -> A and its basis. The quotient map then constructs the N(D)-point. Its reduction is the identity because i_k is injective. The dual-number node's naturality gives its tangent preimage w. Finally the definition of a Lie ideal is exactly closure under these brackets. This is marked elementary with the required cited statements because the additional work is quotient factorization and comparison of basis coefficients, all written out, not a hidden descent theorem.

For step 4 I checked commutativity as a group-scheme property on A-points. Applying the same multiplication to two tangent vectors of N makes the epsilon delta coefficient zero. Bracket preservation and the two injective differentials then give zero bracket on N itself and on its image. The two cited calculus statements provide exactly those properties. Neither the image being an ideal nor its being abelian is assumed as a new node.

Edge cases checked: the trivial subgroup and G=N; finite etale groups with zero tangent space; alpha_p in Ga and mu_p in Gm in characteristic p, including p=2; a commutative but noncentral normal subgroup such as Ga in the affine linear group. The conclusion is [I,I]=0, not [g,I]=0, so the last example is consistent. The basis injection and matrix inverses remain valid in characteristic 2. Both G and N are assumed affine and finite type, exactly as required by every non-elementary same-unit input. Every step is below 2000 characters. No new statement, definition data, proof node, Lean file, compiler or local DAG checker was introduced.

Against delivery-errors B--E: there are no new-node form/source/search issues; every non-elementary input is a named existing node; every quote in citations.json was checked as a literal part of its live statement; I used statements rather than their proofs; the normality and factorization work stays in the item's proof; no new dependency on a restricted-characteristic theorem, reduced-point argument, or smoothness assumption is present. Nothing mathematical remains unfinished.
