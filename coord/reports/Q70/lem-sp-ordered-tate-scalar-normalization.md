# Q70: lem-sp-ordered-tate-scalar-normalization

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-ordered-tate-scalar-normalization.json`: statement, split; seven proof steps; no Mathlib match. The imported statement, statement dependencies, creation record and blueprint origin are retained.
- `citations.json`: 17 step/node entries, each quoting the cited statement verbatim.

New nodes: 0. New Mathlib leaves: 0. The script and search log in the sandbox are working records, not additional DAG nodes.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and the ordered Tate/scalar and coefficient notions, then inspected the affine-space and finite-Kummer candidates. No project declaration states the full equality of the specified normal-form maps and the pasted scalar comparisons. Existing finite-Kummer coefficient isomorphisms alone do not prove the tower equation.

## WANTED

None. The current blueprint and the relevant Stacks source files are present locally.

## Corrections and scope

The item was unsplit, with no proof and no proof dependencies. Its statement is retained; no statement dispute was found. The current source is the Charts paragraph in `main-20261015/.../sk-lem-sp-reduction-exceptional.proof.md`, read together with the unit's second proof step and the affine-space trace proof. That paragraph asserts coefficient compatibility of the canonical chart comparison but does not supply the ordered right-normalization calculation. The proof here supplies it and is explicitly agent-written.

The argument takes place on small ordinary etale sites with arbitrary finite coefficient maps. In particular it does not use the similarly named pro-etale scalar/pullback-composition nodes, completed integral twists, a field coefficient hypothesis, or flatness of B over A. Generic ringed-topos results apply to the ordinary etale sites directly. No SGA route is used.

## Searches and reuse

I searched the whole DAG by ordered Tate normal form, scalar/tensor coherence, coefficient/pullback composition and shifts, and ran `tools/blueprint_refs.py ancestor` plus blueprint searches for `Tate scalar`, `tensor pullback`, `shift scalar`, `normalization` and `Tate`. The ancestor is `det-sp-reduction-exceptional`, through `lem-sp-affine-counit-scalar`, as already recorded. No imported blueprint node states the item's exact named-map equation in another form, so `same_as` stays empty.

The scalar-composition nodes restricted to pro-etale sites and the completed-line coherence nodes were deliberately not used as ordinary-etale facts. The existing general `lem-sfb-ringed-derived-monoidal-comparisons` and `lem-pur-cochain-pullback-tensor-coherence` give the required tensor and composition equations. The existing signed-shift nodes supply the precise shift normalizations. The bilinear universal-property node supplies equality detection for sheaf tensors. Thus none of these arguments requires a new node.

The required msearch commands ran for this item: LeanFinder in two phrasings, Loogle for associator naturality, grep for Tate twist declarations in Mathlib/AlgebraicGeometry, and LeanSearch for derived coefficient/pullback/tensor composition. I read the returned hits and the sources of `SheafOfModules.pullbackComp` at Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:167 and `CategoryTheory.MonoidalCategory.associator_naturality` at Mathlib/CategoryTheory/Monoidal/Category.lean:181. They give ordinary pullback composition and categorical associator naturality, respectively; neither states the derived etale Tate coefficient/tower equation or specializes to it in one line. The second LeanFinder query returns scheme carrier tensor congruences, cyclotomic-character facts, and algebraic base-change maps, also not the item. The actual command queries and returned log summaries were appended to the preserved imported search records.

## Not duplicates

No new nodes are proposed, so there are no new/existing node pairs to justify. All general facts used by the proof reuse existing nodes.

## Review by Q70

I read the current unit `sk-lem-sp-reduction`, chapter `sec-smooth-purity`, Charts paragraph of `det-sp-reduction-exceptional`, and the current `lem-amb-affine-space-top-trace.proof.md`. The chart route remains iterated projective-line integration. This item isolates the right-functor normalization within that route; it does not replace the projective-line counit or purity argument.

For Step 1 I opened the statements of the K-flat resolution node (06YS), ringed pullback preservation node (0G7E), finite Tate-line node, total-tensor K-flat node, derived change-of-rings node, and derived tensor/pullback node (07A4). The first supplies a flat-term K-flat representative. Preservation explicitly has no flatness hypothesis on the ring map, and applies to both the identity-topos coefficient morphism and geometric inverse image. The Tate node gives exact tensor by each degree-zero line, so such a line is K-flat by the definition, not by a lisse/global-triviality assumption. The total-tensor statement permits further tensoring on these same representatives; the change-of-rings statement gives canonical computation and resolution independence. I read `sites-cohomology.tex` at lemma-K-flat-resolution, lemma-pullback-K-flat, lemma-derived-pullback-composition and lemma-pullback-tensor-product (06YS, 0G7E, 0D6D, 07A4). No finite projective dimension or finite-length resolution of B is used.

For Step 2 I read the bilinear-universal-property statement and the finite etale twist pullback statement. The first actually gives the bijection between tensor maps and bilinear maps; the second gives canonical root pullbacks compatible with tensor products, identities and composition. I checked the inverse formulas on a balanced elementary tensor: the coefficient moves from `(t tensor a) tensor b` to `t tensor phi(a)b` and back, with the balancing relation identifying the result with the original. Repeating this operation gives the product of coefficient scalars without changing the ordered root list. This is an elementary calculation, not a new coefficient-line theorem. The sheaf argument uses the bilinear universal property in `sites-modules.tex`, Section 03EK, rather than treating arbitrary sheaf sections as globally pure tensors.

For Step 3 I read the entire statement of `lem-sfb-ringed-derived-monoidal-comparisons`, including its K-flat representative clause, monoidal compositor equation and compatible geometric 2-isomorphism clause, and the whole cochain coefficient/composition statement. Both are for small ringed topoi, so ordinary etale topoi satisfy their domain requirements. I checked that the constant coefficient square commutes with phi, and that the two paths for q followed by j have the same structural ring map. The cochain node asserts equalities of chain maps, not merely existence of isomorphisms. This justifies identifying the actual pasted h/a comparison with the canonical line comparison. I also read the ordinary module composition statement at Stacks 03D8 and tensor pullback at 03EL, rather than relying on a generic definition for a coherence theorem.

For Step 4 I opened both shift statements. The total-tensor node gives unsigned extraction in the first argument, the sign (-1)^(np) in the second, and the addition/interchange laws. The prescribed cochain pullback tensor comparison node gives both actual shift squares. I read the sign-rule item at Stacks 0FNH in `more-algebra.tex`: the tensor shift has sign (-1)^(pb), and reassociation has no sign. For our even shifts all these factors are 1 for every degree p, including odd degrees of the input; the two extracted shifts have interchange sign (-1)^(4r)=1. This checks the accumulated [2d], rather than silently dropping signs.

For Step 5 I checked the definition of I in the item and the finite twist pullback statement. J is simply the last normalization in that definition: combine j*q*, move pullback through old twist/shift, combine u*p*, append the new Tate factor on the right, then add shifts. The generic monoidal comparison statement is used for these same specified canonical maps, not for an arbitrary normal-form existence isomorphism. I intentionally do not infer a chosen normalization from the mere Nonempty assertion in the separate affine-trace normal-form node.

For Step 6 I checked the successor square by the explicit tensor formula, using exactly the cochain coefficient/composition equations and monoidal compositors cited in its uses. Both sides have source T(W_r G_r K) and target G_(r+1)(T K). They pull back the same input component, keep the same ordered root sections, and put b times the product of phi(a_i) in the same resulting tensor. The sheaf-tensor universal property detects equality before localization. Step 1 ensures these actual chain computations represent the derived morphisms in question. This is one routine tensor calculation from the cited general statements; it introduces no independent comparison lemma with separate hypotheses. Every step is below 2000 characters.

For Step 7 I checked the inductive claim, base and successor with all map directions. Naturality of a^u is applied to I_r from the iterated right functor to the direct right functor. This moves T(W(I_r)) to the right of a^u, after which the square of Step 6 applies. Functoriality gives T(J)T(W(I_r))=T(I_(r+1)). No inductive assumption is used in constructing J or proving the successor square. This last step uses only the preceding established steps and functor/naturality identities, so its dependency list is empty and it is elementary.

I checked the hypotheses and small cases: at d=0 all three maps are the specified identity maps, at d=1 the formula reduces to the q/j pasting and the single-line coefficient formula, and at d=2 it keeps t1 before t2 and extracts shifts 2 and 2 with sign 1. The formulas also make sense for an empty base, zero rings (in particular N=1), and the identity coefficient map. A nonflat test A=Z/ell^2 to B=Z/ell shows why the proof must use K-flat P rather than assume ordinary tensor is exact in arbitrary complexes; the proof does so. Since ell differs from p, N is invertible on every coordinate stage. No algebraic closedness of k or global trivialization of mu_N was used. The ordinary unbounded derived calculation specializes to the ctf inputs of the item.

I checked delivery-errors B--E: no unstated new nodes, no hollow definitions, no restated-clause nodes, no unstated non-elementary tensor/shift fact, no use of a cited proof in place of its statement, no pro-etale/etale category substitution, and no change to the item statement. Generic off-unit tools are declared under split_report.tool_uses, not as maintainer-approved top-level tool_uses. The citations quote the actual node statements. Nothing was sent to a second reader because this brief requires direct delivery; this is my own signed self-review, with maintainer independent review still to follow.

## Unfinished work

None in this stage-1 split. No Lean file was written and no compiler, Lake or build tool was run.
