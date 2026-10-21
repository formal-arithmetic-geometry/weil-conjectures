# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-constant-module-scalar-mono.json`: statement, split into four steps, not a Mathlib leaf. No new nodes and no new Mathlib leaves.
- `citations.json`: ten verbatim statement quotations, one for every step/cited-node pair.
- `searches.jsonl`: actual search-command records; the six new searches are also recorded verbatim in the item's `mathlib_searches`. The item's inherited Q26 searches are retained.

## Attachments

None. Searched the item id/docstring tag and scalar/mono/flat/constant terminology in `lean/WeilConjectures/`. No declaration there gives the arbitrary small-site assertion. In particular, the relation-criterion theorems in CategoryTheory/Sites/FlatLocalRelations.lean concern locally trivial relations, impose Noetherian coefficients in the converse, and do not state this result. Mathlib's ordinary module declarations are not project attachments.

## WANTED

None. All sources used are available in the read clone.

## Problems and changes

The imported statement is correct and is unchanged. Its proof was empty. The completed argument separates exact abelian sheafification, the explicit tensor-unit computation, exact flat tensor, and the sectionwise-kernel conclusion. It never replaces sheaf flatness with flatness of M(U), nor supposes the site has points. No chapter or unit is changed.

The chapter and unit were read: sec-six-functors-basics and sk-lem-integral-models. The nearest blueprint ancestor is det-lem-integral-models-operations. Its paragraph (2), tensor product and local scalar models, is the place recorded on the item through lem-sfb-flat-scalar-cyclic-resolution. The current main-20261015 proof and current DAG ancestor were compared. The generic regular-scalar calculation refines the prescribed scalar-model route; no step of the unit is replaced.

## Unfinished work

None at stage 1. No Lean was written and no compiler, Lake or build command was run.

## Searches and reuse

The sandbox initially held no item or report and no previous search log. The item was copied from the current shared repository. Whole-DAG title/concept and source-tag searches, including 03EI and 03ER, located the existing definitions, exact sheafification leaf and exact-functor leaf used below. Blueprint searches `sheafification exact`, `flat scalar`, `constant scalar` and `03EI`, plus the ancestor command, found no blueprint node that states the item. The `constant scalar` hit sk-def-sfb-derived-categories defines derived categories; it does not assert regular scalar injectivity.

The actual msearch.py searches used LeanFinder twice (scalar regularity and kernel preservation formulations), LeanSearch, Loogle and source grep twice. All services answered successfully. LeanFinder's first phrasing returns Module.Flat.isSMulRegular_of_isRegular and Module.Flat.isSMulRegular_of_nonZeroDivisors; I read Mathlib/RingTheory/Flat/TorsionFree.lean:51 and :79. These require flatness of an ordinary module and cannot be applied to sections of a flat sheaf without an additional theorem. The second phrasing returns ordinary tensor-kernel comparisons in Flat/Equalizer and a presheaf tensor definition. LeanSearch returns ordinary-module preservation of injective linear maps. Loogle returns presheaf mono/injectivity criteria and presheaf monoidal definitions. The sheaf-module-directory grep finds no scalar regularity theorem, while the second grep locates the ordinary-module candidates just read. Thus this item is not a one-line Mathlib specialization. The existing general sheafification and exact-functor leaves are reused rather than copied as new nodes.

## Not duplicates

No new nodes were created. The existing broader constant finite-free presentation extension node was inspected but is unnecessary: the ring/module tensor unitor is written explicitly in Step 2. No new scalar-regularity clause or monomorphism lemma was introduced under another name.

## Review by Q19

I read Modules on Sites Tag 03EI (`lemma-sheafification-exact`, sites-modules.tex:874), including its reduction to exact abelian sheafification; Tag 03CY (`lemma-sheafification-presheaf-modules`, extended action and universal property); Tag 03EK (`section-tensor-product`, the sheafification of sectionwise tensor); Tag 03ER (`definition-flat`, specifically sheaf clause (3), not presheaf clause (1)); and Tag 03DA (`lemma-abelian`, the module category and sectionwise kernel). I also read homology.tex Tag 010N (`lemma-exact-functor`): exact functors commute with kernels/cokernels, with its proof of monomorphism preservation. These give the assertion for every small site and commutative ring, without a domain or enough-points hypothesis. No new-node source needs review.

Step 1 cites lem-weil-pbc-sheafification-exact, whose statement really gives finite-limit preservation for abelian sheafification and its adjunction. The kernel of the constant additive presheaf map is zero at each object by precisely the item's injectivity hypothesis; finite-limit preservation then gives the zero sheaf kernel. def-weil-pbc-constant-sheaf defines the constant sheaf by this sheafification, and def-sf-site-constant-module-functor explicitly describes both its underlying abelian sheaf and the unique extended scalar action. These statements justify the identification of the sheafified map with multiplication by the constant a; the equality is checked on the sheafification unit and extended uniquely. Commutativity supplies linearity, and underlying cancellation implies cancellation of module morphisms. No new identification theorem is concealed.

Step 2 cites def-pur-sheaf-tensor-product for the sectionwise tensor followed by sheafification and def-weil-sheaf-of-modules-category for semilinear restriction maps. Both cited statements were opened. The forward and inverse maps are written, both composites are computed by the balancing relation, and restriction compatibility follows from preservation of the unit and action. This is an elementary tensor-unit calculation in a few formulas, not a new node. Because the presheaf tensor is already isomorphic to M, passing to its sheafification gives exactly the claimed unitor; the proof makes no assumption about global pure-tensor representations in a general sheaf tensor.

Step 3 cites def-pc-flat-sheaf-modules for exactness of N tensor M on sheaves; it does not infer sectionwise flatness. def-weil-sheaf-of-modules-category supplies the abelian category under the stated smallness hypothesis. I checked that lem-sp-exact-functor-preserves-homology clause (a) explicitly says that exact functors carry monomorphisms to monomorphisms. This is the needed theorem beyond the flatness definition, so the C1 gap of merely invoking tensor exactness by name is avoided. Applying it to the map already proved monic gives a monomorphism on R tensor M. The step then computes its conjugate by the explicit unitor, using def-pur-sheaf-tensor-product, and obtains exactly m maps to am. The generic exact-functor node is a Mathlib leaf, so no off-route tool declaration is needed.

Step 4 cites def-weil-sheaf-of-modules-category for the exact statement that kernels are computed sectionwise. For both endomorphisms, its section kernel is therefore zero. Subtracting sections proves injectivity, and componentwise cancellation proves the converse monomorphism formulation. This is elementary and applies also to objects admitting empty coverings. Every cited node's actual statement was read and every quote in citations.json checked as a literal substring. All uses equal the union in proof_deps.

For small cases I checked M=0, the empty site (all section claims vacuous), objects on which an empty covering forces zero sections, a unit a over a ring with zero divisors (e.g. 5 in Z/6), and a regular nonunit over a non-domain (e.g. (2,3) in Z times Z). The proof uses injectivity, not a domain cancellation rule. If a=0, its injectivity forces A to be the zero ring; unital modules over its constant sheaf are zero, so the conclusion still holds. No cases require nonempty objects or a point. No statement dispute was found.

Against delivery-errors B-E: no new node can conceal a duplicate, proof sketch, unintroduced object or restatement of the item. Existing notions are cited; the complete argument stays in the item's four steps. Tags and labels were checked in stacks-project/tags/tags. The two non-elementary applications have actual theorem nodes, and the two elementary steps display their calculations. Each step is under 2000 characters. The statement, all hypotheses and the two conclusion clauses are preserved, no proof of a cited node is mined for extra conclusions, and no cyclic dependence is introduced. The main correction to the empty imported proof was to supply these precise identifications and cite the exact-functor theorem rather than treating flatness of sections as available.
