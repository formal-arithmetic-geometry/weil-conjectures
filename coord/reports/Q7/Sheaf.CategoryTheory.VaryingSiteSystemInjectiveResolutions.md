## What changed

Replaced the sole proof hole in
`Sheaf.CategoryTheory.VaryingSiteSystemInjectiveResolutions`, without changing its
statement, universes, visibility, or public imports. Added two structural modules:
`Sheaf.CategoryTheory.VaryingSiteSystemAbelian` and
`Sheaf.CategoryTheory.VaryingSiteSystemEvaluationAdjoints`.

The item now constructs products of systems directly, including transition maps,
identity and cocycle proofs, compatible projections and lifts, and the universal
property. It proves preservation of injectives by evaluation from the free
adjunction. It constructs an injective presentation of every system as the
product of the cofree images of injective component embeddings. The proof of
monicity uses only adjunction naturality and cancellation of those embeddings;
it requires no chosen normalization of the right-adjoint Hom bijection.
Finally it applies the existing bounded-below monomorphic injective-resolution
theorem and proves componentwise injectivity and quasi-isomorphisms by exact
evaluation. The item DAG now records precisely this argument.

All new helpers in the item are private and proved. The two new public statements
have complete proof docstrings, individual modules and nodes. No existing module
other than the assigned item, and no other existing node, was changed. No change
record is needed because no existing public interface changed.

## Proved and sorry left

Closed the original hole:
`CategoryTheory.varyingSiteSystem_injective_resolutions`
(node `lem-per-varying-site-system-injective-resolutions`). The item has zero
remaining textual holes. Its product construction and its enough-injectives,
injective-preservation and resolution arguments contain no holes.

Added exactly two holes, each the whole proof of its named public theorem:

- `CategoryTheory.varyingSiteSystem_abelian_componentwise` in
  `Sheaf.CategoryTheory.VaryingSiteSystemAbelian`, node
  `lem-per-varying-site-system-abelian-componentwise`. This isolates the
  componentwise abelian structure, exact additive evaluations, and detection of
  the kernel and cokernel universal properties. It does not assert injectivity
  or anything about complexes.
- `CategoryTheory.varyingSiteSystem_evaluation_adjoints` in
  `Sheaf.CategoryTheory.VaryingSiteSystemEvaluationAdjoints`, node
  `lem-per-varying-site-system-evaluation-adjoints`. This isolates the free/cofree
  evaluation construction and preservation of monomorphisms by the free functor.
  It asserts neither enough injectives nor preservation of injectives nor any
  resolution theorem.

This is a decomposition: one upper hole closed, two strictly structural holes
added, net minus one by hole count. It is not claimed as a complete proof free
of inherited sorry dependencies. Products are constructed from actual component
products, rather than chosen from an unproved existence theorem. The adjoints
are selected only inside a proof and are determined up to natural isomorphism
by their adjunctions; no definition selects arbitrary data from a holed theorem.

## No longer needed

Removed the proof import `Sheaf.CategoryTheory.SitePullbackAbelianExact` and the
direct proof dependency `lem-weil-pbc-site-pullback-abelian-exact`. The diagram
already supplies additive inverse images and their finite-limit preservation;
finite-colimit preservation follows from their actual sheaf adjunctions.
No theorem about the underlying set-valued inverse image is needed again.

The direct proof dependency `lem-per-varying-site-evaluation-adjoints` and its
module `Sheaf.CategoryTheory.VaryingSiteEvaluationAdjoints` are not used by this
proof: they are replaced by the specified-coherence structural step. The proof
therefore also needs no translation to `VaryingSiteAbelianSystems`,
`TotalSiteSheafSystems`, or a site-level coherent pseudofunctor. Those existing
modules and declarations are preserved.

`def-sp-abelian` is no longer a direct proof dependency of the item, but remains
a statement dependency and is used by the componentwise structural node.
`lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact` is used only in the
new free-adjoint node, rather than as a direct step of the item. It remains
needed transitively and is not claimed as pruned. The existing product,
sheafification, enough-injectives, resolution and exact-homology tools remain
used. There is no module withdrawal or claimed global module pruning.

## Where the brief, the DAG or earlier work was wrong

The original evaluation-adjoint dependency is stated in Lean on
`CoherentSitePseudofunctor.AbelianSystem`, with canonical inverse-image mate
comparisons arising from a site-level pseudofunctor. This item is stated on
`VaryingSiteSystem D e`, where D supplies individual site functors and e supplies
coherence directly at the abelian inverse-image level. The given data contain no
site-functor identity/composition comparisons, and the definitions of the two
system categories are different. Thus the existing Lean theorem cannot be
applied directly to D,e. The new adjoint lemma states the actual missing
construction for this representation. Its proof uses the mates of e rather
than assuming that e arose from a separately supplied site pseudofunctor.
The mathematics of the original construction remains valid and is retained.

The product-of-cofree embedding needs no explicit identity-factor formula from
the adjoint dependency: transpose equality after each product projection and
cancel the original component embedding instead. This preserves the original
unit route and all conclusions. Edge cases checked in the proofs and statements:
empty I, empty Hom sets between distinct vertices, all integer lower bounds,
and noninvertible transitions. No filtering or finite-cover hypothesis was added.

## New nodes

`lem-per-varying-site-system-abelian-componentwise` isolates the first structural
step of the existing proof plan. Its node records the componentwise Hom groups,
finite biproducts, kernels, cokernels, coimage-image comparison, exact evaluation,
and both universal-property criteria. Its statement is strictly below the
injective-resolution theorem.

`lem-per-varying-site-system-evaluation-adjoints` isolates the missing free/cofree
construction for the item's specified inverse-image coherence. Its node records
the summand and projection formulas, coherence, natural Hom bijections and the
finite-subsum argument for monomorphisms. Ordinary functor-category evaluation
adjoints and the differently encoded existing site-pseudofunctor theorem were
searched and read before making this node.

No change records: existing interfaces are unchanged.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
