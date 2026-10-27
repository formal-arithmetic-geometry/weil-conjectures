## What changed

Reduced `CategoryTheory.PrincipalQuotientCompletion.Model.complete_heart_kernels`
without changing its statement or its completeness definition. The proof now uses
invertibility of the explicit differential `1 - scalar shift` on a countable power.

Added `Sheaf.Paper.ExactEndomorphismIsoClosure`, proving the joint kernel,
cokernel, image and extension closure for the invertibility locus of a natural
endomorphism of any exact additive functor. Kernel/cokernel preservation and
naturality give the induced isomorphisms; the abelian coimage-image comparison
gives images, and the short five lemma gives extensions.

Added `Sheaf.Paper.CountableScalarDifference`, constructing the actual countable
power, scalar shift and difference, and proving their closure result from the
product-of-epimorphisms hypothesis. Added
`Sheaf.Paper.PrincipalCompleteProductCriterion`, isolating the remaining
unit-normalized comparison with the two-term scalar Roos differential. This
criterion is a computation for one arbitrary module; it asserts no closure
property. The original theorem combines it with the proved categorical argument.

The source read was Bhatt--Scholze, Proposition 3.1.11, Definition 3.4.1 and
Lemmas 3.4.12 and 3.4.14, printed pp.17,20--23. The unit route is unchanged;
this item is below its realization nodes. The categorical proof spells out the
source's two-term amplitude argument as an exact-product diagram argument.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.PrincipalQuotientCompletion.Model.complete_heart_kernels` by
reduction. Added one hole:
`CategoryTheory.PrincipalQuotientCompletion.Model.complete_product_criterion`
(node `lem-sfb-principal-complete-product-criterion`). This is a decomposition,
with zero net holes closed: one original hole closed and one strictly different
computational hole added.

The new theorems `CategoryTheory.exactEndomorphism_iso_closure` and
`CategoryTheory.CountableScalarDifference.iso_closure` have complete proofs and
add no holes. No definition contains a hole. The item's own module has zero
remaining holes; the delivery has one remaining hole in the criterion module.

The criterion's proof docstring includes transport between the fibre theorem's
canonical model and the arbitrary canonical presentation in the statement,
using the universal counits and normalized augmentation. Small cases checked
mathematically: zero module and zero ring; a unit parameter (the difference has
a nontrivial constant-section kernel on a nonzero module, and completion is
zero); a parameter acting nilpotently on the module (a finite geometric-series
inverse); and the ordinary p-adically complete module over the integers. None
requires regularity on the module itself or closure under arbitrary subobjects.

## No longer needed

Removed the direct proof imports
`Sheaf.Algebra.Homology.RoosConeCalculus` and
`Mathlib.Algebra.Homology.HomotopyCategory.ShortExact` from the item module.
Removed the obsolete direct `lem-pe-roos-cone-calculus` tool approval from this
item node; its approval below the fibre theorem is untouched.
The direct cone/truncation argument of
`lem-pc-cone-short-exact-quasi-iso` is unnecessary for this proof. Its module is
not newly imported by any added module. The direct cone/shift application of
`lem-pe-roos-cone-calculus` is unnecessary in the closure argument; it remains
needed below `lem-sfb-regular-principal-completion-fiber`, so it is not claimed
as globally pruned. Likewise the derived homology and localization nodes remain
needed below the new criterion rather than directly in the closure argument.

The item still needs `lem-weil-proetale-countable-products-exact` and the new
criterion; the criterion still needs the regular principal fibre comparison.
No existing module or declaration is withdrawn. Public imports and all existing
signatures are preserved. No source-library files are changed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The DAG's planned amplitude argument is valid,
but its categorical closure part can be shortened: on modules the scalar Roos
object is a two-term complex for an endomorphism of the exact countable power
functor. Invertibility of that endomorphism is stable under the stated operations
by elementary kernel/cokernel comparisons and the short five lemma. The fibre
interface provides an existential canonical completion model, so its unit must
be transported to the supplied model; the new criterion explicitly includes
that obligation rather than assuming the models are definitionally equal.

## New nodes

`lem-sfb-exact-endomorphism-iso-closure` records the proved generic diagram
argument, including images via cokernels of kernel inclusions and extensions
via the existing Mathlib short-five-lemma node.

`lem-sfb-countable-scalar-difference-closure` records the actual countable power
and scalar differential and their proved closure theorem. It applies the first
node after deriving exactness from preservation of epimorphisms and kernels.

`lem-sfb-principal-complete-product-criterion` is the single remaining hole. Its
source, full proof in words, canonical model comparison, two-term computation,
and edge cases are specified in its module and DAG node. It is strictly a step
of the argument and does not assert any of the item's closure conclusions.

No change record is needed: no existing statement or definition was changed.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
