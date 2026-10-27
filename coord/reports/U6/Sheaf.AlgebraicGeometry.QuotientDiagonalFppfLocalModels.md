## What changed

Proved `AlgebraicGeometry.Scheme.quotient_diagonal_fppf_local_models` in
`Sheaf.AlgebraicGeometry.QuotientDiagonalFppfLocalModels` without changing its signature,
`quotientDiagonalFibre`, or any public import. All six private helpers are fully proved.

The equality presheaf is a sheaf by separatedness of the restricted quotient sheaf, including
empty covering sieves. The sheafification universal property implies local surjectivity by
factoring through the locally generated image subsheaf. Pointwise surjectivity of the
presheaf coequalizer projection then gives local lifts into U. Intersecting the two image
sieves and extracting a precoverage cover gives simultaneous lifts on the same fppf cover.

The existing kernel-pair theorem gives relation witnesses. The pullback universal property
identifies these with points of exactly the prescribed local model. Both sets are
subterminal, giving the natural isomorphism and its inverse by uniqueness. Choices of
relation witnesses are therefore determined uniquely; no arbitrary unproved existence
statement supplies data to a definition. Separatedness and local quasi-finiteness follow
from Mathlib base-change instances and the proved quasi-finiteness comparison theorem.

Added private imports of `Mathlib.CategoryTheory.Sites.LocallySurjective`,
`Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono`, and
`WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphismComparison`.
Updated the item's DAG proof and proof dependencies to describe this argument.
The complete module compiled cleanly through lcompile.py in 12.1 seconds (exit 0).
Source checks verify unchanged public signatures, definition body and public imports,
zero textual holes, and the 100-character line bound.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.quotient_diagonal_fppf_local_models`
(node `lem-trf-quotient-diagonal-fppf-local-models`).
Added 0 holes; split off 0 statements; no sorry remains in any delivered Lean file.
The proof uses the existing `AlgebraicGeometry.Scheme.etale_relation_kernel_pair`,
whose current source theorem is still sorry. That is an existing stated dependency,
unchanged by this delivery.

## No longer needed

Removed the proof import
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal` and the corresponding
proof dependency and tool-use entry `lem-weil-pbc-site-sheafification-sections-local`.
The stated theorem requires the value universe to contain the object universe of the
site, whereas this item uses Type u values on Over Scheme.{u}, whose objects lie in
Type (u+1). A fully proved image-subsheaf argument works directly with hη in the
specified universe and avoids any assumption of global small-valued sheafification.

Removed the proof import `WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange`
and corresponding proof dependency and tool-use entry
`lem-weil-pbc-separated-lqf-base-change`. Its interface treats pullback.snd; the existing
proved `Scheme.Hom.isLocallyQuasiFinite_iff` comparison and Mathlib base-change
instances apply directly to this item's pullback.fst, with no symmetry transport.
These modules and nodes remain available to other consumers; no module is withdrawn.
The kernel-pair and fibre-product dependencies remain used. Existing public imports are
preserved, so the imported interface of this module does not change.

## Where the brief, the DAG or earlier work was wrong

The original step 2 cannot directly instantiate the recorded sheafification-sections
lemma because of its value-universe restriction. The direct universal-property argument
above proves the required local lifting fact in the item's original universes.
Intersection of covering image sieves replaces successive covers and their composition.
The original last step uses a second-projection base-change interface; the comparison
API avoids the extra pullback symmetry. These are changes below the unit level; the
quotient-diagonal local-model step and the parent's descent route are preserved.
No statement is disputed, no target or definition was changed, and no new nodes were needed.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
