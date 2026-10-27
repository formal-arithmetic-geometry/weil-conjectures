## What changed

Proved Profinite.CondensedAction.InternalBar.exists_resolution by combining the existing
pointed deletion contraction with two strictly smaller new construction statements:
equivariant transport of its underlying complex, and the induced-coordinate presentation.
The proof transfers exactness and epimorphic augmentation through ShortComplex isomorphisms
and GroupAlgebra.exact_iff, both before and after arbitrary tensoring, and explicitly
assembles every field of the unchanged Resolution structure.

Extracted free, freeAdjunction, tuples, freePower, generator, onSections, basis, pureTensor
and regularOne verbatim into CondensedInternalBarData, publicly reexported by the original
module. The declared dependency modules imported the original module for these definitions,
so importing those dependencies without this extraction created a cycle. Redirected only
that import in CondensedFreeLinearizationTensor, CondensedGroupAlgebraExactForgetful and
PointedFreeDeletionContraction. Their statements, definitions and proofs are unchanged.
Updated the two definition-node attachments to the defining module. Change record:
coord/changes/H7-internal-bar-shared-data.md (full downstream user table).

All seven packet modules compile individually through lcompile.py in import order. The
consumer check uses the unchanged CondensedProductActionInflation and InternalBarCharacterLifts
sources against the modified dependencies. No target statement or definition body changes.

## Proved and sorry left

Closed the item's one original hole:
Profinite.CondensedAction.InternalBar.exists_resolution
(lem-sfb-condensed-internal-bar-resolution). This is a decomposition, not a net hole reduction.
Two holes added, in separate new modules, each strictly a part of the argument:

- Profinite.CondensedAction.InternalBar.exists_deletionComparison
  (lem-sfb-condensed-equivariant-deletion-comparison): action, tensor maps, and comparison
  with the underlying deletion complex; it does not assert exactness or induced coordinates.
- Profinite.CondensedAction.InternalBar.exists_inducedCoordinates
  (lem-sfb-condensed-induced-coordinates): induced presentation of any diagonal free family;
  it does not mention differentials, augmentation, or exactness.

Item holes: 1 closed of 1, 0 left. New holes: 2. The local packet adds no hole in any
existing dependency module. The pointed contraction was already proved in the current
source by earlier work; this packet does not claim that proof as newly closed.

Existing unchanged holes retained in the three adapted dependency modules:

- Profinite.CondensedFreeLinearization.exists_comparison (lem-sfb-condensed-free-linearization-tensor).
- Profinite.CondensedAction.GroupAlgebra.action_extension (lem-sfb-condensed-group-algebra-exact-forgetful).
- Profinite.CondensedAction.GroupAlgebra.bilinear_extension (lem-sfb-condensed-group-algebra-exact-forgetful).
- Profinite.CondensedAction.GroupAlgebra.exists_algebraEquivalence (lem-sfb-condensed-group-algebra-exact-forgetful).
- Profinite.CondensedAction.GroupAlgebra.forget_additive (lem-sfb-condensed-group-algebra-exact-forgetful).
- Profinite.CondensedAction.GroupAlgebra.exists_abelian (lem-sfb-condensed-group-algebra-exact-forgetful).
- Profinite.CondensedAction.GroupAlgebra.creates_kernels_cokernels (lem-sfb-condensed-group-algebra-exact-forgetful).
- Profinite.CondensedAction.GroupAlgebra.creates_images (lem-sfb-condensed-group-algebra-exact-forgetful).
- Profinite.CondensedAction.GroupAlgebra.induced_action_unique (lem-sfb-condensed-group-algebra-exact-forgetful).
- Profinite.CondensedAction.GroupAlgebra.exact_iff (lem-sfb-condensed-group-algebra-exact-forgetful).
- Profinite.CondensedAction.GroupAlgebra.linearization_exists (lem-sfb-condensed-group-algebra-exact-forgetful).
- Profinite.CondensedAction.GroupAlgebra.equivariant_iff_on_generators (lem-sfb-condensed-group-algebra-exact-forgetful).
- Profinite.CondensedAction.GroupAlgebra.linearization_map (lem-sfb-condensed-group-algebra-exact-forgetful).
- Profinite.CondensedAction.GroupAlgebra.exists_tensorActions (lem-sfb-condensed-group-algebra-exact-forgetful).

## Forced adaptations

Added by the reviewer. The three adapted modules are unclaimed
(Sheaf.CategoryTheory.CondensedFreeLinearizationTensor, Sheaf.CategoryTheory.CondensedGroupAlgebraExactForgetful,
Sheaf.CategoryTheory.PointedFreeDeletionContraction). Each publicly imported
Sheaf.CategoryTheory.CondensedInternalBarResolution only for the free-module data; the proof of
exists_resolution imports them, so the original line
`public import Sheaf.CategoryTheory.CondensedInternalBarResolution` closes an import cycle (error:
import cycle). It is replaced by `public import Sheaf.CategoryTheory.CondensedInternalBarData`. The
additional `public import` lines of Mathlib.CategoryTheory.Sites.LocalSite /
Mathlib.CategoryTheory.Sites.Coherent.CoherentSheaves and Mathlib.Combinatorics.Quiver.ReflQuiver
are not forced: those modules are already in the public import closure of CondensedInternalBarData
(through CondensedActionModule), so they change nothing others see. No signature, body or
visibility changed in any adapted module.

## No longer needed

No mathematical dependency or module is withdrawn. The free-linearization and tensor
comparison inputs remain needed transitively by the two new construction lemmas and the
existing contraction. All three declared construction obligations remain on the route.
The target proof directly imports PointedFreeDeletionContraction,
CondensedGroupAlgebraExactForgetful, CondensedEquivariantDeletionComparison and
CondensedInducedCoordinates, together with its public data import.

Removed unused proof imports from the target and extracted data module:
Sheaf.CategoryTheory.InternalSectionTensorComparison;
WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed;
WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor;
WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension;
Sheaf.CategoryTheory.ModuleObjects.KernelStructure;
Sheaf.CategoryTheory.ModuleObjectCokernelAction.
These are not claims of global pruning: several remain used by the existing dependency
proofs. Existing public imports of the target are retained. The three redirected
public imports remove the proof-dependency cycle; their new imported data has identical
bodies and signatures, and the original module reexports it.

## Where the brief, the DAG or earlier work was wrong

The three declared proof dependencies existed, but their public imports of the item
made the planned proof imports cyclic. The shared-data extraction repairs this without
changing a statement or construction. No mathematical error or departure from the unit
route was found. The two split statements isolate precisely the missing comparison glue
and the parent's continuous-coordinate step; neither restates the resolution theorem.

Edge checks: n=0 uses the terminal zero-fold power and regular module unit; the contraction
also works for the trivial group, zero coefficient ring, T=0 and non-flat T. The identity
point exists even on an empty test profinite space. The coordinate inverse uses ordered
partial products, so the statement does not assume that G is commutative. Tensoring uses
additivity and the underlying contraction, not preservation of kernels or flatness.

No definition chooses arbitrary data from an unproved existence theorem. The only
postponed choices are obtained locally inside the theorem proof, with all free-object,
action, differential and coordinate normalizations fixed by their generator formulas.

## New nodes

lem-sfb-condensed-equivariant-deletion-comparison is the normalized equivariant lift of
the deletion complex and its short-complex comparison, before any exactness assertion.
Its proof text supplies the representable power comparison, diagonal linearization,
transported maps and tensor-action construction.

lem-sfb-condensed-induced-coordinates is the independent continuous coordinate
linearization for any family with diagonal free generators. Its proof text gives the
successive-quotient map, ordered-product inverse, tensor comparison and equivariance.

CondensedInternalBarData contains only the already owned definitions, so no duplicate
definition node was created. The existing free-adjunction and generator definition nodes
now attach there. Searches (LeanSearch, Loogle/LeanFinder and source grep) found only
ordinary-ring Rep constructions and constant-ring condensed free objects, with different
coefficients. The source formulas were checked in Mathlib RepresentationTheory/Rep/Iso
and CategoryTheory/Action/Monoidal. No matching internal-condensed comparison node or
blueprint statement was found. Source remains the parent's agent-formulated internal
bar input, with its existing independent-reference WANTED qualification preserved.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
