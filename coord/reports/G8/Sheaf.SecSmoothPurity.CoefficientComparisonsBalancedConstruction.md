## What changed

Prove `CategoryTheory.CoefficientComparisonsBalanced.coefficientComparisons_balanced_construction`
from the existing normalized composition theorem and the scalar-extension tensor construction.
The public theorem, every definition, all four section formulas, independent universes, and
hypotheses are unchanged. Private helpers express scalar linearity, balancing and generation.
The two common-pullback comparisons are constructed by two applications of
`CochainCompositeHom.normalizedScalarComposition_exists`. Their formulas give both formulas
for `k = l.symm ≪≫ h`; uniqueness follows from the common-pullback normalization and
extension-of-scalars extensionality. The existing
`CochainTensorComparison.canonicalRingedTensorComparison_existsUnique` supplies the scalar
comparison. Evaluate its generalized pure normalization on the product of the underlying
module sheaves to get the coefficient-one formula for arbitrary local sections. Linearity
and bilinearity give the displayed forward and inverse formulas. The same canonical
comparison's subsingleton property gives the required normalization and uniqueness.
A private `import all` of `CochainTensorCoherenceData` reuses its proved product-section
and tensor-pair helpers. A private generic record conversion transfers existence and
uniqueness to the public comparison record. Private helpers expose their sheafification
instances as explicit parameters, avoiding repeated construction while checking the proofs.
No public declaration or definition is added or changed. A proved private helper caches
Mathlib's existing sheaf-composition instance for the proofs. Elaboration runs synchronously
to avoid scheduling overhead at the single-file compile limit.

## Proved and sorry left

The delivery closes the original hole in
`CategoryTheory.CoefficientComparisonsBalanced.coefficientComparisons_balanced_construction`.
Holes closed: 1. Holes added: 0. No sorry remains in the item or is added elsewhere.
No split-off theorem or new public declaration. The complete proof has compiled successfully.
Earlier delivery checks hit the 60-second limit; profiling identified repeated instance
inference. The final version caches that instance privately, retains synchronous elaboration,
removes profiling, and omits unused private instance parameters. Delivery validates this
final version and checks its axiom dependencies.

## No longer needed

The proof reuses established constructions rather than reconstructing their balanced
pairings. The following former direct proof dependencies are no longer used directly:

- `Sheaf.SecSmoothPurity.CochainInverseComparison` /
  `lem-pur-independent-inverse-image-tensor-comparison`;
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal` /
  `lem-pc-sites-sheaf-tensor-bilinear-universal`;
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension` /
  `lem-pc-sites-module-sheafification-bilinear-extension`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarTensorInverseFormulas` /
  `lem-pd-sheaf-scalar-tensor-inverse-formulas`;
- `Mathlib.LinearAlgebra.TensorProduct.Basic`;
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.

The normalized composition theorem supplies the two common-pullback isomorphisms, and the
proved canonical ringed tensor construction supplies the scalar isomorphisms. The three former
`tool_uses` entries for the bilinear universal property, bilinear sheafification extension,
and scalar inverse formulas are therefore withdrawn from this node. Some of their
mathematics remains used inside the reused constructions; no module withdrawal or
source-library declaration removal is proposed. No whole-library pruning count is claimed. The two Mathlib imports are redundant
through the retained imports.

## Where the brief, the DAG or earlier work was wrong

The DAG plan repeats existing constructions. The existing normalized scalar-composition
result constructs both comparisons from the common pullback directly, and its normalization
on the identity generalized section covers arbitrary inverse-image sections. Thus no lift
of a local section from the source site is required. The established independent-universe
canonical tensor comparison already includes a true inverse and simultaneous naturality.
The simplified node proof records these uses. There is no unit-route change:
`sk-def-purity-conv` has no realized statement or proof-step obligation at this node.

Searches used msearch LeanFinder (scalar extension of sheaves, composition and tensor
normalization), Loogle (`SheafOfModules.pullbackComp`), msearch grep, and local ripgrep.
Mathlib's continuous-site pullback composition does not directly match arbitrary geometric
inverse-image presentations; the proved library APIs do match. All formulas require only
unital ring maps, so zero rings, identity maps, and nonflat coefficient quotients remain
covered without new assumptions.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
