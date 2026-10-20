## What changed

Proved `AlgebraicGeometry.ProEtale.pbcComparisonReductionMap_isIso` for an arbitrary
coefficient ring map. The ordinary scalar-extension comparison is invertible by
iterated mates and the restriction/coextension adjunction triangle. Comparison
inverse image preserves flat resolutions, so the ordinary mate computes the derived
mate on K-flat representatives. Naturality extends the result to every derived
object; uniqueness of left adjoints identifies the computed adjunctions with the
fixed choices used in the public definition.

Refactored the existing proof of `pbcRestriction_isRightAdjoint` into private scalar
extension, preservation, and adjunction helpers, so its unit computation can be used
in this proof. Added proved private localization and mate calculations, a local
relations proof of comparison flatness without a Noetherian assumption, and explicit
private preservation instances to avoid expensive instance searches. Bundled the
computed derived adjunction with its proved unit formula, so later checks use its
interface without normalizing the localization construction. Updated the
node's proof and proof origin. Public signatures are unchanged. Four public
definitions receive explicit functor arguments or a result type; their constructions
are judgmentally unchanged. No adopted source-library file is modified. The change records are:

- `coord/changes/X6-pbcFixedScalarExtension-explicit-functors.md`
- `coord/changes/X6-pbcFixedScalarExtensionComp-explicit-functors.md`
- `coord/changes/X6-pbcDerivedComparisonRestrict-explicit-functors.md`
- `coord/changes/X6-pbcComparisonReductionMap-explicit-functors.md`

Added private imports of `MapDerivedCategoryMate` for localization identities,
`Abelian.Flat.PreservesFlat` for images of flat resolutions,
`Mathlib.LinearAlgebra.TensorProduct.Finiteness` for finite tensor expansions, and
`ProEtale.Comparison.Flat` for the cover-preserving inclusion of sites.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.pbcComparisonReductionMap_isIso`.

Holes added: none. Sorries left in the delivered module: none. No results are split
off, and every new private helper is proved in this module.

Validation: the complete module compiled with no errors or warnings through
`lcompile.py` (45.2 seconds). The retained witness-interface tail is verbatim.
Private abstract-category lemmas and bundled adjunction data keep localization
constructions folded; sequential elaboration in the concrete site section avoids
repeated instance searches.

## No longer needed

No existing imports, nodes, or modules are withdrawn. The fixed-ring proof does not
invoke the generic ringed-topos tensor-pullback or change-of-rings nodes directly;
those nodes remain statement dependencies of the witness interface. The blueprint
unit and its own route are retained.

## Where the brief, the DAG or earlier work was wrong

The source-library comparison-flatness theorem assumes Noetherian coefficients,
whereas the assigned scalar comparison has no such hypothesis. The proof here uses
the whole relation kernel and a finite pure-tensor expansion of each local lift;
it does not require the kernel itself to be finitely generated. No statement is
weakened or disputed. The former open-proof placeholder in the node is replaced by
the actual K-flat and mate argument.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
