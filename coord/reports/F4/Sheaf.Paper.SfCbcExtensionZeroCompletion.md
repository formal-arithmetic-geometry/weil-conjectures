## What changed

In `Sheaf.Paper.SfCbcExtensionZeroCompletion`, prove
`sfCbcExtensionModel_existsUnique` and `sfCbcModelComplex_kflat` from an ordinary
binary tensor comparison for a ringed-site equivalence. Private proved helpers
transport total tensor complexes, acyclicity, K-flatness, and exact tensor-right
functors. The total-tensor helper follows the proved abstract argument in
`IntrinsicRealizationTensorComplex`, using the available upstream total-bifunctor
comparison directly and requiring only the explicit zero-morphism preservation
assumptions. The extension model has the actual termwise extended complex and the
specified standard-derived-factorization realization. Its uniqueness follows
from the prescribed complex and realization and proof irrelevance of its other
fields.

The model preservation proof applies the same ordinary comparison to the AsSmall
site equivalence, identifies the two descriptions of the module transport by
a generic identity for precomposition followed by restriction of scalars, and transports K-flatness and flat terms. The extension proof
first transports to the localized site, applies the existing proved
`ringedOpen_preserves_flat_resolution`, and converts site tensor flatness to the
monoidal tensor predicate with `siteSheafTensorRightIso`.

Add private proof imports of `RingedSiteEquivalenceTensor`,
`RingedOpenFlatResolution`, `TensorColimitsIndependentCoefficients`, the upstream
homological bifunctor comparison, and Mathlib's short-complex exactness transport.
Existing theorem signatures and public imports are unchanged. Three public definitions
receive judgmentally equal elaboration refactors, recorded in
`coord/changes/f4-sf-cbc-tensor-normalization-elaboration.md` and
`coord/changes/f4-sf-cbc-finite-evaluation-elaboration.md`, and
`coord/changes/f4-sf-cbc-evaluation-extension-elaboration.md`. The downstream audit
finds no external direct consumer of these definitions; the 32 downstream modules
need no adaptations.
No source-library module changes.

## Proved and sorry left

Original module: 11 named holes. Closed 2:

- `AlgebraicGeometry.Scheme.sfCbcExtensionModel_existsUnique`.
- `AlgebraicGeometry.Scheme.sfCbcModelComplex_kflat`.

Both use the new strictly smaller ordinary tensor-comparison obligation below;
the total-complex and flatness transport, model construction, and uniqueness are
complete Lean proofs. This is a reduction with one new hole, not two independent
proofs without remaining mathematical dependencies. The net hole reduction is one.

Remaining 9 holes in the item, all attached to
`lem-sf-cbc-extension-zero-completion`:

- `AlgebraicGeometry.Scheme.sfCbcOrdinaryTensorComparison_existsUnique`.
- `AlgebraicGeometry.Scheme.sfCbcTensorComparison_existsUnique`.
- `AlgebraicGeometry.Scheme.sfCbcRestrictExtensionIso_existsUnique`.
- `AlgebraicGeometry.Scheme.sfCbcFiniteTensorHom_isIso`.
- `AlgebraicGeometry.Scheme.sfCbcCompletionModelIso_existsUnique`.
- `AlgebraicGeometry.Scheme.sfCbcFiniteUnderlyingHom_transition`.
- `AlgebraicGeometry.Scheme.sfCbcFiniteModelIso_existsUnique`.
- `AlgebraicGeometry.Scheme.sfCbcCompletedReductionIso_evaluation`.
- `AlgebraicGeometry.Scheme.sfCbcRealizationExtensionIso_existsUnique`.

Added 1 hole:

- `SheafOfModules.pushforward_equivalence_tensor_iso`, in
  `Sheaf.CategoryTheory.RingedSiteEquivalenceTensor`, attached to
  `lem-sf-ringed-site-equivalence-tensor`. Its complete argument in words and source
  are recorded both in its docstring and its DAG node. It concerns only ordinary
  binary module-sheaf tensor transport, with no complex, K-flatness, flatness,
  completion, reduction, or extension-model assertion. It is used twice, for the
  localized-site and AsSmall equivalences. Its witness is eliminated only while
  proving propositions; no definition chooses arbitrary data from this existence
  theorem.

## No longer needed

None. No existing import, node, module, or declaration is removed. The unit route
is preserved. The existing dependency on localized strict tensor descent still
serves the untouched tensor-comparison obligations; it is not pruned.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or definition was found. The first proof step requires an
ordinary tensor comparison for the specific module-sheaf equivalences before
applying the existing localized K-flat preservation theorem. This tensor comparison
was not supplied by the declarations inspected. The DAG now records this missing
ordinary substep explicitly. Mathematical edge cases include the zero coefficient
ring, empty sites, unbounded complexes, and arbitrary (not necessarily sectionwise
flat) module sheaves; the ordinary equivalence argument covers all of them.

## New nodes

`lem-sf-ringed-site-equivalence-tensor`, in
`dag/nodes/sec-smooth-purity/lem-sf-ringed-site-equivalence-tensor.json`, states
ordinary binary tensor transport under a site equivalence continuous in both
directions and an invertible coefficient comparison. It specializes the intrinsic
ringed-topos tensor argument of Stacks Modules on Sites, tensor-product section and
lemma-tensor-product-pullback, to the actual precomposition/restriction functor.
Searches of LeanSearch, LeanFinder, Mathlib source, the project source and the
imported blueprint found no exact existing declaration. Its node has the item's
chapter/unit and blueprint ancestor `fix-lem-exchanges`. The parent proof records
how this one substep combines with proved total-tensor and exact-equivalence
arguments. The three change records above document the elaboration refactors; no mathematical
statement changes.


The delivery's verification is the required single-file compilation and axiom and
preflight checks run by deliver3.py. Profiling and alternate-expression
experiments are confined to scratch files; no diagnostic option or temporary
declaration is included in the packet.


Other local performance changes keep the existing maps fixed: use a sectionwise
presheaf-module identity for pushforward followed by scalar restriction, a generic
inverse-equivalence composition lemma for additivity, and a generic extensionality
proof for model uniqueness. Large derived and tensor constructions are locally
irreducible where their APIs suffice. Existing coefficient-universe sheafification
instances have local priorities adjusted to avoid repeated search, with the
original priority restored around the two section-generator definitions. Repeated
weak sheafification instances are cached by three proved private theorems and
reused inside the constant-ring proofs. A generic composition lemma compares
termwise complex functors before substituting the concrete module transports;
its application uses explicit additive proofs and fixes the source scheme.
No profiler, trace, disabled transparency, or changed compile-time limit remains.

The original quotient-presentation accessor and reduction functor are retained.
Private proved helpers expose sheafification compatibility on sections, model
construction from its specified data, and the completion projection's unit
identity. Their callers use these equations before substituting the large
concrete functors. Serial elaboration avoids overlapping checks of large terms;
the ordinary single-file compile limit is unchanged.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
