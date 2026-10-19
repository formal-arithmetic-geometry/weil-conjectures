## What changed

Retained the interrupted proof of
`AlgebraicGeometry.Scheme.etaleSum_preserves_flat_kflat`. Its signature and three
realization/extension definitions are unchanged. Flatness follows from the existing
categorical-flatness preservation instance for étale lower shriek and a coefficient
comparison. K-flatness follows from the tensor-test projection comparison, exact
extension of acyclic complexes, and invariance of exactness under an isomorphism.
The flat-term assertion applies the flatness assertion degreewise.

Further reduced the coefficient comparison: `etaleConstantModule_flat_iff` now
transports exactness across the natural right-tensor isomorphism and the canonical
realization equivalence. The new realization equivalence theorem is proved from
constant-scalar realization and transport along a ring isomorphism. All extension
and inverse-image functors have explicit constructions; no arbitrary existence
witness supplies definition data.

## Proved and sorry left

Proved the original theorem
`AlgebraicGeometry.Scheme.etaleSum_preserves_flat_kflat` from proved auxiliary lemmas.
The item module has zero remaining holes. The following new auxiliary theorems have
complete proofs (all in `AlgebraicGeometry.Scheme`):

- `etaleSum_preserves_flat_aux`;
- `etaleSum_preserves_kflat_aux`;
- `etaleSum_preserves_flat_terms_aux`;
- `etaleConstantModule_flat_iff`;
- `etaleSumTensorTestRealization_isEquivalence`;
- `etaleSumTensorTestExtension_exact` and `etaleSumTensorTestComplexExtension_acyclic`;
- `etaleSumTensorTestInverseImage_exact` and `etaleSumTensorTestInverseImageComplex_acyclic`.

The two structural comparisons are also proved:

- `etaleConstantModule_tensor_comparison` and
  `etaleConstantModule_tensorRight_comparison`, node
  `lem-pur-etale-constant-module-tensor`: identify constant-scalar realization with
  module sheafification of the explicit sectionwise encoding, then compose the
  existing natural sheafification tensor comparisons and counits.
- `etaleSum_tensor_test_comparison`, node
  `lem-pur-etale-sum-tensor-test-projection`: transport the published unbounded
  projection comparison through the coefficient equivalence, using signed tensor
  symmetry and the additive totalization comparison.

Holes closed: the one original hole
`AlgebraicGeometry.Scheme.etaleSum_preserves_flat_kflat`. Holes added: zero.
Every delivered module has zero remaining `sorry`s; no theorem is split off with
an unfinished proof. Existing dependencies supply their published declarations.
The seven new auxiliary nodes record separate, proved parts of the argument.
Zero coefficients, zero complexes and empty schemes require no extra hypotheses.
The full seven-module sandbox compiles cleanly through `lcompile.py --all`; the
projection comparison compiles in 49.1 seconds and the item in 6.6 seconds. The
original theorem signature and all three original definitions were also compared
verbatim against current sources and are unchanged.

## No longer needed

Removed the item's proof-only import
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`. The large
ringed-site existential theorem `prop-weil-pbc-inverse-image-modules-exact` is no
longer needed by this route: the concrete transported inverse image uses the
published exact upper-star functor on ModuleCat-valued sheaves. No claim is made
that this module is unreachable from every other target dependency.

The new auxiliary modules also discard unused flatness imports from the K-flat
argument, unused K-flatness/additive imports from flatness, and unused projection,
pullback, separatedness, and finite-type imports from the general transported-functor
module. The tensor-test projection module needs only that general module and its
separatedness/finite-type hypotheses in its public imports.

The item imports `EtaleSumPreservesFlat` and `EtaleSumPreservesKFlat` for its actual
proof. The flatness argument reuses the proved native projection/flatness API in
`EtaleMapProjection`; it does not import the separately stated
`Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafProjectionMap`. The stronger node
`lem-pur-etale-sheaf-projection-map` is not needed by this proof: the native Kan
projection node `lem-pur-etale-projection-kan-comparison` supplies the projection
used by the existing flatness preservation instance. Its extra section/stalk
normalizations are unnecessary here. Sum-extension exactness and unbounded tensor
totalization remain necessary. The flat-terms node is proved
inside the item, with no separate module.

## Where the brief, the DAG or earlier work was wrong

The interrupted sandbox's report and component nodes did not describe its later
proofs. The retained exactness proof failed because extensionality descended too
far and identity-equivalence projections did not unfold at tactic transparency.
The repaired proof uses a proved private ring-transport equivalence helper and the
published constant-scalar unit and counit. Categorical flatness preservation already
exists in `EtaleMapProjection`, so its proof is reused.

The coefficient encodings have a categorical equivalence, but using it for
flatness and K-flatness also requires its tensor compatibility. The retained work
constructs this compatibility from the existing sheafification tensor comparison;
it is now used for both assertions. The retained projection proof additionally
needed the `MonoidalCategory` namespace and an explicit additive realization
instance. The dry run additionally exposed a tensor-bifunctor mismatch: currying the
uncurried tensor is naturally isomorphic to the existing curried tensor, rather
than definitionally equal. A proved generic private helper now constructs the
comparison from its two-variable naturality, avoiding expensive unfolding of the
sheaf-specific tensor definitions. No target, existing signature or existing
definition was changed.

## New nodes

`lem-pur-etale-sum-flat-aux` records the proved conversion to categorical flatness,
application of étale lower-shriek preservation, and conversion back.

`lem-pur-etale-sum-kflat-aux` records the proved acyclic-test argument, using exact
extension and the proved tensor-test comparison.

`lem-pur-etale-sum-flat-terms-aux` records degreewise application of flatness
preservation, proved in the item module.

`lem-pur-etale-sum-tensor-test` records explicit transported functors, exactness,
and preservation of acyclicity, together with the realization and total-tensor
helpers. All its theorems are proved.

`lem-pur-etale-constant-module-flat` records the proved transfer of tensor exactness
across the canonical realization equivalence and the right-tensor comparison.

`lem-pur-etale-constant-module-tensor` records the proved natural tensor comparison,
with its universal-property proof and empty/zero edge cases in the docstring.

`lem-pur-etale-sum-tensor-test-projection` records the proved unbounded tensor-test
comparison, with the constant-coefficient transport and signed symmetry argument
in its docstring. No definition or statement change record is needed.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
