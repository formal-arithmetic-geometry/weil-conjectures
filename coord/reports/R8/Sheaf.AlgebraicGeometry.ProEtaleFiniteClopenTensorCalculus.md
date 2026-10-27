## What changed

In `Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus`, proved
`AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.restriction_exact` and
`AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.finite_clopen_derived_calculus`.
All public theorem statements, universes, and docstrings are retained.

The restriction proof reflects finite limits through the underlying additive-sheaf functor
and obtains finite colimits from the actual pushforward's left-adjoint instance. The derived
proof constructs the inverse on complexes from the existing module-gluing equivalence,
uses the product localization to descend it, and transports the finite coordinate bicone
through the resulting equivalence. It also proves the empty-component and empty-partition
clauses. The module-gluing declaration is an intended existing proof dependency.

Added private proof imports
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
`Mathlib.CategoryTheory.Functor.ReflectsIso.Exact`, and
`Mathlib.CategoryTheory.PUnit` for joint derived detection, exact reflection, and the
terminal-category cases. The existing product-localization imports are used directly.

The inverse derived tensorator now supplies its two native monoidal structures explicitly,
with local transparency settings, to avoid unfolding the native tensor construction during
instance inference. Its data and its public signature are unchanged. Private local transparency
attributes keep already constructed categorical structures abstract during these proofs.
See `coord/changes/R8-finite-clopen-native-tensor-transparency.md`.

The module and its unchanged direct consumers `Sheaf.Paper.FiniteClopenDerivedDecomposition`
and `Sheaf.Paper.SfClopenDerivedCompatibility` compile against the resulting module.
The final `lcompile.py --all` check passed for the module and both consumers, taking
35.5 s, 46.1 s, and 12.6 s respectively.

## Proved and sorry left

Closed 2 of the item's original 4 holes, with no holes added:

- `AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.restriction_exact` — proved.
- `AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.finite_clopen_derived_calculus` — proved.

The two original holes remain, each at
`lem-pur-finite-product-derived-tensor-calculus`:

- `AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.finite_clopen_tensor_calculus`.
- `AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.finite_clopen_scalar_calculus`.

Their complete original source/proof docstrings and statements remain. This is a partial
proof delivery, not a decomposition. No new public statements or modules are delivered.

## No longer needed

Removed the item's direct imports of:

- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`, using its data module
  `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientData` for the existing public interface.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Homology.ScalarHomTensorCancellation`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology` (already available through
  the exact reflection API).

The completed derived proof does not need the statement-only
`lem-pur-clopen-unbounded-derived-localization`: it builds the localization argument
from the module-gluing declaration and Mathlib. The other three planned calculus nodes
remain relevant to the unproved tensor and scalar declarations. Their dependencies and
all existing source-library declarations remain; no globally unused module is claimed.
Experimental helper modules and draft nodes are not part of this delivery.

## Where the brief, the DAG or earlier work was wrong

The live DAG was re-split during this session into four statement-only nodes, without
Lean attachments. The packet updates only the completed derived part of that route;
it preserves the current three remaining planned steps. No unit realization is bypassed.

The tensor and scalar arguments were developed in scratch work but do not form a verified
complete module. In particular, conversion between `coefficientTotalTensor` and the
native complex tensorator repeatedly exceeded the compilation limit; the integrated
scalar proof also exceeded that limit. These attempts are not counted as proofs.
No split was introduced to evade the limit, no timeout was treated as a tool failure,
and no source-library signature, attribute, or public import was changed.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
