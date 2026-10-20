## What changed

In `Sheaf.Paper.ConstantRealizationDerivedScalarExtension`, proved the normalized
ordinary restriction comparison and the ordinary scalar-extension comparison.
Also simplified the existing `restriction_properties` proof: reflect finite
limits and colimits through the functor to abelian sheaves and use the explicit
ordinary tensor adjunction. The old proof obtained this ordinary instance from
the full derived change-of-rings theorem, making the axiom-dependency traversal
unnecessarily expensive for every new helper using scalar extension. Added a
private `import all Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`
to access its already proved canonical ordinary tensor construction.
All existing declaration signatures, public imports, definitions and docstrings
are unchanged. Added private, proved helpers and canonical private constructions.

`restrictionIso_existsUnique` now constructs the comparison by the module
sheafification Hom bijection. Its underlying map is locally bijective, so the
comparison is invertible. Constant sections detect equality, giving naturality
and uniqueness with the required normalization.

`moduleComparison_tensor` now has an explicit inverse: transpose a map on
constant generators through the ordinary tensor adjunction at each site object,
then extend it by module sheafification. The unit formula, scalar linearity and
tensor induction prove the inverse identities and the displayed pure-tensor
formula. This avoids the separate sheafification-tensor theorem and works with
the independently sized site universes of the statement.

Updated proof steps 1, 4 and 6 and proof_origin of
`lem-sfb-constant-realization-derived-scalar-extension` to record these arguments.
The remaining derived arguments retain their existing plan.

Preflight requests a change record for the local reducibility commands on the
private helpers. This is documented in
`coord/changes/a3-constant-realization-proof-local-reducibility.md`; there are no
public interface changes or forced adaptations.

## Proved and sorry left

Closed 2 of the 4 original holes, with no holes added and no split statements:

- `CategoryTheory.ConstantScalarRealization.restrictionIso_existsUnique`.
- `CategoryTheory.ConstantScalarRealization.moduleComparison_tensor`.

The following two original named theorem holes remain unchanged, both attached
to `lem-sfb-constant-realization-derived-scalar-extension`:

- `CategoryTheory.ConstantScalarRealization.constantRealizationDerivedScalarExtension`.
- `CategoryTheory.ConstantScalarRealization.constantRealizationDerivedScalarExtension_transitivity`.

No definition contains a hole. Every new private theorem is proved. The two
closed holes are proofs, not decompositions into new assumptions. The complete
item module was compiled on the project server after integrating both proofs
and removing the unused imports. A full profiling run compiled in 23 seconds.
`#print axioms` for both completed theorems reports exactly `propext`,
`Classical.choice`, and `Quot.sound`.

## No longer needed

Removed these unused private proof imports:

- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`.
- `Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral`.
- `Sheaf.Paper.KFlatRingedToposPullback`.

The ordinary tensor argument no longer needs
`lem-pc-sites-module-sheafification-tensor`; removed that node from proof step 4,
proof_deps and tool_uses. The other planned dependencies of the two unfinished
derived theorems remain recorded in the node. No module is withdrawn, and no
source-library declaration is changed or removed. No global claim that the
removed import modules are unreachable is made.

## Where the brief, the DAG or earlier work was wrong

No statement was found false and no statement or definition repair is included.
The tensor/sheafification route in step 4 is unnecessary for the ordinary
comparison: the two adjunctions give a direct inverse with the required
normalization. The supplied sheafification-tensor source has more restrictive
site universes, whereas this direct proof uses the independent-universe module
sheafification interface already available to the item. The K-flat and derived
transitivity steps are not claimed proved by this delivery.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
