## What changed

Proved `SheafOfModules.openImmersionTensor_iso` in
`Sheaf.Paper.OpenImmersionTensorPiece`. All existing public definitions and the target
signature are unchanged. Added only proved private helpers in that module.

The proof uses the ordinary slice extension-tensor comparison, exact extension on
complexes, a K-flat coefficient resolution, and a proved private one-K-flat-factor tensor
comparison. The latter uses flat K-flat resolutions of both factors, the existing
TensorModel representative isomorphism, and mapping-cone tensor/flip isomorphisms.
It then uses the invertible open-extension adjunction unit and the proved
categorical projection-map criterion to identify the canonical normalized map. Naturality
and uniqueness are checked in Lean, including the exact inverse normalization of the
statement. The stronger intermediate argument works for every derived coefficient;
restriction gives the existing strict-perfect statement.

Added private proof imports for `Adjunction.ProjectionMap`, locally bijective
sheafification and its restriction, `RingedSliceExtensionTensor`, `TotalComplexMap`,
`BifunctorMappingCone`, `BifunctorFlip`, the cone acyclicity criterion, and
`TensorColimitsIndependentCoefficients`. Updated the item's DAG proof, proof
dependencies and proof origin to this route. No other module was edited.
The ordinary comparison is packaged in proved generic lemmas. Canonical presheaf tensor
structures and derived-category choices are supplied explicitly inside proofs to avoid
repeated instance searches and unfolding. The proof-scope commands required by the static gate are
recorded in `coord/changes/open-immersion-tensor-proof-scope.md`; no consumer needs adaptation.

## Proved and sorry left

Closed the original single hole:
`SheafOfModules.openImmersionTensor_iso`
(node `lemma-weil-pbc-projection-formula-open-piece`).

Original holes: 1. Closed: 1. Added: 0. Remaining in the delivered module: 0.
The final proof, including the delivery tool's axiom probe, passed `lcompile.py`
in 29.8 seconds. The probe checked all six public declarations.
No split statements, new axioms, or holes in definitions. All private helpers are proved.
The proof uses the existing `ringedSlice_extension_tensor` theorem; its proof and
dependencies are outside this packet.

## No longer needed

Removed these private imports:

- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `Mathlib.Algebra.Homology.BifunctorShift`.
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`.
- `Sheaf.Algebra.Homology.KFlat`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`.

The proof no longer directly needs the finite-free/retract argument, bounded-above
flatness, a strict-perfect package on a chosen representative, or signed homotopy
calculations for descending the resulting map. The canonical map and its naturality
are instead inherited from the categorical adjunction projection transformation.
Removed direct proof dependencies:

- `lem-weil-proetale-weakly-etale-localization`: the theorem is already stated on
  the slice, and only monomorphy of the open immersion is needed in its proof.
- `lem-sf-exact-functor-derived-triangulated`: the already-defined localized derived
  operations and their factorization/unit formulas suffice.
- `lem-weil-pbc-ringed-topoi-module-pullback-tensor`: the input `t` supplies the
  normalized derived comparison; ordinary essential-image closure uses the slice formula.
- `def-weil-pbc-strict-perfect-coefficient-package` and
  `lem-pc-bounded-above-flat-kflat-site`: the argument works for any coefficient.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` and
  `lem-weil-pbc-site-derived-tensor-descent`: use the TensorModel representative field and
  a proved private one-K-flat comparison from the existing flat K-flat resolutions
  and tensor mapping-cone lemmas.
- `def-pc-tensor-complex-sheaves`: Mathlib's bicomplex and total-complex API supplies
  the actual totalization and signs.

Withdrew the obsolete top-level tool approvals for
`lem-weil-proetale-weakly-etale-localization`,
`lem-sf-exact-functor-derived-triangulated`, and
`lem-pc-bounded-above-flat-kflat-site`; retained the other approvals in their original order.
These are removals from this proof route, not requests to delete declarations or
modules that remain needed by public statements or other consumers. All original
public imports are preserved. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old finite-projective proof route is valid as a plan but is unnecessary below
this item: the ordinary slice formula plus a K-flat coefficient resolution proves
the essential-image condition for arbitrary derived coefficients. A fully faithful
open-extension adjunction then proves that the specifically normalized projection
map is invertible. The unit's own open-piece statement and the compactification
route are preserved. No statement or definition repair was needed.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
