# AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible

## Reason

The previous instance assumed only `TopologicalSpace.NoetherianSpace X`, but its
coefficient ring object was arbitrary. Topological noetherianity imposes no coherence
condition on that ring. The counterexample is already present over a geometric point:
let `k` be a field, `V = ⨁ n : ℕ, k`, and let `B = k ⊕ V` have multiplication
`(a,v)(b,w) = (ab, aw + bv)`. Thus `V² = 0`. Fix a nonzero `e ∈ V`.
Multiplication by `(0,e)` is a homomorphism `B → B` between rank-one free modules and
has kernel `0 ⊕ V`: its value at `(a,v)` is `(0,ae)`, which is zero precisely if `a=0`.
The action of `B` on this kernel factors through `k`; finitely many generators therefore
span a finite-dimensional subspace and cannot generate the infinite-dimensional `V`.
In particular this kernel is not finitely presented.

Take constant discrete coefficient and module sheaves on the pro-etale site of the
spectrum of a separably closed field. Their geometric fiber recovers the displayed
modules and preserves finite free presentations. Local finite presentation would give a
finite presentation on this fiber, so the constant kernel above cannot be locally finitely
presented. There is only one nonempty stratum of the geometric point. The cone of the
map between the two degree-zero free-module complexes consequently has nonconstructible
cohomology. Both source complexes are bounded constructible. This disproves the old
instance even with a one-point noetherian base.

This is the usual obstruction to kernel closure over a noncoherent coefficient ring;
compare [Stacks Project, Coherent rings](https://stacks.math.columbia.edu/tag/05CU).
The specific square-zero calculation above is explicit, rather than an assertion that
some unspecified noncoherent ring exists.

The repaired instance assumes exactly closure of constructible module objects under
kernels, cokernels and extensions. Zero membership and isomorphism invariance are proved
from the definitions, not added as hypotheses. No noetherian hypothesis is needed after
these three closure conditions are assumed. This is a correction of a false intermediate
statement, not a proof of the former unrestricted statement. The definitions of
`boundedConstructible`, `BoundedConstructible`, and `IsConstructibleModuleObject`, and all
the target signatures, are unchanged.

## Old

```lean
instance isTriangulated_boundedConstructible [TopologicalSpace.NoetherianSpace X] :
    (boundedConstructible R).IsTriangulated :=
  sorry
```

## New

```lean
instance isTriangulated_boundedConstructible
    [ObjectProperty.IsClosedUnderKernels (IsConstructibleModuleObject R)]
    [ObjectProperty.IsClosedUnderCokernels (IsConstructibleModuleObject R)]
    [ObjectProperty.IsClosedUnderExtensions (IsConstructibleModuleObject R)] :
    (boundedConstructible R).IsTriangulated := by
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsConstructibleModuleObject R) :=
    ⟨fun e hM ↦ constructible_of_iso R e hM⟩
  have : ObjectProperty.ContainsZero (IsConstructibleModuleObject R) :=
    ⟨0, isZero_zero _, constructible_of_isZero R (isZero_zero _)⟩
  change (DerivedCategory.TStructure.t.bounded ⊓
    DerivedCategory.homologyProperty (IsConstructibleModuleObject R)).IsTriangulated
  infer_instance
```

`Mathlib.CategoryTheory.ObjectProperty.Extensions` and
`Mathlib.CategoryTheory.ObjectProperty.Kernels` are public imports because the signature
names their classes. The general homology-property theorem is imported privately for the
proof. Three proved private helpers supply isomorphism invariance and the zero case.

## Users

`python3 tools/downstream.py WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory --uses isTriangulated_boundedConstructible`
finds 37 downstream modules and no textual use of the instance outside its own file
(docstrings are stripped by the tool). All 37 are listed below. The three direct
importers were recompiled, unchanged, with the corrected module in a sandbox overlay.
The other downstream references to shifts and triangulated functors concern the ambient
derived categories, whose triangulation is unchanged. None uses the triangulation of
this constructible full subcategory. No adaptation is necessary and none is delivered.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory | B4 | Replace the false unrestricted instance by its proved conditional version. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse | B2 | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover | C3 | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover | B3 | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | C2 | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex | C3 | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.AlgebraicGeometry.ProEtaleQcAffineContractibleCover | C4 | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.Paper.AdicCompletionReduction | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.Paper.CompletionMap | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | C1 | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Original file compiles against the corrected instance; no adaptation. |
| Sheaf.Paper.IntrinsicKoszulCompletion | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.Paper.KoszulQuotientLimit | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.RingTheory.BoundedWContractibleExtension | D3 | No textual use of the changed instance; unchanged category definitions and signatures. |
| Sheaf.Topology.BoundedExtremallyDisconnectedCover | F4 | No textual use of the changed instance; unchanged category definitions and signatures. |
| TargetsCheck | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | A2 | No textual use of the changed instance; unchanged category definitions and signatures. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | A2 | Original file compiles against the corrected instance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | E4 | Original file compiles against the corrected instance; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No textual use of the changed instance; unchanged category definitions and signatures. |

No target meaning is changed: every definition occurring in a target is unchanged. The
only modified theorem is an intermediate structural instance not referenced by a target
statement. The blueprint unit's statement and proof steps are unchanged.

## Status

landed 20261015T154153-L-159101 2026-10-15 (merge of deliver/B4/WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory)
