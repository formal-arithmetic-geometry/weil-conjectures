# IsCanonicalPullbackTensorComparison

## Reason

The assigned module is quarantined in coord/rework.tsv and has zero holes.
Restoring its archived bytes fails immediately because its public import of
Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel no longer exists.
The adopted source already supplies every public declaration of this module,
with the same proof route and no textual sorry. Restoring the archived declarations
would also duplicate the adopted public names. Restore the Sheaf import path as
a compatibility module referring to the adopted source instead.

The retirement census called the canonical predicate DIFFERENT. The only predicate
change is IsAcyclicTensorKFlat to IsKFlatTensor: the definitions agree by reduction.
Copied all three archived definition bodies under fresh scratch names and compiled
these exact tests against the adopted source and Sheaf.Algebra.Homology.KFlat:

```lean
example : @archivedPullbackTensorTotal = @pullbackTensorTotal := rfl
example : @archivedPullbackTensorModelMap = @pullbackTensorModelMap := rfl
example : @archivedIsCanonicalPullbackTensorComparison =
    @IsCanonicalPullbackTensorComparison := rfl
```

All passed in 14.3 seconds. These compare full definitions at all their universes,
not only the K-flat predicate. Thus the re-exported definitions preserve meaning,
including for targets using them. No target statement or upstream source is edited.

The extra private import all is needed: the quarantined
DerivedPullbackCompositionTensorKFlat consumer imports all of the old Sheaf module
and uses counit_isIso and modelMap_isIso. A sandbox consumer checking both helpers
and all public theorems fails with only the public import and passes with both
imports (2.7 seconds). The further public import of Sheaf.Algebra.Homology.KFlat preserves the legacy
IsAcyclicTensorKFlat and IsKFlatResolution names inherited by archived consumers.
The final consumer audit uses public declarations with the old hP predicate and
actually applies both source helpers; it passes in 5.8 seconds. No consumer edit
is needed. Full quarantined consumer compiles also require restoration of their
other dependencies, outside this packet; these isolated checks verify the API
this repair supplies.

Both existing DAG attachments now name the actual adopted declaration module.
Their declarations, mathematical statements, proof steps, and proof dependencies
are retained. The archived files stay in quarantine; this is not withdrawal.

## Old

Archived imports and the three definition bodies (verbatim):

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
public import Mathlib.Algebra.Homology.Monoidal
import Sheaf.Algebra.Homology.KFlatPullback

def pullbackTensorTotal (X : Scheme.{uTC})
    (P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ :=
  letI := pullbackDescentModuleTensor X
  CochainComplex.mapBifunctor P N (curriedTensor _)

/-- The canonical localization tensor map, invertible on K-flat coordinates.
It is the upstream lax monoidal map of Q for the recorded derived tensor.
Source: Stacks, 06YH and 079U
(blueprint: def-pc-derived-pullback-tensor-comparison). -/
def pullbackTensorModelMap (X : Scheme.{uTC})
    [HasDerivedCategory.{wTC} (SheafOfModules.{uTC} (moduleRings X.toRingedSpace))]
    (P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N ⟶
      DerivedCategory.Q.obj (pullbackTensorTotal X P N) := by
  letI := pullbackDescentModuleTensor X
  letI := moduleSymmetric X
  haveI := modulePreadditive X
  letI := moduleClosed X
  haveI := moduleGrothendieck X
  haveI := moduleResolutions X
  haveI := moduleDerivedMonoidal X
  exact @Functor.LaxMonoidal.μ _ _ _ _ _ _ _ (pullbackDescentQLax X) P N

def IsCanonicalPullbackTensorComparison {T X : Scheme.{uTC}} (g : T ⟶ X)
    (τ : ∀ E K : schemeDerivedCategory X,
      (derivedPullback g).obj (E ⊗ K) ⟶
        (derivedPullback g).obj E ⊗ (derivedPullback g).obj K) : Prop :=
  letI := pullbackDescentModuleTensor X
  letI := pullbackDescentModuleTensor T
  letI := modulePreadditive X
  letI := modulePreadditive T
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor T.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj T.sheaf
  (∀ P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ,
    P.IsAcyclicTensorKFlat → N.IsAcyclicTensorKFlat →
    ∃ φ : ((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal X P N) ≅
      pullbackTensorTotal T
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N),
      (∀ (p q n : ℤ) (h : p + q = n),
        (Scheme.Modules.tensorPullback g).map
            (HomologicalComplex.ιMapBifunctor P N (curriedTensor _) (.up ℤ) p q n h) ≫
          φ.hom.f n =
        ((Classical.choose (Scheme.Modules.module_pullback_tensor g)) (P.X p) (N.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)
            (curriedTensor
              (SheafOfModules.{uTC} (moduleRings T.toRingedSpace))) (.up ℤ) p q n h) ∧
      (derivedPullback g).map (pullbackTensorModelMap X P N) ≫
          (SingleComplexBaseChange.counit g).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal X P N)) ≫
          DerivedCategory.Q.map φ.hom =
        τ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) ≫
          ((SingleComplexBaseChange.counit g).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
            (SingleComplexBaseChange.counit g).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
          pullbackTensorModelMap T
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)) ∧
    ∀ (E E' K K' : schemeDerivedCategory X) (a : E ⟶ E') (b : K ⟶ K'),
      (derivedPullback g).map (a ⊗ₘ b) ≫ τ E' K' =
        τ E K ≫ ((derivedPullback g).map a ⊗ₘ (derivedPullback g).map b)

```

The archive additionally declares exists_canonical_from_model,
exists_canonicalPullbackTensorComparison and IsCanonicalPullbackTensorComparison.unique,
and proved private helpers. All are provided by the adopted source under the same names.

## New

The complete restored module is:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Sheaf.Algebra.Homology.KFlat
-- Preserve helper access for consumers using `import all` on this compatibility path.
import all WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison

/-! # Canonical tensor comparison for derived pullback

Compatibility import of the adopted source implementation, including the total tensor,
localization tensor map, canonical comparison predicate, model transport, existence and
uniqueness theorems. This keeps the original Sheaf import path usable without redeclaring
those constants. The source predicate uses `IsKFlatTensor`, whose definition agrees with
`IsAcyclicTensorKFlat` in the archived Sheaf implementation.

Source: Stacks Project, Cohomology, Tag 079U; perfect.tex, Tag 0DJA(1)
(blueprint: def-pc-derived-pullback-tensor-comparison;
def-pc-derived-pullback-tensor-comparison-model-transport).
-/

@[expose] public section
```

Both node lean.module fields become
WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison,
with the same declarations and existing: true. Their proof dependencies stay intact.

## Users

There are no live direct importers at the checked source snapshot; the old path is
absent from lean. tools/downstream.py reports unknown module for that reason.
The following direct importers are preserved in quarantine and were also inspected.
All use the same re-exported public definitions/theorems. Import-all helper access
is separately checked as explained above. Group holders are from coord/claims.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomModel | unclaimed | quarantined; identical public API by conversion; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionTensorKFlat | unclaimed | quarantined; identical public API by conversion; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | unclaimed | quarantined; identical public API by conversion; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange | unclaimed | quarantined; identical public API by conversion; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitIsomorphism | unclaimed | quarantined; identical public API by conversion; no adaptation. |
| Sheaf.AlgebraicGeometry.InternalHomBaseChangeExchange | unclaimed | quarantined; identical public API by conversion; no adaptation. |
| Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso | unclaimed | quarantined; identical public API by conversion; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | unclaimed | quarantined; identical public API by conversion; no adaptation. |
| Sheaf.AlgebraicGeometry.TensorCoordinateIdentifications | unclaimed | quarantined; identical public API by conversion; no adaptation. |
| Sheaf.AlgebraicGeometry.TensorCounitOneKFlatCoordinates | unclaimed | quarantined; identical public API by conversion; no adaptation. |
| Sheaf.AlgebraicGeometry.TensorStalkChainCoordinates | unclaimed | quarantined; identical public API by conversion; no adaptation. |
| Sheaf.AlgebraicGeometry.TensorStalkFixedMapSquare | unclaimed | quarantined; identical public API by conversion; no adaptation. |

No source declaration is removed, redefined or weakened. No module is withdrawn.
The unit realization and all DAG mathematical dependencies remain unchanged.

## Status

landed 20261021T192754-L-724351 2026-10-21 (merge of deliver/B4/Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison)
