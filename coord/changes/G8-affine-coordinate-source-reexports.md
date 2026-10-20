# AlgebraicGeometry.affineCoordinateComplex_isKFlat

## Reason

The upstream sync quarantined `Sheaf.AlgebraicGeometry.AffineCoordinateModuleModels`
for an unavailable public `CochainComplex.IsAcyclicTensorKFlat`; its sole quarantined
consumer is `Sheaf.AlgebraicGeometry.AffineCoordinateTensorComparison`.
The adopted `WeilConjectures` twins already supply all seven coordinate declarations
and all fourteen tensor-comparison declarations with complete proofs. Restore the
old import paths as public re-exports of these twins, rather than recreating their
same-named declarations and the legacy K-flat dependency chain.

This is a zero-hole rework repair. The source implementation is used verbatim.
`IsKFlatTensor` and the legacy `IsAcyclicTensorKFlat` both mean acyclicity of
`mapBifunctor F K (curriedTensor _)` for every acyclic `F`, with precisely the same
ring sheaf, module universe and monoidal structure. The coordinate functors,
comparison data, and equivalence constructors have identical bodies. The tensor
comparison's only non-comment body difference replaces the additive-instance proof
`ModuleCat.extendScalars_additive_sheaf` by the source's
`ModuleCat.baseDerivedTensor_extendScalars_additive`; both prove the same Prop.
No target statement or source-library definition changes. Target-definition
semantic review is not reopened: the library was already using these source
constructions. The two DAG realization records now point to their source modules.
Their mathematical statements and proof-dependency lists stay unchanged.

## Old

Quarantined item, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineCoordinateComparisonData
import Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde
import Sheaf.Algebra.Homology.KFlatPullback
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! # Concrete module models for affine coordinates
Source: Stacks Project, Tags 08DW and 06Y1.
(blueprint: lem-pc-affine-coordinate-module-models). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- Tilde followed by the supplied coordinate isomorphism's pushforward. -/
noncomputable abbrev affineCoordinateModules (a : AffineComparisonCoordinate.{u, w}) :
    ModuleCat.{u} a.A ⥤ SheafOfModules.{u} (moduleRings a.X.toRingedSpace) :=
  tilde.functor a.A ⋙ SheafOfModules.pushforward a.σ.hom.toRingCatSheafHom

/-- The termwise concrete module model. -/
noncomputable abbrev affineCoordinateComplex (a : AffineComparisonCoordinate.{u, w}) :
    CochainComplex (ModuleCat.{u} a.A) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (moduleRings a.X.toRingedSpace)) ℤ :=
  (@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} a.A)
    (SheafOfModules.{u} (moduleRings (Spec a.A).toRingedSpace)) _ _ _ _
    (tilde.functor a.A) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙
    (@Functor.mapHomologicalComplex ℤ
      (SheafOfModules.{u} (moduleRings (Spec a.A).toRingedSpace))
      (SheafOfModules.{u} (moduleRings a.X.toRingedSpace)) _ _ _ _
      (SheafOfModules.pushforward a.σ.hom.toRingCatSheafHom)
      ⟨fun _ _ ↦ rfl⟩ (.up ℤ))

/-- The concrete module chart preserves zero maps. -/
instance affineCoordinateModules_preservesZero (a : AffineComparisonCoordinate.{u, w}) :
    (affineCoordinateModules a).PreservesZeroMorphisms where
  map_zero := by
    intro M N
    change (SheafOfModules.pushforward a.σ.hom.toRingCatSheafHom).map (tilde.map 0) = 0
    rw [tilde.map_zero]
    rfl

/-- Termwise application of the composite chart agrees with its two explicit factors. -/
noncomputable def affineCoordinateComplexFactorIso (a : AffineComparisonCoordinate.{u, w}) :
    (affineCoordinateModules a).mapHomologicalComplex (.up ℤ) ≅
      affineCoordinateComplex a :=
  NatIso.ofComponents (fun M ↦ HomologicalComplex.Hom.isoOfComponents
    (fun _ ↦ Iso.refl _) (by intros; simp)) (by intros; ext i; rfl)

/-- The supplied localized model is naturally its concrete module model's localization.
Source: Stacks Project, Tag 08DW; the supplied hd and hH.
(blueprint: lem-pc-affine-coordinate-module-models). -/
noncomputable def affineCoordinateModelIso (a : AffineComparisonCoordinate.{u, w}) :
    a.H ≅ affineCoordinateComplex a ⋙ DerivedCategory.Q :=
  a.hH ≪≫ Functor.isoWhiskerLeft _ a.hd

/-- Pushforward along an isomorphism, with inverse pushforward. -/
noncomputable def affineCoordinateModuleEquivalence {X Y : Scheme.{u}} (s : X ≅ Y) :
    SheafOfModules.{u} (moduleRings X.toRingedSpace) ≌
      SheafOfModules.{u} (moduleRings Y.toRingedSpace) :=
  CategoryTheory.Equivalence.mk (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
    (SheafOfModules.pushforward s.inv.toRingCatSheafHom)
    ((Scheme.Modules.pushforwardComp s.hom s.inv ≪≫
      Scheme.Modules.pushforwardCongr s.hom_inv_id ≪≫ Scheme.Modules.pushforwardId X).symm)
    (Scheme.Modules.pushforwardComp s.inv s.hom ≪≫
      Scheme.Modules.pushforwardCongr s.inv_hom_id ≪≫ Scheme.Modules.pushforwardId Y)

/-- Concrete coordinate models preserve K-flatness.
Source: Stacks Project, Tags 06Y1 and 08DW.
(blueprint: lem-pc-affine-coordinate-module-models).
Proof: tilde of M is K-flat. Pushforward along a scheme isomorphism is the inverse
of the opposite pushforward equivalence, hence is isomorphic, by uniqueness of
left adjoints, to tensor pullback along the inverse isomorphism. Pullback preserves
K-flatness. The termwise comparison and invariance under isomorphism give the result. -/
theorem affineCoordinateComplex_isKFlat (a : AffineComparisonCoordinate.{u, w})
    (M : CochainComplex (ModuleCat.{u} a.A) ℤ) (hM : AffineComparisonKFlat a.A M) :
    CochainComplex.IsAcyclicTensorKFlat (R := a.X.sheaf) ((affineCoordinateComplex a).obj M) := by
  let T := @Functor.mapHomologicalComplex ℤ (ModuleCat.{u} a.A)
    (SheafOfModules.{u} (moduleRings (Spec a.A).toRingedSpace)) _ _ _ _
    (tilde.functor a.A) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  have hT : CochainComplex.IsAcyclicTensorKFlat (R := (Spec a.A).sheaf) (T.obj M) :=
    isKFlat_tilde a.A M hM
  let e := affineCoordinateModuleEquivalence a.σ
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction a.σ.inv
  let θ : e.functor ≅ Scheme.Modules.tensorPullback a.σ.inv :=
    e.toAdjunction.leftAdjointUniq adj
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : (Scheme.Modules.tensorPullback a.σ.inv).Additive := Functor.additive_of_iso θ
  let q := (NatIso.mapHomologicalComplex θ (.up ℤ)).app (T.obj M)
  have hP : CochainComplex.IsAcyclicTensorKFlat (R := a.X.sheaf)
      (((Scheme.Modules.tensorPullback a.σ.inv).mapHomologicalComplex (.up ℤ)).obj
        (T.obj M)) := by
    have h := CochainComplex.isKFlat_pullback a.σ.inv.base a.X.sheaf
      (Spec a.A).sheaf ⟨a.σ.inv.c⟩ (T.obj M) hT
    convert h using 1
    rfl
  let := SheafOfModules.monoidalCategory a.X.sheaf
  intro F hF i
  exact (hP F hF i).of_iso
    (((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj F).mapIso q.symm)

end AlgebraicGeometry
```

The restored consumer previously defined the following comparison, verbatim;
its other declaration signatures match the source twin:

```lean
noncomputable def affineCoordinateComplexComparison
    (a b : AffineComparisonCoordinate.{u, w}) (φ : a.A →+* b.A)
    (p : b.X ⟶ a.X)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom) :
    affineCoordinateComplex a ⋙ perfectHomTensorComplex p ≅
      (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙
        affineCoordinateComplex b := by
  let := perfectHomTensorAdditive p
  have : (ModuleCat.extendScalars φ).Additive := ModuleCat.extendScalars_additive_sheaf φ
  have : (tilde.functor a.A).Additive := ⟨by intros; exact tilde.map_add _ _⟩
  have : (tilde.functor b.A).Additive := ⟨by intros; exact tilde.map_add _ _⟩
  have : (Scheme.Modules.pushforward a.σ.hom).Additive := inferInstance
  have : (Scheme.Modules.pushforward b.σ.hom).Additive := inferInstance
  have : (affineCoordinateModules a).Additive := by
    change (tilde.functor a.A ⋙ Scheme.Modules.pushforward a.σ.hom).Additive
    infer_instance
  have : (affineCoordinateModules b).Additive := by
    change (tilde.functor b.A ⋙ Scheme.Modules.pushforward b.σ.hom).Additive
    infer_instance
  exact Functor.isoWhiskerRight (affineCoordinateComplexFactorIso a).symm
      (perfectHomTensorComplex p) ≪≫
    Functor.mapHomologicalComplexCompIso (affineCoordinateTensorComparison a b φ p hp)
      (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ModuleCat.extendScalars φ ⋙ affineCoordinateModules b)) (.up ℤ)).symm ≪≫
    Functor.isoWhiskerLeft ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ))
      (affineCoordinateComplexFactorIso b)

```

Its public imports were:

```lean
public import Sheaf.AlgebraicGeometry.AffineCoordinateModuleModels
public import Sheaf.AlgebraicGeometry.PerfectHomCochainCounit
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
```

## New

`Sheaf.AlgebraicGeometry.AffineCoordinateModuleModels`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineCoordinateModuleModels

/-! # Concrete module models for affine coordinates

The adopted source library supplies the constructions and proofs. Re-export its
implementation so imports of this module use the same coordinate models.
(blueprint: lem-pc-affine-coordinate-module-models). -/

@[expose] public section
```

`Sheaf.AlgebraicGeometry.AffineCoordinateTensorComparison`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineCoordinateTensorComparison

/-! # Canonical underived comparison in affine coordinates

The adopted source library supplies the constructions and proofs. Re-export its
implementation so imports of this module use the same coordinate models.
(blueprint: lem-pc-affine-coordinate-tensor-comparison). -/

@[expose] public section
```

The source theorem re-exported at the old path has this signature:

```lean
theorem affineCoordinateComplex_isKFlat (a : AffineComparisonCoordinate.{u, w})
    (M : CochainComplex (ModuleCat.{u} a.A) ℤ) (hM : AffineComparisonKFlat a.A M) :
    CochainComplex.IsKFlatTensor (R := a.X.sheaf) ((affineCoordinateComplex a).obj M)
```

Every old declaration name is available from the compatibility imports. No new
public declaration, proof hole, or definition is introduced.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.AffineCoordinateModuleModels --uses
 affineCoordinateComplex_isKFlat` reports an unknown module because it is quarantined.
A search of `lean/` and `quarantine/` finds the restored tensor-comparison module as
its only remaining direct consumer. There are no other imports of either Sheaf
module. The canonical source-module downstream checks list the modules below;
none needs an adaptation because their exact existing source implementation is
being re-exported. In particular the canonical derived-comparison and chart-cocycle
modules already use `IsKFlatTensor`.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineCoordinateModuleModels | G8 | Restore as source re-export; zero holes. |
| Sheaf.AlgebraicGeometry.AffineCoordinateTensorComparison | unclaimed | Restore consumer as source re-export; zero holes. |
| WeilConjectures | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.AffineBaseChangeModelComparisonIsos | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.AffineBaseChangeModelIsosOfSchemeComparisons | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.AffineCoordinateComparisonChartCocycle | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.AffineCoordinateComparisonCoherence | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.AffineCoordinateComparisonFamilyBase | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.AffineCoordinateDerivedComparison | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.AffineCoordinateTensorComparison | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.AffineModelCoherentObjectComparisons | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.AffineModelComparisonDataFromHomEquations | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.AffineModelComparisonOfBottomModels | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.AffineModelLimitHomEquationOfCoherentObjects | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.AffineModelStageHomEquationOfCoherentObjects | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.AffinePerfectChainGeometricModels | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.AffinePerfectChainHomPresentation | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.AffinePerfectHomPresentation | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.AffineSpecifiedModelChainComparison | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.PerfectDescendMorphisms | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.PerfectHomContinuity | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.PerfectHomContinuityAffine | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.PerfectHomPresentation | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.RecordedPerfectHomContinuity | unclaimed | Existing canonical source consumer; no change. |
| WeilConjectures.AlgebraicGeometry.AffineCoordinateModuleModels | unclaimed | Existing canonical source consumer; no change. |

Both restored modules compile independently in under two seconds. An import probe
checks all seven coordinate declarations and both tensor/homotopy composition laws:
all depend only on `propext`, `Classical.choice`, and `Quot.sound`. Import-direction
checks accept both source imports. The unit route and its realized steps are kept.

## Status

landed 20261020T150639-L-2551339 2026-10-20 (merge of deliver/G8/Sheaf.AlgebraicGeometry.AffineCoordinateModuleModels)
