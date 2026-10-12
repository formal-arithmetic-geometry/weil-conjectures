/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Sheaf.AlgebraicGeometry.ModulePullbackTensor
public import Mathlib.Algebra.Homology.Monoidal

/-! # Canonical tensor comparison for derived pullback

Source: Stacks Project, Cohomology, Tag 079U; perfect.tex, Tag 0DJA(1)
(blueprint: def-pc-derived-pullback-tensor-comparison).
The comparison is the unique family satisfying `IsCanonicalPullbackTensorComparison`:
it is pinned by the actual module pullback tensor map and the shared left-derived
counit on K-flat representatives. Statements bind the comparison together with this
uniquely characterising predicate; no monoidal structure on pullback is chosen
arbitrarily and no data is chosen from a theorem.
-/

@[expose] public section

universe uTC wTC
open CategoryTheory CategoryTheory.Limits MonoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry

/-- The total tensor complex used in the coordinate equation below.
Source: Stacks, 079U (blueprint: def-pc-derived-pullback-tensor-comparison). -/
def pullbackTensorTotal (X : Scheme.{uTC})
    (P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ :=
  letI := SheafOfModules.monoidalCategory X.sheaf
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
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.symmetricCategory X.sheaf
  haveI : MonoidalPreadditive (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  letI : MonoidalClosed (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  haveI : IsGrothendieckAbelian.{uTC} (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  haveI : CategoryTheory.Limits.HasColimitsOfSize.{0,0}
      (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) :=
    CategoryTheory.Limits.hasColimitsOfSizeShrink.{0,0,uTC,uTC} _
  haveI := schemeModule_hasFunctorialFlatResolution X
  haveI := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{uTC} (moduleRings X.toRingedSpace))
  haveI (A B : GradedObject ℤ (SheafOfModules.{uTC} (moduleRings X.toRingedSpace))) :
      GradedObject.HasTensor A B := inferInstance
  letI := HomologicalComplex.monoidalCategory
    (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) (.up ℤ)
  haveI : (DerivedCategory.Q
      (C := SheafOfModules.{uTC} (moduleRings X.toRingedSpace))).LaxMonoidal := inferInstance
  exact Functor.LaxMonoidal.μ (DerivedCategory.Q
    (C := SheafOfModules.{uTC} (moduleRings X.toRingedSpace))) P N

variable [∀ Y : Scheme.{uTC},
  HasDerivedCategory.{wTC} (SheafOfModules.{uTC} (moduleRings Y.toRingedSpace))]

/-- The canonical tensor comparison is characterized on every pair of K-flat
representatives by the left-derived counits, the localization tensor maps and
termwise module pullback. The degreewise equation pins the chain isomorphism to
the canonical module tensor map on each summand, including its signs.
Source: Stacks, 079U; perfect.tex, 0DJA(1)
(blueprint: def-pc-derived-pullback-tensor-comparison). -/
def IsCanonicalPullbackTensorComparison {T X : Scheme.{uTC}} (g : T ⟶ X)
    (τ : ∀ E K : schemeDerivedCategory X,
      (derivedPullback g).obj (E ⊗ K) ⟶
        (derivedPullback g).obj E ⊗ (derivedPullback g).obj K) : Prop :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.monoidalCategory T.sheaf
  letI := Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  letI := Classical.choice (SheafOfModules.tensorClosed T.sheaf).1
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor T.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj T.sheaf
  (∀ P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ,
    P.IsKFlat → N.IsKFlat →
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

/-- Transport a verified core-monoidal model to the canonical comparison predicate.
The model supplies the counit and K-flat coordinate equations; the transport is the
standard descent argument through K-flat resolutions.
Source: Stacks, 079U; perfect.tex, 0DJA(1)
(blueprint: def-pc-derived-pullback-tensor-comparison-model-transport). -/
theorem exists_canonical_from_model {T X : Scheme.{uTC}} (g : T ⟶ X)
    (m : (derivedPullback g).CoreMonoidal)
    (hm : IsDerivedPullbackMonoidalModel g m) :
    ∃ τ : ∀ E K : schemeDerivedCategory X,
      (derivedPullback g).obj (E ⊗ K) ⟶
        (derivedPullback g).obj E ⊗ (derivedPullback g).obj K,
      IsCanonicalPullbackTensorComparison g τ := by
  sorry

/-- Existence of the canonical derived tensor comparison.
Proof: choose K-flat representatives of both inputs (lem-pc-kflat-resolution).
Their tensor and pullbacks are K-flat (lem-pc-kflat-tensor-product and
lem-pc-kflat-pullback-preservation), so the localization tensor maps and the
left-derived counits are invertible. Form the chain tensor isomorphism from
lem-weil-pbc-module-pullback-tensor on every summand; naturality makes it commute
with differentials. Transport it through the counits and localization tensor
maps to obtain τ. Comparisons between K-flat resolutions and the universal
left-derived property show independence of representatives, giving the displayed
equation for every P,N (lem-pc-derived-pullback-tensor-product).
Source: Stacks, 079U; perfect.tex, 0DJA(1)
(blueprint: def-pc-derived-pullback-tensor-comparison). -/
theorem exists_canonicalPullbackTensorComparison {T X : Scheme.{uTC}} (g : T ⟶ X) :
    ∃ τ : ∀ E K : schemeDerivedCategory X,
      (derivedPullback g).obj (E ⊗ K) ⟶
        (derivedPullback g).obj E ⊗ (derivedPullback g).obj K,
      IsCanonicalPullbackTensorComparison g τ := by
  obtain ⟨m, hm⟩ := exists_derivedPullbackMonoidalModel g
  exact exists_canonical_from_model g m hm

/-- The canonical derived tensor comparison is unique: two families satisfying the
characterising predicate agree.
Proof: on K-flat representatives P, N the counits at P and N and the localization
tensor map at the K-flat pullbacks are invertible, and the chain isomorphism is pinned
on every summand, so the coordinate equation determines the value at (Q P, Q N).
Every derived object is isomorphic to Q of a K-flat complex (lem-pc-kflat-resolution),
and naturality in both inputs transports the value along these isomorphisms.
Source: Stacks, 079U (blueprint: def-pc-derived-pullback-tensor-comparison). -/
theorem IsCanonicalPullbackTensorComparison.unique {T X : Scheme.{uTC}} {g : T ⟶ X}
    {τ τ' : ∀ E K : schemeDerivedCategory X,
      (derivedPullback g).obj (E ⊗ K) ⟶
        (derivedPullback g).obj E ⊗ (derivedPullback g).obj K}
    (h : IsCanonicalPullbackTensorComparison g τ)
    (h' : IsCanonicalPullbackTensorComparison g τ') : τ = τ' := by
  sorry

end AlgebraicGeometry
end
