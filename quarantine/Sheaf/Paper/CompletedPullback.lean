/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.FourCorners
public import Sheaf.Paper.CompletedRlimFunctor
public import Sheaf.Paper.IntrinsicCompletion
public import Sheaf.Paper.CompletedTowerPullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Sheaf.Paper.CompletedKoszulQuotientComparison

/-!
# Completed pullback through strict completed-coefficient towers

Source: blueprint proper base change, completed pullback; Stacks Tag 099N
(blueprint: def-weil-pbc-completed-pullback).

## Main definitions

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedPull`:
  the recorded construction or statement of this node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The ordinary constant strict tower functor.
Source: blueprint completed pullback (blueprint: def-weil-pbc-completed-pullback). -/
abbrev AdicCoefficientDatum.constantTower (T : Scheme.{t}) :
    reductionModules T (d.completedRing T) ⥤ d.towers T := Functor.const ℕᵒᵖ

/-- Exact constant towers on the derived category.
Source: blueprint completed pullback (blueprint: def-weil-pbc-completed-pullback). -/
abbrev AdicCoefficientDatum.derivedConstantTower (T : Scheme.{t}) :=
  (d.constantTower T).mapDerivedCategory

/-- Constant towers are left adjoint to the chosen total right derived inverse limit.
Source: blueprint completed pullback; Stacks 079P
(blueprint: def-weil-pbc-completed-pullback). -/
def AdicCoefficientDatum.constantRlimAdjunction (T : Scheme.{t}) :
    d.derivedConstantTower T ⊣ completedRlim T (d.completedRing T) :=
  (constLimAdj :
    d.constantTower T ⊣ completedTowerLimit T (d.completedRing T)
  ).mapDerivedCategoryRightDerivedAdjunction

/-- Reuse the published derived quotient unit, including its K-flat normalization.
Source: blueprint completed pullback; Stacks 06YY and 099N
(blueprint: def-weil-pbc-completed-pullback). -/
abbrev completedReductionAugmentation (T : Scheme.{t}) :
    d.derivedConstantTower T ⟶ completedReductionTower T d :=
  completedReductionTowerUnit d T

/-- The canonical completion unit, formed by the constant-tower adjunction and quotient map.
Source: blueprint completed pullback (blueprint: def-weil-pbc-completed-pullback). -/
def AdicCoefficientDatum.completionUnit (T : Scheme.{t}) (K : d.derived T) :
    K ⟶ (completedRlim T (d.completedRing T)).obj
      ((completedReductionTower T d).obj K) :=
  (d.constantRlimAdjunction T).unit.app K ≫
    (completedRlim T (d.completedRing T)).map ((completedReductionAugmentation d T).app K)

/-- Quotient-tower completeness is invertibility of the specified canonical completion unit.
This is the completeness condition in the completed base-change construction.
Source: blueprint completed base-change map, input paragraph and canonical quotient unit
(blueprint: def-weil-pbc-completed-pullback). -/
def AdicCoefficientDatum.TowerComplete (T : Scheme.{t}) (K : d.derived T) : Prop :=
  IsIso (d.completionUnit T K)

/-- The quotient-tower unit and the intrinsic Koszul unit give the same complete inputs.
Source: blueprint completed pullback, last paragraph and its constant-completion comparison
(blueprint: def-weil-pbc-completed-pullback).
Proof: restrict along the constant-to-completed coefficient map. The finite quotient
comparisons commute with all quotient transitions and with the quotient augmentation.
Restriction preserves the specified strict derived limits. The Noetherian Koszul-to-
quotient comparison identifies the completion objects and their units; it also commutes
with scalar restriction. The constant-completion equivalence reflects invertibility,
so the quotient unit is invertible exactly when every generating-list Koszul unit is.
Finite generation supplies generating lists, and change of generators preserves this
unit condition. This is a comparison of the two specified units, not their definition. -/
theorem AdicCoefficientDatum.towerComplete_iff_intrinsic (T : Scheme.{t})
    (K : d.derived T) :
    d.TowerComplete T K ↔
      ∀ (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal),
        ∀ (C : CochainComplex (reductionModules T (d.completedRing T)) ℤ)
          (e : DerivedCategory.Q.obj C ≅ K),
          IsDerivedCompleteIntrinsic T d r a ha K C e := by
  classical
  have hcomparison (r : ℕ) (a : Fin r → A)
      (ha : Ideal.span (Set.range a) = d.ideal)
      (C : CochainComplex (reductionModules T (d.completedRing T)) ℤ)
      (e : DerivedCategory.Q.obj C ≅ K) :
      IsDerivedCompleteIntrinsic T d r a ha K C e ↔ d.TowerComplete T K := by
    obtain ⟨c, hc⟩ := completedKoszulQuotientComparison T d r a ha K C e
    change IsIso (intrinsicCompletionUnit T d r a ha K C e) ↔ IsIso (d.completionUnit T K)
    change intrinsicCompletionUnit T d r a ha K C e ≫ c.hom = d.completionUnit T K at hc
    rw [← hc]
    exact (isIso_comp_right_iff _ c.hom).symm
  constructor
  · intro h r a ha C e
    exact (hcomparison r a ha C e).mpr h
  · intro h
    obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
    exact (hcomparison r a ha (DerivedCategory.Q.objPreimage K)
      (DerivedCategory.Q.objObjPreimageIso K)).mp
        (h r a ha _ _)

/-- Apply actual module pullback to every level and transition of a strict tower.
Source: blueprint completed pullback (blueprint: def-weil-pbc-completed-pullback). -/
abbrev AdicCoefficientDatum.towerModulePull {U V : Scheme.{t}} (f : U ⟶ V) :
    d.towers V ⥤ d.towers U :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U) (d.integralRingIso f))

/-- Tower pullback is exact: the canonical profinite coefficient map is invertible and
module inverse image is exact; exactness of strict towers is evaluated levelwise.
Source: blueprint completed pullback (blueprint: def-weil-pbc-completed-pullback).
Proof: evaluation commutes with this whiskering functor. Use exactness of ordinary
ringed pullback at every level and the pointwise kernels and cokernels of towers. -/
theorem AdicCoefficientDatum.towerModulePull_exact {U V : Scheme.{t}} (f : U ⟶ V) :
    PreservesFiniteLimits (d.towerModulePull f) ∧
      PreservesFiniteColimits (d.towerModulePull f) := by
  unfold AdicCoefficientDatum.towerModulePull
  constructor
  · exact ⟨fun J _ _ ↦ inferInstance⟩
  · exact ⟨fun J _ _ ↦ inferInstance⟩

/-- Exact tower pullback preserves finite limits.
Source: blueprint completed pullback (blueprint: def-weil-pbc-completed-pullback). -/
instance AdicCoefficientDatum.towerModulePull_finiteLimits {U V : Scheme.{t}} (f : U ⟶ V) :
    PreservesFiniteLimits (d.towerModulePull f) := (d.towerModulePull_exact f).1
/-- Exact tower pullback preserves finite colimits.
Source: blueprint completed pullback (blueprint: def-weil-pbc-completed-pullback). -/
instance AdicCoefficientDatum.towerModulePull_finiteColimits {U V : Scheme.{t}} (f : U ⟶ V) :
    PreservesFiniteColimits (d.towerModulePull f) := (d.towerModulePull_exact f).2

/-- Termwise pullback of strict towers is additive, evaluated at every level.
Source: blueprint completed pullback (blueprint: def-weil-pbc-completed-pullback). -/
instance AdicCoefficientDatum.towerModulePull_additive {U V : Scheme.{t}} (f : U ⟶ V) :
    (d.towerModulePull f).Additive := inferInstance

/-- The total left derived tower pullback, here computed by the exact termwise functor.
Source: blueprint completed pullback (blueprint: def-weil-pbc-completed-pullback). -/
abbrev AdicCoefficientDatum.towerPull {U V : Scheme.{t}} (f : U ⟶ V) :=
  (d.towerModulePull f).mapDerivedCategory

/-- Completed pullback is precisely Rlim of tower pullback of the strict reduction tower.
The formula extends to ambient inputs; its restriction is the completed pullback of the node.
Source: blueprint completed pullback; Stacks 099N
(blueprint: def-weil-pbc-completed-pullback). -/
def AdicCoefficientDatum.completedPull {U V : Scheme.{t}} (f : U ⟶ V) :
    d.derived V ⥤ d.derived U :=
  completedReductionTower V d ⋙ d.towerPull f ⋙ completedRlim U (d.completedRing U)

/-- Constant towers commute with actual ordinary pullback, with identity components.
Source: blueprint direct image and limits (blueprint: def-weil-pbc-completed-pullback). -/
def AdicCoefficientDatum.constantPullbackIso {U V : Scheme.{t}} (f : U ⟶ V) :
    d.constantTower V ⋙ d.towerModulePull f ≅
      proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f) ⋙ d.constantTower U :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents
      (fun n ↦ Iso.refl
        (((d.towerModulePull f).obj ((d.constantTower V).obj M)).obj n))
      (fun _ ↦ by
        ext n
        simp [AdicCoefficientDatum.constantTower, AdicCoefficientDatum.towerModulePull]))
    (fun _ ↦ by
      ext n
      simp [AdicCoefficientDatum.constantTower, AdicCoefficientDatum.towerModulePull])

/-- The exact derived constant/pullback comparison, induced from identity components.
Source: blueprint direct image and limits (blueprint: def-weil-pbc-completed-pullback). -/
def AdicCoefficientDatum.derivedConstantPullbackIso {U V : Scheme.{t}} (f : U ⟶ V) :
    d.derivedConstantTower V ⋙ d.towerPull f ≅ d.pull f ⋙ d.derivedConstantTower U :=
  (Functor.mapDerivedCategoryCompIso (d.constantTower V) (d.towerModulePull f)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (d.constantPullbackIso f) ≪≫
      Functor.mapDerivedCategoryCompIso
        (proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
          (d.integralRingIso f)) (d.constantTower U)


/-- The canonical ordinary-to-completed comparison: constant-tower unit followed by
the image of the actual strict quotient augmentation.
Source: blueprint coherence, proof step 5; completed pullback, comparison paragraph
(blueprint: def-weil-pbc-completed-pullback). -/
def AdicCoefficientDatum.ordinaryToCompleted {U V : Scheme.{t}} (g : U ⟶ V)
    (K : d.derived V) : (d.pull g).obj K ⟶ (d.completedPull g).obj K :=
  (d.constantRlimAdjunction U).unit.app ((d.pull g).obj K) ≫
    (completedRlim U (d.completedRing U)).map
      ((d.derivedConstantPullbackIso g).inv.app K ≫
        (d.towerPull g).map ((completedReductionAugmentation d V).app K))


end AlgebraicGeometry.Scheme
