/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormulaCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerCurrentStatement
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Proper/open factorization of the current limit mate

Source: blueprint integral direct-image proof (2).
(blueprint: lem-sp-current-limit-factorization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Proper pushforward in the recorded coefficient-tower coordinates.
Source: blueprint proof (2) (blueprint: lem-sp-current-limit-factorization). -/
def nativeProper (s : Coefficients l E) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (realization l E s X).functor ⋙
    SpTowerShriek.push l E s.base (s.operations.geometry f) ⋙
      (realization l E s Y).inverse

/-- Open extension in the recorded coefficient-tower coordinates.
Source: blueprint proof (2) (blueprint: lem-sp-current-limit-factorization). -/
def nativeOpen (s : Coefficients l E) {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] :=
  (realization l E s U).functor ⋙ (s.operations.openOp j).extension.mapDerivedCategory ⋙
    (realization l E s T).inverse

/-- The specified proper scalar mate in coefficient-tower coordinates.
Source: blueprint proof (2) (blueprint: lem-sp-current-limit-factorization). -/
def nativeProperScalar (s : Coefficients l E) (q : ScalarCompatibility l E s)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.lowerStar (spIntegralCondensed l E) f).rightDerivedFunctor ⋙
      red l E s Y ⟶ red l E s X ⋙ nativeProper l E s f :=
  Functor.whiskerLeft
      ((CondensedRing.lowerStar (spIntegralCondensed l E) f).rightDerivedFunctor ⋙
        red l E s Y) (realization l E s Y).unitIso.hom ≫
    Functor.whiskerRight (properNat l E s q f) (realization l E s Y).inverse

/-- The inverse specified open scalar mate in coefficient-tower coordinates.
Source: blueprint proof (2) (blueprint: lem-sp-current-limit-factorization). -/
def nativeOpenScalar (s : Coefficients l E) (q : ScalarCompatibility l E s)
    (hq : OpenScalarIsIso l E s q) {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    (CondensedRing.openImmersionLowerShriek (spIntegralCondensed l E) j).mapDerivedCategory ⋙
      red l E s T ⟶ red l E s U ⋙ nativeOpen l E s j := by
  let τ := openNat l E s q j
  have hτ (M : Integral l E U) : IsIso (τ.app M) := by
    change IsIso ((openNat l E s q j).app M)
    rw [openNat_app]
    exact hq j M
  letI : ∀ M, IsIso (τ.app M) := hτ
  letI : IsIso τ := NatIso.isIso_of_isIso_app _
  exact Functor.whiskerLeft
      ((CondensedRing.openImmersionLowerShriek (spIntegralCondensed l E) j).mapDerivedCategory ⋙
        red l E s T) (realization l E s T).unitIso.hom ≫
    Functor.whiskerRight (inv τ) (realization l E s T).inverse

/-- The intermediate realization cancels between the proper and open factors.
Source: blueprint proof (2) (blueprint: lem-sp-current-limit-factorization). -/
def nativeFactorsIso (s : Coefficients l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    nativeOpen l E s c.i ⋙ nativeProper l E s c.g ≅ towerShriek l E s c :=
  NatIso.ofComponents
    (fun C ↦ (realization l E s Y).inverse.mapIso
      ((SpTowerShriek.push l E s.base (s.operations.geometry c.g)).mapIso
        ((realization l E s c.Z).counitIso.app
          ((s.operations.openOp c.i).extension.mapDerivedCategory.obj
            ((realization l E s X).functor.obj C)))))
    (by
      intro C D v
      dsimp only [nativeOpen, nativeProper, towerShriek, Functor.comp_map, Functor.comp_obj,
        Functor.mapIso_hom]
      simpa only [Functor.comp_map, Functor.id_map, Functor.map_comp, Iso.app_hom,
        SpTowerShriek.openD] using
        congrArg (fun v ↦ (realization l E s Y).inverse.map
          ((SpTowerShriek.push l E s.base (s.operations.geometry c.g)).map v))
          ((realization l E s c.Z).counitIso.hom.naturality
            ((s.operations.openOp c.i).extension.mapDerivedCategory.map
              ((realization l E s X).functor.map v))))

/-- Proper/limit mate, with the original scalar comparison and completion adjunction.
Source: blueprint proof (2) (blueprint: lem-sp-current-limit-factorization). -/
def properLimitMate (s : Coefficients l E) (q : ScalarCompatibility l E s)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  AdjunctionReconstruction.rightMate _ _ _ _
    (adjunction l E s A X) (adjunction l E s A Y) (nativeProperScalar l E s q f)

/-- Open/limit mate, with the original scalar comparison and completion adjunction.
Source: blueprint proof (2) (blueprint: lem-sp-current-limit-factorization). -/
def openLimitMate (s : Coefficients l E) (q : ScalarCompatibility l E s)
    (hq : OpenScalarIsIso l E s q) (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :=
  AdjunctionReconstruction.rightMate _ _ _ _
    (adjunction l E s A U) (adjunction l E s A T) (nativeOpenScalar l E s q hq j)

/-- The scalar square for compact support is the pasted open and proper square.
Proof: naturality of the intermediate realization counit moves the inverse open
mate across it; the realization triangle cancels the intermediate unit.
Source: blueprint proof (2) (blueprint: lem-sp-current-limit-factorization). -/
theorem nativeScalar_pasting (s : Coefficients l E) (q : ScalarCompatibility l E s)
    (hq : OpenScalarIsIso l E s q)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Functor.whiskerLeft
        (CondensedRing.openImmersionLowerShriek (spIntegralCondensed l E) c.i).mapDerivedCategory
        (nativeProperScalar l E s q c.g) ≫
      Functor.whiskerRight (nativeOpenScalar l E s q hq c.i) (nativeProper l E s c.g) ≫
      Functor.whiskerLeft (red l E s X) (nativeFactorsIso l E s c).hom =
        baseChangeNat l E s q hq c := by
  have hτ (N : Integral l E X) : IsIso ((openNat l E s q c.i).app N) := by
    rw [openNat_app]
    exact hq c.i N
  let : ∀ N, IsIso ((openNat l E s q c.i).app N) := hτ
  let : IsIso (openNat l E s q c.i) := NatIso.isIso_of_isIso_app _
  ext M
  dsimp only [nativeProperScalar, nativeOpenScalar, nativeProper, nativeFactorsIso,
    baseChangeNat, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatIso.ofComponents_hom_app, Functor.mapIso_hom, Functor.comp_map, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp]
  congr 1
  apply congrArg (fun v ↦ (realization l E s Y).inverse.map
    ((properNat l E s q c.g).app
      ((CondensedRing.openImmersionLowerShriek
        (spIntegralCondensed l E) c.i).mapDerivedCategory.obj M) ≫
      (SpTowerShriek.push l E s.base (s.operations.geometry c.g)).map v))
  have hc := (realization l E s c.Z).counitIso.hom.naturality
    ((inv (openNat l E s q c.i)).app M)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, derivedReduction] at hc
  simp only [Iso.app_hom]
  rw [hc, ← Category.assoc, (realization l E s c.Z).functor_unitIso_comp]
  simp

/-- The whole compact-support/limit mate is the ordered composite of its factors.
Proof: apply pasting for right mates and then carry the cancellation isomorphism
through the right adjoint. Source: blueprint proof (2).
(blueprint: lem-sp-current-limit-factorization). -/
theorem limitComparison_factorization (s : Coefficients l E)
    (q : ScalarCompatibility l E s) (hq : OpenScalarIsIso l E s q)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (C : spDerivedCoefficientTowers l E X (s.towers X)) :
    limitComparison l E s q hq A c C =
      (CondensedRing.lowerStar (spIntegralCondensed l E) c.g).rightDerivedFunctor.map
          ((openLimitMate l E s q hq A c.i).app C) ≫
        (properLimitMate l E s q A c.g).app ((nativeOpen l E s c.i).obj C) ≫
          (limit l E s A Y).map ((nativeFactorsIso l E s c).hom.app C) := by
  let β : shriek l E c ⋙ red l E s Y ⟶
      red l E s X ⋙ (nativeOpen l E s c.i ⋙ nativeProper l E s c.g) :=
    Functor.whiskerLeft
        (CondensedRing.openImmersionLowerShriek
          (spIntegralCondensed l E) c.i).mapDerivedCategory
        (nativeProperScalar l E s q c.g) ≫
      Functor.whiskerRight (nativeOpenScalar l E s q hq c.i) (nativeProper l E s c.g)
  have hp := AdjunctionReconstruction.rightMate_postcompose
    (red l E s X) (limit l E s A X) (red l E s Y) (limit l E s A Y)
    (adjunction l E s A X) (adjunction l E s A Y) β
    (nativeFactorsIso l E s c).hom C
  have hs := AdjunctionReconstruction.rightMate_pasting
    (red l E s X) (limit l E s A X) (red l E s c.Z) (limit l E s A c.Z)
    (adjunction l E s A X) (adjunction l E s A c.Z)
    (red l E s Y) (limit l E s A Y) (adjunction l E s A Y)
    (nativeOpenScalar l E s q hq c.i) (nativeProperScalar l E s q c.g) C
  have heq : β ≫ Functor.whiskerLeft (red l E s X)
      (nativeFactorsIso l E s c).hom = baseChangeNat l E s q hq c := by
    simpa only [β, Category.assoc] using nativeScalar_pasting l E s q hq c
  rw [heq] at hp
  have hs' : (AdjunctionReconstruction.rightMate _ _ _ _
      (adjunction l E s A X) (adjunction l E s A Y) β).app C = _ := hs
  rw [hs'] at hp
  simpa only [properLimitMate, openLimitMate, limitComparison,
    AdjunctionReconstruction.rightMate, baseChangeNat_app, Category.assoc] using hp


end AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
