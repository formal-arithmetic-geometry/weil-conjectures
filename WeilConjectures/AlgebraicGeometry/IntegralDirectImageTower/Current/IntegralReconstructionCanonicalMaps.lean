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
import WeilConjectures.CategoryTheory.AdjunctionReconstruction.AdjunctionReconstructionMate
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Canonical identities for the integral reconstruction maps

Source: integral direct-image proof (2), adjoint mates and finite projections.
(blueprint: lem-sp-integral-image-canonical-mates).
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

/-- Naturality of the specified proper scalar mate.
Source: blueprint proof (2), normalized scalar mates
(blueprint: lem-sp-integral-image-canonical-mates). -/
def properNat (s : Coefficients l E) (q : ScalarCompatibility l E s)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.lowerStar (spIntegralCondensed l E) f).rightDerivedFunctor ⋙
        derivedReduction l E s Y ⟶
      derivedReduction l E s X ⋙
        SpTowerShriek.push l E s.base (s.operations.geometry f) :=
  (mateEquiv
    (CondensedRing.derivedUpperStarLowerStarAdjunction (spIntegralCondensed l E) f)
    (SpTowerShriek.adjunction l E s.base (s.operations.geometry f))
    (TwoSquare.mk _ _ _ _ (q.pullback f).derived.inv)).natTrans

/-- The proper square has the specified component.
Source: blueprint proof (2), normalized scalar mates
(blueprint: lem-sp-integral-image-canonical-mates). -/
theorem properNat_app (s : Coefficients l E) (q : ScalarCompatibility l E s)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Integral l E X) :
    (properNat l E s q f).app M = properReduction l E s q f M := by
  simp [properNat, properReduction, mateEquiv, Adjunction.homEquiv_unit, Functor.map_comp]

/-- Naturality of the specified inverse open scalar mate.
Source: blueprint proof (2), normalized scalar mates
(blueprint: lem-sp-integral-image-canonical-mates). -/
def openNat (s : Coefficients l E) (q : ScalarCompatibility l E s)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    derivedReduction l E s U ⋙ (s.operations.openOp j).extension.mapDerivedCategory ⟶
      (CondensedRing.openImmersionLowerShriek (spIntegralCondensed l E) j).mapDerivedCategory ⋙
        derivedReduction l E s T :=
  ((mateEquiv
    ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (spIntegralCondensed l E) j).ofNatIsoRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (spIntegralCondensed l E) j).symm)
    (s.operations.openOp j).derivedAdjunction).symm
    (TwoSquare.mk _ _ _ _ (q.pullback j).derived.hom)).natTrans

/-- The inverse open square has the specified component.
Source: blueprint proof (2), normalized scalar mates
(blueprint: lem-sp-integral-image-canonical-mates). -/
theorem openNat_app (s : Coefficients l E) (q : ScalarCompatibility l E s)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (M : Integral l E U) :
    (openNat l E s q j).app M = openReductionInverse l E s q j M := by
  simp [openNat, openReductionInverse, mateEquiv, Adjunction.homEquiv_counit, Functor.map_comp]

/-- The composite proper/open scalar square.
Source: blueprint proof (2), normalized scalar mates
(blueprint: lem-sp-integral-image-canonical-mates). -/
def baseChangeNat (s : Coefficients l E) (q : ScalarCompatibility l E s)
    (hq : OpenScalarIsIso l E s q)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    shriek l E c ⋙ red l E s Y ⟶ red l E s X ⋙ towerShriek l E s c := by
  let τ := openNat l E s q c.i
  have hτ (M : Integral l E X) : IsIso (τ.app M) := by
    change IsIso ((openNat l E s q c.i).app M)
    rw [openNat_app]
    exact hq c.i M
  letI : ∀ M, IsIso (τ.app M) := hτ
  letI : IsIso τ := NatIso.isIso_of_isIso_app _
  exact Functor.whiskerLeft (shriek l E c ⋙ red l E s Y)
      (realization l E s Y).unitIso.hom ≫
    Functor.whiskerRight
      (Functor.whiskerLeft
          (CondensedRing.openImmersionLowerShriek
            (spIntegralCondensed l E) c.i).mapDerivedCategory (properNat l E s q c.g) ≫
        Functor.whiskerRight (inv τ)
          (SpTowerShriek.push l E s.base (s.operations.geometry c.g)))
      (realization l E s Y).inverse

/-- The composite square has the specified base-change component.
Source: blueprint proof (2), normalized scalar mates
(blueprint: lem-sp-integral-image-canonical-mates). -/
theorem baseChangeNat_app (s : Coefficients l E)
    (q : ScalarCompatibility l E s) (hq : OpenScalarIsIso l E s q)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (M : Integral l E X) :
    (baseChangeNat l E s q hq c).app M = towerBaseChange l E s q hq c M := by
  simp [baseChangeNat, towerBaseChange, properNat_app, openNat_app, Functor.map_comp, red]

/-- Naturality of the proper/open mate, before any constructibility restriction.
Source: blueprint proof (2), mates of normalized scalar comparisons.
(blueprint: lem-sp-integral-image-canonical-mates). -/
theorem towerBaseChange_naturality (s : Coefficients l E)
    (q : ScalarCompatibility l E s) (hq : OpenScalarIsIso l E s q)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {M N : Integral l E X} (v : M ⟶ N) :
    (red l E s Y).map ((shriek l E c).map v) ≫ towerBaseChange l E s q hq c N =
      towerBaseChange l E s q hq c M ≫
        (towerShriek l E s c).map ((red l E s X).map v) := by
  simpa only [Functor.comp_map, baseChangeNat_app] using
    (baseChangeNat l E s q hq c).naturality v

private theorem rightMate_app (s : Coefficients l E) (q : ScalarCompatibility l E s)
    (hq : OpenScalarIsIso l E s q) (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (C : spDerivedCoefficientTowers l E X (s.towers X)) :
    (AdjunctionReconstruction.rightMate _ _ _ _
      (adjunction l E s A X) (adjunction l E s A Y)
      (baseChangeNat l E s q hq c)).app C = limitComparison l E s q hq A c C := by
  simp only [AdjunctionReconstruction.rightMate, baseChangeNat_app, limitComparison]

/-- Reconstruction is the adjoint transpose of the original whole-tower scalar map.
Proof: naturality of the output unit moves the input unit across the right mate;
the input adjunction triangle cancels its counit. Source: blueprint proof (2).
(blueprint: lem-sp-integral-image-canonical-mates). -/
theorem reconstruction_eq_transpose (s : Coefficients l E)
    (q : ScalarCompatibility l E s) (hq : OpenScalarIsIso l E s q)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (M : Integral l E X) :
    reconstruction l E s q hq A c M =
      (adjunction l E s A Y).unit.app ((shriek l E c).obj M) ≫
        (limit l E s A Y).map (towerBaseChange l E s q hq c M) := by
  simpa only [rightMate_app, baseChangeNat_app, reconstruction] using
    AdjunctionReconstruction.reconstruction_eq _ _ _ _
      (adjunction l E s A X) (adjunction l E s A Y)
      (baseChangeNat l E s q hq c) M

/-- Transposing reconstruction returns the specified proper/open mate itself.
Source: blueprint proof (2); the second adjunction triangle.
(blueprint: lem-sp-integral-image-canonical-mates). -/
theorem towerComparison_eq_baseChange (s : Coefficients l E)
    (q : ScalarCompatibility l E s) (hq : OpenScalarIsIso l E s q)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (M : Integral l E X) :
    towerComparison l E s q hq A c M = towerBaseChange l E s q hq c M := by
  unfold towerComparison
  rw [reconstruction_eq_transpose]
  exact ((adjunction l E s A Y).homEquiv _ _).symm_apply_apply
    (towerBaseChange l E s q hq c M)

/-- Naturality of reconstruction follows from naturality of the unit and scalar mate.
Source: blueprint proof (2). (blueprint: lem-sp-integral-image-canonical-mates). -/
theorem reconstruction_naturality (s : Coefficients l E)
    (q : ScalarCompatibility l E s) (hq : OpenScalarIsIso l E s q)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {M N : Integral l E X} (v : M ⟶ N) :
    (shriek l E c).map v ≫ reconstruction l E s q hq A c N =
      reconstruction l E s q hq A c M ≫
        (limit l E s A Y).map ((towerShriek l E s c).map ((red l E s X).map v)) := by
  simpa only [rightMate_app, reconstruction] using
    AdjunctionReconstruction.reconstruction_naturality _ _ _ _
      (adjunction l E s A X) (adjunction l E s A Y)
      (baseChangeNat l E s q hq c) v

/-- Naturality of the actual tower transpose, as a whole-tower equality.
Source: blueprint proof (2). (blueprint: lem-sp-integral-image-canonical-mates). -/
theorem towerComparison_naturality (s : Coefficients l E)
    (q : ScalarCompatibility l E s) (hq : OpenScalarIsIso l E s q)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {M N : Integral l E X} (v : M ⟶ N) :
    (red l E s Y).map ((shriek l E c).map v) ≫ towerComparison l E s q hq A c N =
      towerComparison l E s q hq A c M ≫
        (towerShriek l E s c).map ((red l E s X).map v) := by
  simp only [towerComparison_eq_baseChange]
  exact towerBaseChange_naturality l E s q hq c v

private def finiteBaseChangeNat (s : Coefficients l E)
    (q : ScalarCompatibility l E s) (hq : OpenScalarIsIso l E s q)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :
    shriek l E c ⋙ level l E s Y n ⟶ level l E s X n ⋙ finiteShriek l E s c n :=
  Functor.whiskerRight (baseChangeNat l E s q hq c)
      (spDerivedCoefficientEvaluation l E Y (s.towers Y) n) ≫
    Functor.whiskerLeft (red l E s X) (finiteComparison l E s q.evaluation c n).hom

private theorem finiteBaseChangeNat_app (s : Coefficients l E)
    (q : ScalarCompatibility l E s) (hq : OpenScalarIsIso l E s q)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ)
    (M : Integral l E X) :
    (finiteBaseChangeNat l E s q hq c n).app M = finiteBaseChange l E s q hq c M n := by
  simp only [finiteBaseChangeNat, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, baseChangeNat_app, finiteBaseChange]

/-- Evaluating the actual tower transpose gives the specified finite scalar map.
Source: blueprint proof (2). (blueprint: lem-sp-integral-image-canonical-mates). -/
theorem towerComparison_evaluation (s : Coefficients l E)
    (q : ScalarCompatibility l E s) (hq : OpenScalarIsIso l E s q)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Integral l E X) (n : ℕ) :
    (spDerivedCoefficientEvaluation l E Y (s.towers Y) n).map
        (towerComparison l E s q hq A c M) ≫
      (finiteComparison l E s q.evaluation c n).hom.app ((red l E s X).obj M) =
        finiteBaseChange l E s q hq c M n := by
  rw [towerComparison_eq_baseChange]
  rfl

private theorem finiteRightMate_app (s : Coefficients l E)
    (q : ScalarCompatibility l E s) (hq : OpenScalarIsIso l E s q)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ)
    (N : Scheme.proEtaleDerivedCategory X (SpTowerShriek.R l E n)) :
    (AdjunctionReconstruction.rightMate _ _ _ _
      (finiteAdjunction l E s X n) (finiteAdjunction l E s Y n)
      (finiteBaseChangeNat l E s q hq c n)).app N =
      finiteRestrictionComparison l E s q hq c n N := by
  simp only [AdjunctionReconstruction.rightMate, finiteBaseChangeNat_app,
    finiteRestrictionComparison]

/-- Every finite projection of reconstruction is the right mate of finite base change.
Proof: transpose the evaluated counit and apply the input triangle identity, then
use naturality of the finite adjunction hom-equivalence in its target.
Source: blueprint proof (2). (blueprint: lem-sp-integral-image-canonical-mates). -/
theorem reconstruction_projection (s : Coefficients l E)
    (q : ScalarCompatibility l E s) (hq : OpenScalarIsIso l E s q)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Integral l E X) (n : ℕ) :
    reconstruction l E s q hq A c M ≫
        projection l E s A Y (imageTower l E s c M) n ≫
        (finiteRestriction l E s Y n).map
          ((finiteComparison l E s q.evaluation c n).hom.app ((red l E s X).obj M)) =
      (shriek l E c).map ((finiteAdjunction l E s X n).unit.app M) ≫
        finiteRestrictionComparison l E s q hq c n ((level l E s X n).obj M) := by
  have hr := AdjunctionReconstruction.reconstruction_eq _ _ _ _
    (finiteAdjunction l E s X n) (finiteAdjunction l E s Y n)
    (finiteBaseChangeNat l E s q hq c n) M
  simp only [finiteRightMate_app, finiteBaseChangeNat_app] at hr
  rw [hr, reconstruction_eq_transpose]
  have hp := AdjunctionReconstruction.projection_transpose _ _
    (adjunction l E s A Y)
    (spDerivedCoefficientEvaluation l E Y (s.towers Y) n)
    (finiteRestriction l E s Y n) (finiteAdjunction l E s Y n)
    (towerBaseChange l E s q hq c M)
  change ((adjunction l E s A Y).homEquiv _ _ (towerBaseChange l E s q hq c M)) ≫
    (projection l E s A Y (imageTower l E s c M) n ≫ _) = _
  rw [← Category.assoc]
  change (((adjunction l E s A Y).homEquiv _ _ (towerBaseChange l E s q hq c M)) ≫
    (finiteAdjunction l E s Y n).homEquiv _ _
      ((spDerivedCoefficientEvaluation l E Y (s.towers Y) n).map
        ((adjunction l E s A Y).counit.app (imageTower l E s c M)))) ≫ _ = _
  rw [hp, ← Adjunction.homEquiv_naturality_right]
  rfl

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
