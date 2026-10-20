/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q96
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound
import Sheaf.AlgebraicGeometry.StrictHenselization
import WeilConjectures.AlgebraicGeometry.UniversalHomeomorphismInvariance
import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
import Sheaf.Paper.NearbyGeometricSlice
import Sheaf.Paper.OrientedNearbyCycles
import Sheaf.Paper.OrientedNearbyStrictLocalDescription
import Sheaf.Paper.PsiGoodOrientedCohomologyStrata
import Sheaf.Paper.TraitNearbyBaseChange
import Sheaf.RingTheory.EtaleHenselianRingLift
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison

/-!
# Standard nearby-cycle constructibility and vanishing

Source: Luc Illusie, *Grothendieck and vanishing cycles*, Ann. Fac. Sci. Toulouse
30 (2021), §1.1, formula (1.2), and §1.2, last paragraph, printed pp. 85--86
(blueprint: lem-trf-nearby-cycle-sheaf-finiteness).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The canonical projection from the geometric generic fibre to the generic fibre.

Source: Illusie, *Grothendieck and vanishing cycles*, §1.1, formula (1.2)
(blueprint: lem-trf-nearby-cycle-sheaf-finiteness). -/
noncomputable def nearbyCycleProjection
    (R K Kbar : Type u) [CommRing R] [Field K] [Field Kbar]
    [Algebra R K] [Algebra K Kbar] [Algebra R Kbar]
    [IsScalarTower R K Kbar]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of R)) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  pullback.map f (Spec.map (CommRingCat.ofHom (algebraMap R Kbar)))
    f (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) (𝟙 _)
    (by simp)
    (by
      simp only [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [IsScalarTower.algebraMap_eq R K Kbar])

/-- For a strictly henselian discrete valuation ring and a finite torsion coefficient ring,
nearby-cycle cohomology sheaves of a constructible sheaf on the generic fibre are
constructible on the closed fibre and vanish in all sufficiently large degrees.

Source: Luc Illusie, *Grothendieck and vanishing cycles*, Ann. Fac. Sci. Toulouse
30 (2021), §1.1, formula (1.2), and §1.2, last paragraph, printed pp. 85--86
(blueprint: lem-trf-nearby-cycle-sheaf-finiteness).
Proof: (1) Use the DVR unit-times-uniformizer description and affine finite-type facts
for the finite-presentation setting. (2) Extend the constructible sheaf by zero to the
total scheme. (3) Apply the trait nearby-base-change and oriented cohomology-stratification
inputs. (4) Identify the geometric slice with ordinary nearby cycles and descend finite
local constancy. (5) Apply the uniform strict-local torsion bound and joint conservativity
for one global vanishing bound. (6) Use exactness of inverse image to identify the displayed
cohomology sheaves with the stated `i^* R^q j_*` objects. -/
theorem nearbyCycleSheafFiniteness
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsDomain R]
    [IsStrictlyHenselianLocalRing R]
    (hDimension : ringKrullDim R = 1)
    (hPrincipal : (IsLocalRing.maximalIdeal R).IsPrincipal)
    (hMaximalNe : IsLocalRing.maximalIdeal R ≠ ⊥)
    (X : Scheme.{u})
    (f : X ⟶ Spec (.of R))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (ell : ℕ) [Fact ell.Prime] [Invertible (ell : R)]
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : ∀ a : Λ, (ell : Λ) ^ n * a = 0)
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Kbar : Type u) [Field Kbar] [Algebra K Kbar] [Algebra R Kbar]
    [IsSepClosure K Kbar] [IsScalarTower R K Kbar]
    (F : Sheaf
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    (∀ q : ℤ, 0 ≤ q →
      Scheme.IsConstructibleEtaleModuleSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f
            (Spec.map (CommRingCat.ofHom
              (algebraMap R (IsLocalRing.ResidueField R)))))).obj
          (Etale.higherDirectImage Λ
            (pullback.fst f
              (Spec.map (CommRingCat.ofHom (algebraMap R Kbar)))) q
            ((Etale.upperStar (ModuleCat.{u + 1} Λ)
              (nearbyCycleProjection R K Kbar X f)).obj F)))) ∧
    (∃ N : ℤ, ∀ q : ℤ, N < q →
      IsZero
        ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f
            (Spec.map (CommRingCat.ofHom
              (algebraMap R (IsLocalRing.ResidueField R)))))).obj
          (Etale.higherDirectImage Λ
            (pullback.fst f
              (Spec.map (CommRingCat.ofHom (algebraMap R Kbar)))) q
            ((Etale.upperStar (ModuleCat.{u + 1} Λ)
              (nearbyCycleProjection R K Kbar X f)).obj F)))) := by
  sorry

end AlgebraicGeometry
