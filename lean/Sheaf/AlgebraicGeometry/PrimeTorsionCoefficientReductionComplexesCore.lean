/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReductionPullbacks
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!
# Degree zero complexes and localization

Source: Stacks Project, Tags 03EK, 06YU and 0F1J
(blueprint: def-kun-prime-coefficient-complexes).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
/-- The chosen degree-zero complex; its image under Q is primeSingle.
Source: Stacks, Tag 06YU (blueprint: def-kun-prime-coefficient-complexes). -/
def primeSingleComplex (Λ : Type (u + 1)) [CommRing Λ] (V : Scheme.{u})
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ :=
  (CochainComplex.singleFunctor _ 0).obj M

/-- Termwise scalar restriction on complexes, using the recorded exact functor.
Source: Stacks, Tag 0D6J (blueprint: def-kun-prime-coefficient-complexes). -/
def primeRestrictedComplex (φ : A →+* B) (V : Scheme.{u})
    (C : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ) :=
  (Sheaf.restrictScalars V.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ) |>.obj C

/-- Localization into the recorded derived category, fixing its Hom universe.
Source: Stacks, Tag 06YU (blueprint: def-kun-prime-coefficient-complexes). -/
def primeLocalization (Λ : Type (u + 1)) [CommRing Λ] (V : Scheme.{u}) :
    CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ ⥤
      DerivedCategoryModule Λ V :=
  _root_.DerivedCategory.Q

/-- Monoidality of sheafification for the coefficient sheaves.
Source: Stacks, Tag 03EK
(blueprint: def-kun-prime-coefficient-complexes). -/
instance primeSheafMonoidalW (Λ : Type (u + 1)) [CommRing Λ] (V : Scheme.{u}) :
    (V.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  GrothendieckTopology.W.monoidal

/-- The recorded canonical lax monoidal localization, exposed at the fixed
coefficient universes. Source: Stacks, Tag 06YU
(blueprint: def-kun-prime-coefficient-complexes). -/
instance primeLocalizationLaxMonoidal (Λ : Type (u + 1)) [CommRing Λ] (V : Scheme.{u}) :
    (primeLocalization Λ V).LaxMonoidal :=
  laxMonoidal_Q (ModuleCat.{u + 1} Λ) V

/-- The canonical localization factorization of exact termwise scalar restriction.
Source: Stacks, Tag 0D6J
(blueprint: def-kun-prime-coefficient-complexes). -/
def primeRestrictionFactors (φ : A →+* B) (V : Scheme.{u}) :
    primeLocalization B V ⋙ Sheaf.derivedRestrictScalars V.smallEtaleTopology φ ≅
      (Sheaf.restrictScalars V.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ) ⋙
        primeLocalization A V :=
  (Sheaf.restrictScalars V.smallEtaleTopology φ).mapDerivedCategoryFactors.{u + 1, u + 1}



end AlgebraicGeometry.Etale
