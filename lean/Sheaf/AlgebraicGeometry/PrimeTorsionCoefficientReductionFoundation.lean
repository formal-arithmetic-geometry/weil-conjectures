/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!
# Canonical quotient coefficient tensor arrow

Source: Stacks Project, Tags 03EK, 06YU and 0F1J
(blueprint: def-kun-prime-coefficient-constructions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The quotient coefficient homomorphism, with the common size lift used for étale sheaves.
Source: Stacks, Tag 0F1J (blueprint: def-kun-prime-coefficient-constructions). -/
def primeCoefficientHom (n ell : ℕ) (hd : ell ∣ n) :
    ULift.{u + 1} (ZMod n) →+* ULift.{u + 1} (ZMod ell) :=
  (ULift.ringEquiv.symm.toRingHom.comp (ZMod.castHom hd (ZMod ell))).comp
    ULift.ringEquiv.toRingHom

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

/-- Sheafified extension of constant coefficients. For the prime quotient this is E / ell E.
Source: Stacks, Tags 03EK and 0F1J
(blueprint: def-kun-prime-coefficient-constructions). -/
def primeCoefficientQuotient (φ : A →+* B) (V : Scheme.{u}) :
    Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B) :=
  Sheaf.composeAndSheafify V.smallEtaleTopology (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)

/-- The sheaf quotient unit: on presheaf representatives x maps to 1 tensor x, then to
sheafification. Source: Stacks, Tags 03EK and 0F1J
(blueprint: def-kun-prime-coefficient-constructions). -/
def primeCoefficientQuotientUnit (φ : A →+* B) (V : Scheme.{u}) :
    𝟭 (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ⟶
      primeCoefficientQuotient φ V ⋙ Sheaf.restrictScalars V.smallEtaleTopology φ :=
  (Sheaf.adjunction V.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)).unit

/-- The ordinary coefficient identification, with rule x tensor y maps to bar x tensor y.
The first arrow applies the quotient unit to x; the second is the balanced tensor map
of restriction of scalars. Both use sheaf tensor, including its sheafification.
Source: Stacks, Tags 03EK and 0F1J
(blueprint: def-kun-prime-coefficient-constructions). -/
def primeCoefficientTensorMap (φ : A →+* B) (V : Scheme.{u})
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    M ⊗ (Sheaf.restrictScalars V.smallEtaleTopology φ).obj N ⟶
      (Sheaf.restrictScalars V.smallEtaleTopology φ).obj
        ((primeCoefficientQuotient φ V).obj M ⊗ N) :=
  (primeCoefficientQuotientUnit φ V).app M ▷
      (Sheaf.restrictScalars V.smallEtaleTopology φ).obj N ≫
    Functor.LaxMonoidal.μ (Sheaf.restrictScalars V.smallEtaleTopology φ)
      ((primeCoefficientQuotient φ V).obj M) N

/-- Degree-zero embedding used in the coefficient comparison.
Source: Stacks, Tag 0F1J (blueprint: def-kun-prime-coefficient-constructions). -/
@[implicit_reducible]
def primeSingle (Λ : Type (u + 1)) [CommRing Λ] (V : Scheme.{u}) :
    Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ DerivedCategoryModule Λ V :=
  _root_.DerivedCategory.singleFunctor _ 0

/-- The recorded derived inverse image, with all coefficient universes fixed.
Source: Stacks, Tag 0F1J (blueprint: def-kun-prime-coefficient-constructions). -/
@[implicit_reducible]
def primePullback (Λ : Type (u + 1)) [CommRing Λ] {V W : Scheme.{u}} (f : V ⟶ W) :
    DerivedCategoryModule Λ W ⥤ DerivedCategoryModule Λ V :=
  L(upperStar (ModuleCat.{u + 1} Λ) f)

/-- The recorded derived direct image, with all coefficient universes fixed.
Source: Stacks, Tag 0F1J (blueprint: def-kun-prime-coefficient-constructions). -/
@[implicit_reducible]
def primePushforward (Λ : Type (u + 1)) [CommRing Λ] {V W : Scheme.{u}} (f : V ⟶ W) :
    DerivedCategoryModule Λ V ⥤ DerivedCategoryModule Λ W :=
  R(lowerStar (ModuleCat.{u + 1} Λ) f)


end AlgebraicGeometry.Etale
