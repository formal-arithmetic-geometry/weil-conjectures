/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReductionFunctors
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!
# Canonical coefficient pullback maps

Source: Stacks Project, Tags 03EK, 06YU and 0F1J
(blueprint: def-kun-prime-coefficient-pullbacks).
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
/-- The sheaf inverse image in the coefficient comparison.
Source: Stacks, Tag 0F1J (blueprint: def-kun-prime-coefficient-pullbacks). -/
abbrev primePulledSheaf (Λ : Type (u + 1)) [CommRing Λ]
    {V W : Scheme.{u}} (f : V ⟶ W)
    (M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (upperStar (ModuleCat.{u + 1} Λ) f).obj M

/-- Pullback of a coefficient quotient map, using the canonical scalar comparison.
Source: Stacks, Tags 0F1J and 0D6J
(blueprint: def-kun-prime-coefficient-pullbacks). -/
def primePullbackCoefficientMap (φ : A →+* B) {V W : Scheme.{u}} (f : V ⟶ W)
    (M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} B))
    (q : M ⟶ (Sheaf.restrictScalars W.smallEtaleTopology φ).obj N) :
    primePulledSheaf A f M ⟶
      (Sheaf.restrictScalars V.smallEtaleTopology φ).obj (primePulledSheaf B f N) :=
  (upperStar (ModuleCat.{u + 1} A) f).map q ≫
    (upperStarRestrictScalarsIsoSheaf φ f).hom.app N

/-- Exact inverse image on degree-zero sheaves, with its canonical computation isomorphism.
Source: Stacks, Tag 0F1J (blueprint: def-kun-prime-coefficient-pullbacks). -/
def primePullbackSingleIso (Λ : Type (u + 1)) [CommRing Λ]
    {V W : Scheme.{u}} (f : V ⟶ W)
    (M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (primePullback Λ f).obj ((primeSingle Λ W).obj M) ≅
      (primeSingle Λ V).obj (primePulledSheaf Λ f M) :=
  (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).app M


end AlgebraicGeometry.Etale
