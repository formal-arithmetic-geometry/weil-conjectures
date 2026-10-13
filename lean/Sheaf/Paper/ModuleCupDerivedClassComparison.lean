/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.Paper.ModuleCupRealizationComplexData
public import Sheaf.Paper.ModuleCupNaiveDerivedCompatibility
public import Sheaf.Paper.ModuleCupDerivedHomologyTensor

/-! # Comparing resolution classes with the homology of derived global sections

Source: Stacks Project, Tags 01DZ and 0FKU.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable (X : Scheme.{u})
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

local instance : CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))

/-- Derived global sections of a coefficient sheaf placed in degree zero. -/
abbrev cupDerivedSections (F : X.Modules) :=
  (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)

/-- A comparison with derived global sections, including the representative formula.
The cycles in integer degrees are obtained by the actual extension by zero. -/
structure CupDerivedClassComparison where
  equiv : ∀ (F : X.Modules) (n : ℕ),
    (RingedSpace.moduleCohomology X.toRingedSpace n).obj F ≃ₗ[Γ(X, ⊤)]
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) (n : ℤ)).obj
        (cupDerivedSections X F)
  on_cycles : ∀ {F : X.Modules} (D : CupAcyclicResolution F) (n : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K),
    let K := ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj D.integerComplex
    ∃ z : K.cycles (n : ℤ),
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).map
        (D.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom) (K.iCycles n z) =
          a.val ∧
      equiv F n (D.class n a) =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) (n : ℤ)).map
          (moduleCup_globalComparison X D.integerComplex ≫
            (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map
              (inv D.derivedAugmentation))
          (cupLocalizedCycleClass K n z)

/-- The right-derived cohomology functor agrees with homology of RΓ, with its
canonical formula on every computing resolution.
Source: Stacks Project, Tag 01DZ, computation by injective resolutions;
Tag 0FKU, global specialization of the comparison diagram.
(blueprint: lem-sc-module-cup-derived-class-comparison)
Proof: choose an injective resolution of F and extend it by zero to integers.
This bounded-below complex of injectives is K-injective, so the right-derived
comparison unit at it is invertible. The localized augmentation is invertible
as well. The homology factorization of localization and the extension homology
isomorphism therefore identify H^n(RΓ(F[0])) with H^n(Γ(I)). Compose with the
inverse of I.isoRightDerivedObj to obtain equiv, in the displayed direction.
For another computing resolution D, extend D.comparison by zero. Its equation
over the augmentation and naturality of the derived comparison identify the
localized composite with the chosen comparison above. The map on global
homology is precisely the one in D.class; computes says it is invertible.
The extension cycles isomorphism lifts a to z and identifies its component
through extendXIso. Naturality of homologyπ then gives the displayed equation.
Independence of the injective resolution follows from comparison maps over F
and their homotopies. At n=0 extension has a zero incoming differential, just
as the natural complex does; zero sheaves and zero cycles cause no exception. -/
theorem exists_cupDerivedClassComparison : Nonempty (CupDerivedClassComparison X) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
