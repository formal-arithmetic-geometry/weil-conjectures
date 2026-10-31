/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
public import WeilConjectures.CategoryTheory.Preadditive.CoyonedaSectionsExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero

/-! # Cohomology of actual condensed coefficient modules

Source: latest blueprint, ordinary/compact cohomology and the degree-zero clause of
sk-def-sfb-module-derived-lower-shriek (blueprint: def-weil-ordinary-compact-cohomology).

The formulas use actual condensed coefficient modules and also work over
an arbitrary algebraically closed field. Sections are represented by maps from the regular
coefficient module; evaluation at its unit is terminal-object evaluation. The coefficient
field is lifted to the section universe, with its canonical ring equivalence to Qbar_l.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Constant global scalars of any commutative condensed coefficient ring.
Source: latest blueprint, Lambda_Y = p_Y^* Lambda
(blueprint: def-weil-ordinary-compact-cohomology). -/
def condensedRingScalarSections
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    Γ Λ →+* Γ (condensedRingObj Λ X) :=
  letI : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  letI : (upperStarFromPoint X).Additive :=
    rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [rightExactFunctor_iff]
      infer_instance)
  Γ.mapFunctor (upperStarFromPoint X)

/-- Terminal sections with the canonical coefficient action, for every condensed ring.
This applies to all four coefficient rings of the cohomology convention.
Source: latest blueprint, Fib_s by geometric-point evaluation
(blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev condensedRingCoefficientSections
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      ModuleCat.{u + 1} (Γ Λ) :=
  coyonedaSections ((Mod.regularEndRingHom.op).comp
    ((RingEquiv.toOpposite _).toRingHom.comp (condensedRingScalarSections Λ X)))

/-- Ordinary coefficient complex, formed with the actual condensed derived direct image.
Over the algebraically closed point the terminal evaluation is exact, so its right derived
functor is the geometric-point evaluation on complexes. Any constructible complex, including
constants, Tate twists and underlying complexes of Weil objects, is an input to this functor.
Source: latest blueprint, RΓ(Y,K) = Fib_s(Ra_* K)
(blueprint: def-weil-ordinary-compact-cohomology). -/
def condensedRingOrdinaryCoefficientComplex
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (a : X ⟶ Y) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) ⥤ DerivedCategory (ModuleCat.{u + 1} (Γ Λ)) :=
  (lowerStar Λ a).rightDerivedFunctor ⋙
    (condensedRingCoefficientSections Λ Y).rightDerivedFunctor

/-- Compact coefficient complex, formed with the actual compactification lower shriek.
Source: latest blueprint, RΓ_c(Y,K) = Fib_s(Ra_! K)
(blueprint: def-weil-ordinary-compact-cohomology). -/
def condensedRingCompactCoefficientComplex
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) ⥤ DerivedCategory (ModuleCat.{u + 1} (Γ Λ)) :=
  rightDerivedLowerShriekOfCompactification Λ c ⋙
    (condensedRingCoefficientSections Λ Y).rightDerivedFunctor

/-- Ordinary cohomology in every integer degree and with any condensed coefficient ring.
Source: latest blueprint, H^i(Y,K) = H^i(RΓ(Y,K))
(blueprint: def-weil-ordinary-compact-cohomology). -/
def condensedRingOrdinaryCohomology
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (a : X ⟶ Y) (n : ℤ) :=
  condensedRingOrdinaryCoefficientComplex Λ a ⋙ DerivedCategory.homologyFunctor _ n

/-- Compact cohomology in every integer degree and with any condensed coefficient ring.
Source: latest blueprint, H_c^i(Y,K) = H^i(RΓ_c(Y,K))
(blueprint: def-weil-ordinary-compact-cohomology). -/
def condensedRingCompactCohomology
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) (n : ℤ) :=
  condensedRingCompactCoefficientComplex Λ c ⋙ DerivedCategory.homologyFunctor _ n

/-- The coefficient field in the universe of sections.
Source: latest blueprint, coefficient cohomology
(blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev CohomologyScalar (ℓ : ℕ) [Fact ℓ.Prime] := ULift.{u + 1} (PadicAlgCl ℓ)

/-- Constant scalar sections of the pulled-back condensed coefficient ring.
Source: latest blueprint, Lambda_X = p_X^* Lambda
(blueprint: def-weil-ordinary-compact-cohomology). -/
def cohomologyScalarSections (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    CohomologyScalar.{u} ℓ →+* Γ (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) :=
  (condensedRingScalarSections (Profinite.padicAlgClRingObj ℓ) X).comp
    ((Profinite.PadicAlgCl.constRingHom ℓ).comp ULift.ringEquiv.toRingHom)

/-- Global sections of a Qbar_l coefficient module, with their actual scalar action.
A section is the module map Lambda_X -> G sending 1 to that section.
Source: latest blueprint, coefficient cohomology
(blueprint: def-weil-ordinary-compact-cohomology). -/
def condensedCoefficientSections (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) ⥤
      ModuleCat.{u + 1} (CohomologyScalar.{u} ℓ) :=
  coyonedaSections ((Mod.regularEndRingHom.op).comp
    ((RingEquiv.toOpposite _).toRingHom.comp (cohomologyScalarSections ℓ X)))

/-- Ordinary cohomology: homology of Ra_* followed by exact terminal-point evaluation.
For an algebraically closed base this is H^i(Fib_s(Ra_* K)).
Source: latest blueprint, H^i = H^i RΓ
(blueprint: def-weil-ordinary-compact-cohomology). -/
def condensedOrdinaryCohomology (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (a : X ⟶ Y) (n : ℤ) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) ⥤
      ModuleCat.{u + 1} (CohomologyScalar.{u} ℓ) :=
  (lowerStar (Profinite.padicAlgClRingObj ℓ) a).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor _ n ⋙ condensedCoefficientSections ℓ Y

/-- Compact cohomology: the actual compactification lower shriek, homology, and point sections.
Source: latest blueprint, H_c^i = H^i RΓ_c
(blueprint: def-weil-ordinary-compact-cohomology). -/
def condensedCompactCohomology (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a) (n : ℤ) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) ⥤
      ModuleCat.{u + 1} (CohomologyScalar.{u} ℓ) :=
  rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) c ⋙
    DerivedCategory.homologyFunctor _ n ⋙ condensedCoefficientSections ℓ Y

end AlgebraicGeometry.ProEtale.CondensedRing
