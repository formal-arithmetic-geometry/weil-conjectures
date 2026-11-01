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

end AlgebraicGeometry.ProEtale.CondensedRing
