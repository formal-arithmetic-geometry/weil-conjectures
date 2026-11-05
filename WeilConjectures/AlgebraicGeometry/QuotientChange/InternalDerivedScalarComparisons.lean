/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.InternalDerivedScalarComparisons

/-! # Integral quotient scalar comparison for unbounded direct image

Source: blueprint main-20261015, proper-base-change integral proof, paragraphs (1), (3);
Stacks Project, Tags 093M, 0D6D, 0D6E, 07A6 and 0944
(blueprint: def-sfb-internal-derived-scalar-comparisons).

Positive quotient levels are indexed by n + 1. All categories are ordinary unbounded
derived categories of the recorded internal module objects. No completion is applied.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

end AlgebraicGeometry.ProEtale.QuotientChange
namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [MonObj Λ''] [IsCommMonObj Λ'']

end AlgebraicGeometry.ProEtale.QuotientChange

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [MonObj Λ''] [IsCommMonObj Λ'']

/-- The ordinary balanced composition, including coefficient-map composition.
Source: Stacks 0D6D (blueprint: def-sfb-internal-derived-scalar-comparisons). -/
def ordinaryComp (a : Λ ⟶ Λ') [IsMonHom a]
    (b : Λ' ⟶ Λ'') [IsMonHom b] (c : Λ ⟶ Λ'') [IsMonHom c]
    (h : a ≫ b = c) (T : Scheme.{u}) :
    extension a T ⋙ extension b T ≅ extension c T :=
  by
    have hc : coefficientMap a T ≫ coefficientMap b T = coefficientMap c T :=
      (coefficientMap_comp a b T).symm.trans
        (congrArg (fun d ↦ coefficientMap d T) h)
    exact (Mod.extendScalarsComp (coefficientMap a T) (coefficientMap b T)).symm ≪≫
      (Mod.extendRestrictAdjunction _).leftAdjointUniq
        ((Mod.extendRestrictAdjunction _).ofNatIsoRight (Mod.comapCongr hc).symm)

end AlgebraicGeometry.ProEtale.QuotientChange
