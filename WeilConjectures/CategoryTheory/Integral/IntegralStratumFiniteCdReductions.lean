/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.CategoryTheory.Integral.IntegralStratumFiniteCdReductionsSupportWindow
import WeilConjectures.CategoryTheory.Integral.IntegralStratumFiniteCdReductionsAssembly
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Mathlib.CategoryTheory.HomCongr

/-!
# Integral stratum finite-reduction bound

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-int-compactness/sk-lem-int-ext-bound.proof.md, three finite-reduction bullets.
The bound is stated with explicit finite upper bounds on the two classical
cohomological dimensions. Positive quotient exponents are indexed by `n + 1`.
(blueprint: lem-sfb-integral-stratum-finite-cd-reductions)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace CategoryTheory

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory

private theorem stratum_hom_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Z S V : Scheme.{u}} (i : Z ⟶ X) (v : S ⟶ Z) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion v] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (r : ℤ)
    (h : Subsingleton ((DerivedCategory.singleFunctor _ 0).obj L ⟶
      ((CondensedRing.upperStar Λ v).mapDerivedCategory.obj
        ((CondensedRing.closedSupport Λ i j).rightDerivedFunctor.obj B))⟦r⟧))
    (f : (DerivedCategory.singleFunctor _ 0).obj
      ((CondensedRing.lowerStar Λ i).obj
        ((CondensedRing.openImmersionLowerShriek Λ v).obj L)) ⟶ B⟦r⟧) :
    f = 0 := by
  let := CondensedRing.closedSupport_lowerStarExact Λ i j hij
  let R := (CondensedRing.closedSupport Λ i j).rightDerivedFunctor
  let U := (CondensedRing.upperStar Λ v).mapDerivedCategory
  let A := (CondensedRing.openImmersionLowerShriek Λ v).obj L
  let AZ := (DerivedCategory.singleFunctor _ 0).obj A
  let LS := (DerivedCategory.singleFunctor _ 0).obj L
  let eI := ((CondensedRing.lowerStar Λ i).mapDerivedCategorySingleFunctor 0).app A
  let eV := ((CondensedRing.openImmersionLowerShriek Λ v).mapDerivedCategorySingleFunctor 0).app L
  let ai := CondensedRing.closedSupportDerivedAdjunction Λ i j hij
  let av := Adjunction.mapDerivedCategoryAdjunction
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ v)
  let e₁ := Iso.homCongr eI.symm (Iso.refl (B⟦r⟧))
  let e₂ := ai.homEquiv AZ (B⟦r⟧)
  let e₃ := Iso.homCongr eV.symm ((R.commShiftIso r).app B)
  let e₄ := av.homEquiv LS ((R.obj B)⟦r⟧)
  let e₅ := Iso.homCongr (Iso.refl LS) ((U.commShiftIso r).app (R.obj B))
  let e := (((e₁.trans e₂).trans e₃).trans e₄).trans e₅
  exact e.injective (h.elim (e f) (e 0))

end CategoryTheory
