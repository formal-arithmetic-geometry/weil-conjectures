/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.UpperShriekGeometric
public import WeilConjectures.CategoryTheory.DerivedCategory.FreeComparisonMapDerivedCategory

/-!
# Constructibility of the condensed carrier

The exact equivalence of native and condensed Weil sheaves intertwines the two
forgetful functors. Thus the carrier of a native Weil complex is bounded
constructible also in the condensed model.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]

/-- Forgetting the condensed Weil structure agrees with passing the native
geometric carrier through the coefficient equivalence. -/
noncomputable def condensedCarrierIso (K : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj
      ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj K) ≅
    (adicSheafDerivedEquivCondensedMod l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj
      ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj K) :=
  (Functor.mapDerivedCategoryCompForgetIso
    (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso
      (ProEtaleWeilSheaf.condensedFrobeniusComparison k₀ l X))).app K

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Native bounded constructibility gives bounded constructibility of the
forgotten condensed Weil complex. -/
theorem boundedConstructible_condensedCarrier (K : WeilComplex k₀ l X) :
    CondensedRing.boundedConstructible
      (CondensedRing.condensedRingObj (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj
        ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj K.obj)) := by
  have h := (boundedConstructibleAdic_iff_boundedConstructible l k₀ (AlgebraicClosure k₀)
    (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure)
    (forget.obj K)).1 ((objectProperty_iff K.obj).1 K.property)
  exact (CondensedRing.boundedConstructible _).prop_of_iso
    (condensedCarrierIso K.obj).symm h

end AlgebraicGeometry.WeilComplex
