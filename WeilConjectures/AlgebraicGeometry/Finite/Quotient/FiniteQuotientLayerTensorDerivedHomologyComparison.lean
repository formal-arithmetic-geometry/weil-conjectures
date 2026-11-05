/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCoefficientLayerData
public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerTensorComplex
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData

import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerTensorDerivedSliceComparison

/-! # Derived chart homology comparison for the finite quotient layer

Source: Stacks Project, sites-cohomology.tex, Tags 094I and 06YU.
(blueprint: lem-weil-pbc-finite-quotient-layer-tensor-derived-homology-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

private theorem homology_iso_of_derived_iso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [HasDerivedCategory C] [HasDerivedCategory D]
    {K L : DerivedCategory C} (e : Nonempty (F.mapDerivedCategory.obj K ≅
      F.mapDerivedCategory.obj L)) (q : ℤ) :
    Nonempty (F.obj ((DerivedCategory.homologyFunctor C q).obj K) ≅
      F.obj ((DerivedCategory.homologyFunctor C q).obj L)) := by
  obtain ⟨e⟩ := e
  exact ⟨(F.mapDerivedCategoryHomologyFunctorIso q).app K ≪≫
    (DerivedCategory.homologyFunctor D q).mapIso e ≪≫
      ((F.mapDerivedCategoryHomologyFunctorIso q).app L).symm⟩

end AlgebraicGeometry.Scheme
