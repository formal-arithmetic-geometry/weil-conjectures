/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentHigherImageClasses
public import Sheaf.AlgebraicGeometry.UnitStructureCoefficientIso
public import Sheaf.AlgebraicGeometry.RawRestrictedClassNormalizationData
public import Sheaf.AlgebraicGeometry.UnitLocalizedScalarConjugation

/-! # Raw evaluation after the canonical unit coefficient identification -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] tensorPullback tensorPullbackObj
  Etale.rawRestrictedCohomologyComparison Etale.abelianHigherDirectImageClass
  affineRealizationRawEvaluation affineRealizationClass affineRealizationRawEquiv
  Etale.sheafHDerivedEquiv Etale.sheafHToDerived CategoryTheory.derivedExtEvaluation
  coherentEtaleRestrictionIso unitLocalizedCoefficientIso unitStructureCoefficientIso
  coherentEtaleMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Transport raw structural classes by the actual inverse coefficient isomorphism.
Source: Stacks Project, Tag 03Q8.
(blueprint: new-unit-scalar-raw-data). -/
def unitCoherentRawClass {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ) (U : S.Etale)
    (z : (Etale.abelianHigherDirectImageRawPresheaf f q X.etaleAdditiveSheaf).obj (op U)) :
    (Etale.abelianHigherDirectImageRawPresheaf f q
      (liftedCoherentEtaleSheaf (SheafOfModules.unit X.ringCatSheaf))).obj (op U) :=
  (Etale.normalizationRawCoefficient f q (unitStructureCoefficientIso X).inv).app (op U) z


end
end AlgebraicGeometry.Scheme.Modules
