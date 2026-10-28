/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.SixFunctors.EtaleHomComparisonModels
public import Sheaf.SixFunctors.EtaleHomTransposeExactShiftData

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Pretriangulated.Opposite Opposite
namespace AlgebraicGeometry.Etale

/-- The evaluation transpose satisfies the shift square in one fixed integer degree.
Source: Stacks Project, Tags 08JC and 08J9; blueprint
`lem-coef-etale-hom-transpose-exact`, proof steps 3--4.

Transpose the shift square through the tensor--Hom adjunction. The transpose equation
for `v` turns both sides into evaluation after scalar balancing; the normalization
hypotheses identify those evaluations on flat-term K-flat models, and localization
extends the identity to all objects. This is the fixed-degree calculation from which
`NatTrans.CommShift` is assembled.
(blueprint: lem-coef-etale-hom-transpose-exact-comm-shift-core) -/
theorem etaleHomComparison_reversedExact_commShift_core
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M)
    (hv : IsEtaleHomTranspose X φ M v)
    (sA : ((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).CommShift ℤ)
    (sB : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
      ((scalarExtension φ X).obj M)).CommShift ℤ)
    (_chiPhi : (EtaleHomLeft X φ M).CommShift ℤ)
    (_chiPsi : (EtaleHomRight X φ M).CommShift ℤ)
    (hA : EtaleHomShiftNormalization (ModuleCat.{u + 1} A) X M sA)
    (hB : EtaleHomShiftNormalization (ModuleCat.{u + 1} B) X
      ((scalarExtension φ X).obj M) sB)
    (n : ℤ) :
    letI := etaleHomScalarCommShift X φ
    letI := _chiPhi
    letI := _chiPsi
    NatTrans.CommShiftCore v n := by
  sorry

end AlgebraicGeometry.Etale
