/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.SixFunctors.EtaleHomComparisonModels
import Sheaf.SixFunctors.EtaleScalarTensorShiftCancellation

/-! # Fixed-degree étale Hom shift component

Source: Stacks Project, Tags 08JC and 08J9; blueprint
`lem-coef-etale-hom-transpose-exact-comm-shift-core`, proof steps 3--4.
This is the fixed-degree component equation, strictly simpler than the assembled
`NatTrans.CommShiftCore` because it has no extensional wrapper or composite shift
structures. The proof is the tensor--Hom diagram chase from the parent module.
(blueprint: lem-coef-etale-hom-transpose-exact-comm-shift-component) -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Pretriangulated.Opposite Opposite
namespace AlgebraicGeometry.Etale

/-- The evaluation transpose commutes, in a fixed degree `n` and at a fixed object `K`, with
the normalized shifts: those of `EtaleHomLeft` (`F(sA)` followed by the scalar shift) and of
`EtaleHomRight` (Hom of the inverse scalar shift followed by `sB`).
Source: Stacks Project, Tags 08JC and 08J9; blueprint `thm-coef-finite-hom`, proof
paragraph 2.

Proof. Postcompose both sides with the inverse of the `sB` shift and transpose through the
tensor--Hom adjunction; the evaluation normalization `hB` turns the transposed right side
into signed tensor evaluation, i.e. tensor cancellation followed by evaluation. Tensor
cancellation is natural in its second variable (the `CommShift` compatibility of the
tensor bifunctor maps and naturality of `shiftFunctorCompIsoId`), so the shifted map can be
moved through it. Precompose with the tensor image of the scalar shift, an isomorphism;
replace the unshifted evaluation by the transpose equation `hv`; apply
`etaleHomTensorComparison_shiftCancellation` and the naturality of the binary tensor
comparison in its second variable. The composite obtained is the image under scalar
extension of the `sA` evaluation normalization `hA`, which is the transposed left side.
Cancelling the tensor image of the scalar shift and using injectivity of the adjunction's
`homEquiv` gives the equation.
(blueprint: lem-coef-etale-hom-transpose-exact-comm-shift-component) -/
theorem etaleHomComparison_reversedExact_commShift_component
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M)
    (hv : IsEtaleHomTranspose X φ M v)
    (sA : ((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).CommShift ℤ)
    (sB : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
      ((scalarExtension φ X).obj M)).CommShift ℤ)
    (hA : EtaleHomShiftNormalization (ModuleCat.{u + 1} A) X M sA)
    (hB : EtaleHomShiftNormalization (ModuleCat.{u + 1} B) X
      ((scalarExtension φ X).obj M) sB)
    (K : DerivedCategoryModule A X) (n : ℤ) :
    letI := etaleHomScalarCommShift X φ
    ((scalarExtension φ X).map ((sA.commShiftIso n).hom.app (op K)) ≫
      ((scalarExtension φ X).commShiftIso n).hom.app
        (((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).obj (op K))) ≫
      (v.app (op K))⟦n⟧' =
    v.app (op (K⟦-n⟧)) ≫
      ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
        ((scalarExtension φ X).obj M)).map
          ((((scalarExtension φ X).commShiftIso (-n)).inv.app K).op) ≫
      (sB.commShiftIso n).hom.app (op ((scalarExtension φ X).obj K)) := by
  sorry

end AlgebraicGeometry.Etale
