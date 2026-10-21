module

public import Sheaf.AlgebraicGeometry.FieldActionTransportData

/-! # Normalized field-action transport interfaces

Source: Bhatt--Scholze Example 4.1.10, Definition 6.8.3 and Proposition 6.8.4;
main-20261015 direct-images paragraph (3), normalized ordinary derived sections
(blueprint: def-sfb-field-action-scalar-transport-data).

## Main definitions

* `ScalarTransport`: ordinary and total derived scalar transport, with fixed section,
  total-derived-counit, adjunction, and shift normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FieldActionTransport

open CondensedGalois

variable (k ks : Type u) [Field k] [Field ks] [Algebra k ks] [IsSepClosure k ks]

section Scalars
variable {R R' : Coefficients.{u}} (φ : R ⟶ R')
  [CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks)]
  [CategoryTheory.CondensedBar.ActionAbelian R' (ks ≃ₐ[k] ks)]
  (e : FieldData k ks R) (e' : FieldData k ks R')
  [ForgetData k ks R] [ForgetData k ks R']

/-- Ordinary and total derived scalar adjunctions in the action categories, with their
normalized comparison to the field presentation and to ordinary condensed modules.
The left-derived counit specifies a total left-derived functor, without introducing a
second tensor product or imposing flatness on the coefficient map.
Source: field-action node, coefficient-adjunction paragraph
(blueprint: def-sfb-field-action-scalar-transport-data). -/
structure ScalarTransport extends OrdinaryScalarTransport k ks φ e e' where
  /-- Total derived scalar extension in the action category. -/
  derivedExtension : DerivedCategory (CategoryTheory.CondensedBar.Equivariant R
    (ks ≃ₐ[k] ks)) ⥤ DerivedCategory (CategoryTheory.CondensedBar.Equivariant R'
      (ks ≃ₐ[k] ks))
  /-- Its localization counit, from derived to termwise ordinary extension. -/
  derivedCounit : DerivedCategory.Qh ⋙ derivedExtension ⟶
    extension.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  /-- The counit has the total-left-derived universal property. -/
  isDerived : derivedExtension.IsLeftDerivedFunctor derivedCounit
    (HomotopyCategory.quasiIso (CategoryTheory.CondensedBar.Equivariant R
      (ks ≃ₐ[k] ks)) (.up ℤ))
  /-- The left-derived functor carries its canonical shifts. -/
  [shift : derivedExtension.CommShift ℤ]
  /-- Its total-derived counit commutes with those shifts. -/
  derivedCounit_shift : NatTrans.CommShift derivedCounit ℤ
  /-- The derived scalar adjunction, with exact termwise restriction. -/
  derivedAdjunction : derivedExtension ⊣ restriction.functor.mapDerivedCategory
  /-- The total-left-derived counit is the transpose of the original scalar unit.
  Thus the derived adjunction and the specified total derivation are the same one. -/
  derivedCounit_normalization : ∀ J : HomotopyCategory
      (CategoryTheory.CondensedBar.Equivariant R (ks ≃ₐ[k] ks)) (.up ℤ),
    derivedCounit.app J = (derivedAdjunction.homEquiv _ _).symm
      (DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory adjunction.unit (.up ℤ)).app J) ≫
        restriction.functor.mapDerivedCategoryFactorsh.inv.app
          ((extension.mapHomotopyCategory (.up ℤ)).obj J))
  /-- Both unit and counit commute with canonical shifts. -/
  derivedAdjunction_shift : derivedAdjunction.CommShift ℤ
  /-- Transport preserves the K-flat scalar adjunction on the field site. -/
  derived : AdjunctionSquare
    (scalarDerivedAdjunction φ (Spec (.of k)))
    derivedAdjunction (fieldFunctor k ks e).mapDerivedCategory
      (fieldFunctor k ks e').mapDerivedCategory
  /-- The derived scalar-extension identification preserves canonical shifts. -/
  derived_shift : NatTrans.CommShift derived.extension.hom ℤ
  /-- The right comparison is exactly the canonical total-derived restriction comparison. -/
  derived_restriction : derived.restriction =
    Functor.isoWhiskerLeft (restrictX φ (Spec (.of k))).mapDerivedCategory
      (fieldFunctor k ks e).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    fieldComparison.derived ≪≫
    Functor.isoWhiskerRight (fieldFunctor k ks e').rightDerivedFunctorIsoMapDerivedCategory
      restriction.functor.mapDerivedCategory
  /-- Forgetting preserves the specified derived scalar adjunction. -/
  underlyingDerived : AdjunctionSquare derivedAdjunction
    (condensedScalarAdjunction φ)
    CategoryTheory.CondensedBar.forgetAction.mapDerivedCategory
      CategoryTheory.CondensedBar.forgetAction.mapDerivedCategory
  /-- Its right comparison is induced termwise by the actual underlying restriction. -/
  underlyingDerived_restriction : underlyingDerived.restriction =
    (Functor.mapDerivedCategoryCompIso restriction.functor
      CategoryTheory.CondensedBar.forgetAction).symm ≪≫
      Functor.mapDerivedCategoryNatIso restriction.underlying ≪≫
        Functor.mapDerivedCategoryCompIso CategoryTheory.CondensedBar.forgetAction
          (restrictCondensed φ)

attribute [instance] ScalarTransport.shift

end Scalars
end AlgebraicGeometry.ProEtale.FieldActionTransport
