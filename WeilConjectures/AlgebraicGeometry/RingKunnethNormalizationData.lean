/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KunnethGlobalSections

/-! # Explicit point and constant-pullback normalization data

Source: Stacks Tag 0F1E and the constant-sheaf equivalence on a separably closed point.
(blueprint: lem-sf-ring-kunneth-normalization-data).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]
  {k : Type u} [Field k] [IsSepClosed k]

/-- The adjunction transported from the specified derived point equivalence to RΓ.
Source: the point equivalence of Stacks Tag 0F1E.
(blueprint: lem-sf-ring-kunneth-normalization-data). -/
noncomputable def ringKunnethPointAdjunction :
    constantFunctor Λ (Spec (.of k)) ⊣
      rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k)) :=
  let P := constantSheafEquivalenceOfIsSepClosed Λ (k := k)
  letI : P.functor.Additive := additive_constantSheaf Λ _
  letI : P.inverse.Additive := additive_sheafSections_obj Λ _
  P.mapDerivedCategory.toAdjunction.ofNatIsoRight
    (rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).symm

/-- The specified constant-pullback comparison, with left-derived constants on the source.
Source: Stacks Tag 0F1E, pullback of constant complexes.
(blueprint: lem-sf-ring-kunneth-normalization-data). -/
noncomputable def ringKunnethConstantComparison
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).leftDerivedFunctor ≅
      constantFunctor Λ (Spec (.of k)) ⋙
        (upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor :=
  let F := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  F.leftDerivedFunctorIsoMapDerivedCategory ≪≫
    (constantFunctorCompLeftDerivedUpperStarIso Λ a).symm

/-- The exact tensor comparison used in the definition of the point tensor.
Source: Stacks Tag 0F1E, deriving the point constant-sheaf equivalence.
(blueprint: lem-sf-ring-kunneth-normalization-data). -/
noncomputable def ringKunnethPointTensorComparison
    (P Q : DerivedCategory (ModuleCat.{u + 1} Λ)) :
    (constantFunctor Λ (Spec (.of k))).obj (P ⊗ Q) ⟶
      (constantFunctor Λ (Spec (.of k))).obj P ⊗
        (constantFunctor Λ (Spec (.of k))).obj Q :=
  (mapDerivedCategoryObjTensorIsoDerivedTensor (ModuleCat.{u + 1} Λ)
    (Spec (.of k)) (constantSheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) P Q).hom

set_option maxHeartbeats 1000000 in
-- The specified derived equivalence and tensor comparison have large reducible data.
/-- The point tensor is the adjunct of the tensor of the two transported point counits.
Source: the explicit point-equivalence formula of Stacks Tag 0F1E.
(blueprint: lem-sf-ring-kunneth-normalization-data).
Proof: the transported unit is the unit of the derived point equivalence followed by
its inverse exact-sections comparison. Its counit is constants applied to the exact-
sections comparison followed by the derived equivalence counit. Substitution into the
unit formula for the adjunction bijection is precisely the definition of the point tensor. -/
theorem ringKunnethPointTensorTranspose
    (C D : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))) :
    (pointGlobalSectionsTensorIso Λ C D).hom =
      (ringKunnethPointAdjunction Λ).homEquiv _ _
        ((ringKunnethPointTensorComparison Λ
          ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C)
          ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj D)) ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) (Spec (.of k))).map
          ((ringKunnethPointAdjunction Λ).counit.app C)).app _ ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C).map
          ((ringKunnethPointAdjunction Λ).counit.app D)) := by
  simp [pointGlobalSectionsTensorIso, ringKunnethPointAdjunction,
    ringKunnethPointTensorComparison,
    Adjunction.homEquiv_unit, Adjunction.ofNatIsoRight_unit,
    Adjunction.ofNatIsoRight_counit, Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.Etale
