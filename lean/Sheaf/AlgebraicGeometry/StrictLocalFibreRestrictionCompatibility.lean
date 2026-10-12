/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.GeometricFibreExchangeGerms
public import Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison
public import WeilConjectures.SixFunctors.BaseChange.GlobalSections

/-! # Compatibility of the constructed strict-local fibre restriction

Source: Stacks Project, Tag 0EYP, canonical restrictions, and Tag 03Q9.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
open Scheme

/-- Restriction along an explicit map to the strict-local pullback, followed by
inverse-image composition and evaluation at the identity etale object.
Source: Stacks Project, Tag 0EYP, canonical restrictions.
(blueprint: lem-sbc-strict-local-fibre-restriction-compatibility). -/
noncomputable def strictLocalFibreRestriction
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {g' : X' ⟶ X} {f : X ⟶ Y}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {s : Spec (.of Ω) ⟶ Y}
    (i : X' ⟶ pullback f (strictHenselizationStructuralMap s))
    (hi : i ≫ pullback.fst f (strictHenselizationStructuralMap s) = g')
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.Γ (pullback f (strictHenselizationStructuralMap s)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj
      ((upperStar (ModuleCat.{u + 1} Λ)
        (pullback.fst f (strictHenselizationStructuralMap s))).obj F) ⟶
      ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 X'))) :=
  globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i
      ((upperStar (ModuleCat.{u + 1} Λ)
        (pullback.fst f (strictHenselizationStructuralMap s))).obj F) ≫
    (Sheaf.Γ X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) i
        (pullback.fst f (strictHenselizationStructuralMap s)) g' hi.symm).inv.app F) ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
        (Scheme.Etale.mk (𝟙 X')) Over.mkIdTerminal)).hom.app _

/-- Compatibility uses only the two projections of i and the pointed limit-leg
identities, and asserts neither continuity nor invertibility.

Source: Stacks Project, Tag 0EYP, canonical restrictions, and Tag 03Q9.
(blueprint: lem-sbc-strict-local-fibre-restriction-compatibility).

Proof: Expand qcqsStrictLocalSectionRestriction. Its terminal evaluation map is
inverse to the first factor in the global-sections restriction along i. Cancel
these maps. Naturality of the unit for i moves its unit past the neighbourhood
section map. The composition coherence equation for inverse-image units then
combines the unit for the strict-local projection with the unit for i into the
unit for g'. Evaluate the inverse-image composition isomorphism at the terminal
object. The remaining etale morphism has projections f' followed by the marked
point and g': the first is the pointed limit-leg identity in ht, the second is hi.
Pullback uniqueness identifies it with geometricFibreSectionLift. The resulting
composite is geometricFibreSectionRestriction by its definition. This argument
works for empty schemes and the zero coefficient ring; it has no integral, local,
or proper assumption. -/
theorem strictLocalFibreRestriction_compatibility
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    (t : Spec (.of Ω) ⟶ strictHenselizationScheme s)
    (ht : ∀ j : SmallModel.{u} (strictHenselizationNeighbourhoods s),
      t ≫ (strictHenselizationCone s).π.app (op (op j)) ≫
        (Spec (unop ((equivSmallModel.{u}
          (strictHenselizationNeighbourhoods s)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2.left)
    (i : X' ⟶ pullback f (strictHenselizationStructuralMap s))
    (hi : i ≫ pullback.fst f (strictHenselizationStructuralMap s) = g')
    (hi' : i ≫ pullback.snd f (strictHenselizationStructuralMap s) = f' ≫ t)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
    qcqsStrictLocalSectionRestriction Λ f s F j ≫ strictLocalFibreRestriction Λ i hi F =
      geometricFibreSectionRestriction Λ sq F
        ((AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2 := by
  sorry

end AlgebraicGeometry.Etale
