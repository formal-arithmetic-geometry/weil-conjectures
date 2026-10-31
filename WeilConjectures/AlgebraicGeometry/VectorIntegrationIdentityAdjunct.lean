/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.VectorIntegrationUnitTranspose
import WeilConjectures.AlgebraicGeometry.VectorIntegrationIdentityUnit
import all WeilConjectures.AlgebraicGeometry.VectorIntegrationRankZeroLocal

/-! # Exceptional identity adjunction in ordered integration coordinates

Source: the rank-zero normalization in the diagonal chart proof.
(blueprint: lem-pur-vector-integration-identity-adjunct).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 128
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationChart

attribute [local irreducible] Etale.rightDerivedLowerShriek
  Etale.rightDerivedUpperShriek Etale.rightDerivedUpperShriekAdjunction
  Etale.affineLinearCompactComparison Functor.mapDerivedCategory
attribute [local semireducible] ProEtale.AffineSpacePurity.orderedSource
  ProEtale.AffineSpacePurity.exceptional
attribute [local implicit_reducible] affineTraceTower affineTraceProjection
  Etale.affineLinearBaseCoefficient

private theorem chartMap_injective_of_unit_mono
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {X Y : C} [Mono (adj.unit.app Y)] {f g : X ⟶ Y}
    (h : L.map f = L.map g) : f = g := by
  apply (cancel_mono (adj.unit.app Y)).mp
  have hf := adj.unit.naturality f
  have hg := adj.unit.naturality g
  simp only [Functor.id_map, Functor.comp_map] at hf hg
  rw [hf, hg, h]

private theorem chartAffineCoefficient_zero (A : Type (u + 1)) [CommRing A]
    (B : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA) (hB : IsUnit (N : Γ(B, ⊤))) :
    (Etale.affineLinearCoefficientDescent A N hA t B hB 0 ≪≫
      Etale.vectorIntegrationBaseCoefficientPullback A N hA t
        (affineTraceProjection B 0) hB 0) = Iso.refl _ := by
  apply Iso.ext
  change (Etale.affineLinearPullbackId A B).inv.app (Etale.ordinaryFiniteUnit A B) ≫
    (Etale.ordinaryFiniteUnitPullback A (𝟙 B)).hom = 𝟙 _
  rw [Etale.vectorIntegration_identity_unit]
  exact Iso.inv_hom_id_app _ _

private theorem chartAffineCounit_zero (A : Type (u + 1)) [CommRing A]
    (B : Scheme.{u}) [IsNoetherian B] (N : ℕ) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA t T hT) (hB : IsUnit (N : Γ(B, ⊤))) :
    (Etale.affineTraceAdjunction A N hA t D B hB 0).counit.app
      (Etale.ordinaryFiniteUnit A B) = 𝟙 _ := by
  unfold Etale.affineTraceAdjunction
  rfl

-- Normalize the trace before putting it under the adjunction and comparison maps.
private theorem chartAffineTrace_zero (A : Type (u + 1)) [CommRing A] [Finite A]
    (B : Scheme.{u}) [IsNoetherian B] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA t T hT) (hB : IsUnit (N : Γ(B, ⊤))) :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection B 0)).map
        (Etale.affineLinearCoefficientDescent A N hA t B hB 0 ≪≫
          Etale.vectorIntegrationBaseCoefficientPullback A N hA t
            (affineTraceProjection B 0) hB 0).inv ≫
      (Etale.affineLinearCompactComparison N hN A hA B hB 0).inv ≫
      (Etale.affineTraceAdjunction A N hA t D B hB 0).counit.app
        (Etale.ordinaryFiniteUnit A B) =
      (Etale.unboundedEtaleLowerShriekId A B).hom.app (Etale.ordinaryFiniteUnit A B) := by
  rw [chartAffineCoefficient_zero]
  simp only [Iso.refl_inv]
  erw [(Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
    (affineTraceProjection B 0)).map_id]
  simp only [Category.id_comp]
  erw [chartAffineCounit_zero, Category.comp_id, Etale.compact_comparison_zero]

/-- The ordinary adjunct of the compact-support identity comparison is the
inverse exceptional-identity comparison at the coefficient unit.
Source: chart proof, rank-zero clause, and the ordered coefficient-unit transpose
(blueprint: lem-pur-vector-integration-identity-adjunct).

Proof: coefficient descent cancels against identity-unit pullback. The rank-zero
ordered adjunction is the identity adjunction, so its counit is the identity.
The compact-support comparison is the canonical unbounded identity comparison.
Apply affineTranspose_unit_coordinates at zero: its source and integration
coordinates are identities by their HEq specifications, and its target is the
image of the exceptional-identity comparison. The comparison-adjunction unit at
the exceptional target is invertible, since that target is isomorphic to the
bounded-below coefficient unit. Its naturality therefore detects equality of the
ordinary maps. No nonempty hypothesis is used. -/
private theorem identityAdjunctRing (P : WeilConjectures.PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsNoetherian B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] :
    (Etale.rightDerivedUpperShriekAdjunction
      (AffineLinePurity.Ring P) (𝟙 B)).homEquiv
        (Etale.ordinaryFiniteUnit (AffineLinePurity.Ring P) B)
        (Etale.ordinaryFiniteUnit (AffineLinePurity.Ring P) B)
        ((Etale.unboundedEtaleLowerShriekId (AffineLinePurity.Ring P) B).hom.app
          (Etale.ordinaryFiniteUnit (AffineLinePurity.Ring P) B)) =
      (((Etale.rightDerivedUpperShriekIsoOfIso
        (AffineLinePurity.Ring P) (Iso.refl B)) ≪≫
        Etale.leftDerivedUpperStarId
          (ModuleCat.{u + 1} (AffineLinePurity.Ring P)) B).app
            (Etale.ordinaryFiniteUnit (AffineLinePurity.Ring P) B)).symm.hom := by
  let e := ((Etale.rightDerivedUpperShriekIsoOfIso
    (AffineLinePurity.Ring P) (Iso.refl B)) ≪≫
    Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} (AffineLinePurity.Ring P)) B).app
      (Etale.ordinaryFiniteUnit (AffineLinePurity.Ring P) B)
  let : IsIso ((ProEtale.derivedComparisonAdjunction
      (ModuleCat.{u + 1} (AffineLinePurity.Ring P)) B).unit.app
        ((Etale.rightDerivedUpperShriek (AffineLinePurity.Ring P)
          (𝟙 B)).obj (Etale.ordinaryFiniteUnit (AffineLinePurity.Ring P) B))) :=
    ProEtale.isIso_derivedComparisonAdjunction_unit_app
      (ModuleCat.{u + 1} (AffineLinePurity.Ring P)) B _
      (_root_.DerivedCategory.TStructure.t.plus.prop_of_iso e.symm (unit_properties P B).1)
  apply chartMap_injective_of_unit_mono
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} (AffineLinePurity.Ring P)) B)
  have h := ProEtale.VectorIntegrationChart.affineTranspose_unit_coordinates P B aB 0
  have hs : (ProEtale.VectorIntegrationChart.orderedSourceIso P B 0).hom = 𝟙 _ := by
    unfold ProEtale.VectorIntegrationChart.orderedSourceIso
    exact eq_of_heq (ProEtale.VectorIntegrationChart.orderedSourceIso_existsUnique
      P B 0).exists.choose_spec
  have hi : ProEtale.AffineOrderedIntegration.integrationTranspose P B aB
      (ProEtale.VectorIntegrationChart.unitPlus P B)
      (Etale.ordinaryFiniteUnit (AffineLinePurity.Ring P) B)
      (ProEtale.VectorIntegrationChart.unit_properties P B).2 (Iso.refl _) 0 = 𝟙 _ := by
    unfold ProEtale.AffineOrderedIntegration.integrationTranspose
    exact eq_of_heq (ProEtale.AffineOrderedIntegration.integrationTranspose_existsUnique
      P B aB _ _ _ _ 0).exists.choose_spec
  have ha : ProEtale.VectorIntegrationChart.affineTranspose P B aB 0 P.level
      (ProEtale.AffineSpacePurity.annihilates P) =
      ProEtale.VectorIntegrationChart.affineTransposeRaw P B aB 0 P.level
        (ProEtale.AffineSpacePurity.annihilates P) := by
    unfold ProEtale.VectorIntegrationChart.affineTranspose
    exact eq_of_heq (ProEtale.VectorIntegrationChart.affineTranspose_existsUnique
      P B aB 0 P.level (ProEtale.AffineSpacePurity.annihilates P)).exists.choose_spec
  erw [hs, hi, Category.id_comp, Category.id_comp, ha] at h
  dsimp only [ProEtale.VectorIntegrationChart.affineTransposeRaw] at h
  erw [chartAffineTrace_zero] at h
  exact h

/-- The ordinary adjunct of the compact-support identity comparison is the
inverse exceptional-identity comparison at the coefficient unit.
Source: chart proof, rank-zero clause, and the ordered coefficient-unit transpose
(blueprint: lem-pur-vector-integration-identity-adjunct).

Proof: coefficient descent cancels against identity-unit pullback. The rank-zero
ordered adjunction is the identity adjunction, so its counit is the identity.
The compact-support comparison is the canonical unbounded identity comparison.
Apply affineTranspose_unit_coordinates at zero: its source and integration
coordinates are identities by their HEq specifications, and its target is the
image of the exceptional-identity comparison. The comparison-adjunction unit at
the exceptional target is invertible, since that target is isomorphic to the
bounded-below coefficient unit. Its naturality therefore detects equality of the
ordinary maps. No nonempty hypothesis is used. -/
theorem identityAdjunct (P : WeilConjectures.PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsNoetherian B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] :
    (Etale.rightDerivedUpperShriekAdjunction
      P.Coefficient (𝟙 B)).homEquiv
        (Etale.ordinaryFiniteUnit P.Coefficient B)
        (Etale.ordinaryFiniteUnit P.Coefficient B)
        ((Etale.unboundedEtaleLowerShriekId P.Coefficient B).hom.app
          (Etale.ordinaryFiniteUnit P.Coefficient B)) =
      (((Etale.rightDerivedUpperShriekIsoOfIso
        P.Coefficient (Iso.refl B)) ≪≫
        Etale.leftDerivedUpperStarId
          (ModuleCat.{u + 1} P.Coefficient) B).app
            (Etale.ordinaryFiniteUnit P.Coefficient B)).symm.hom := by
  rcases P with @⟨F, C, E, fin, m, hm⟩
  cases m with
  | zero => omega
  | succ m =>
    let := fin
    let P : WeilConjectures.PurityFiniteSetting.{u} := ⟨F, C, E, m + 1, hm⟩
    exact identityAdjunctRing P B aB

end AlgebraicGeometry.ProEtale.VectorIntegrationChart
