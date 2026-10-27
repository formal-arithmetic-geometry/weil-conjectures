/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.AffineLinearTraceAction
import Sheaf.CategoryTheory.ExactDegreeZero
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows

/-! # Identity inverse image of the constant derived unit

Source: blueprint sec-smooth-purity/sk-prop-an, vector-bundle purity proof paragraph 2;
identity compatibility of inverse image and the constant sheaf adjunction.
(blueprint: lem-pur-vector-integration-identity-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

attribute [local implicit_reducible] ordinaryFiniteSingleFunctor

-- Reuse the abelian and derived-category instance proofs captured by this category.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

-- The argument of ConstantPullbackIdentityCoherence works for general abelian coefficients.
private theorem constant_identity (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    (S : Scheme.{u}) (M : A) :
    (Scheme.upperStarConstantSheafIso A (𝟙 S)).hom.app M =
      (upperStarId A S).hom.app ((constantSheaf S.smallEtaleTopology A).obj M) := by
  symm
  let adj := constantSheafAdj S.smallEtaleTopology A terminalIsTerminal
  let adjId := upperStarLowerStarAdjunction A (𝟙 S)
  let e := lowerStarCompSheafSectionsTerminalIso A (𝟙 S)
  apply (((adj.comp adjId).ofNatIsoRight e).homEquiv M _).injective
  change _ = (((adj.comp adjId).ofNatIsoRight e).homEquiv M _)
    ((((adj.comp adjId).ofNatIsoRight e).leftAdjointUniq adj).hom.app M)
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change adj.homEquiv M _ (adjId.homEquiv _ _
    ((upperStarId A S).hom.app
      ((constantSheaf S.smallEtaleTopology A).obj M))) ≫ e.hom.app _ = _
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  dsimp only [adjId]
  rw [upperStarId_hom_app_unit_app]
  have ht : PreservesTerminal.iso (Scheme.Hom.Etale (𝟙 S)) =
      (MorphismProperty.Over.pullbackId @AlgebraicGeometry.Etale ⊤ S).app
        (⊤_ S.Etale) := by
    apply Iso.ext
    exact terminalIsTerminal.hom_ext _ _
  simp [e, lowerStarCompSheafSectionsTerminalIso, lowerStarId,
    GrothendieckTopology.lowerStarId, ht, ← Functor.map_comp, ← op_comp]

-- Invert the already proved exact degree-zero unit identity.
private theorem exact_identity_single {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (F : C ⥤ C) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (e : F ≅ 𝟭 C) (M : C) :
    (F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor C 0).map (e.hom.app M) =
      (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app
        ((DerivedCategory.singleFunctor C 0).obj M) := by
  have h := SheafExactDegreeZero.unit_id F e M (e.inv.app M) rfl
  unfold SheafExactDegreeZero.unit SheafExactDegreeZero.map
    SheafExactDegreeZero.comparison SheafExactDegreeZero.functor SheafExactDegreeZero.obj at h
  have hi : ((F.mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctor C 0).mapIso (e.app M)).inv =
      ((Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C).app
        ((DerivedCategory.singleFunctor C 0).obj M)).inv := h
  exact congrArg Iso.hom (Iso.ext_inv hi)

/-- The constant-unit pullback comparison over the identity is the derived identity
comparison used for the affine linear action.
Source: blueprint vector-bundle purity proof paragraph 2, identity-base normalization.
(blueprint: lem-pur-vector-integration-identity-unit).

Proof: at sheaf level both maps are the unique comparison between the two left
adjoints to global sections. Their adjoint transposes are the identity, by the unit
law for upperStarLowerStarAdjunction over the identity. The natural comparison of
exact derived functors commutes with singleFunctor. On a complex concentrated in
degree zero, the derived identity comparison is the identity-chain-map comparison;
this follows by applying the localization functor to the identity chain map.
Composing these equalities gives the stated equality with exactly the chosen
singleFunctorCompLeftDerivedUpperStarIso. This applies to the zero ring and the empty
scheme as well, since it uses only adjunction uniqueness and functoriality.
-/
theorem vectorIntegration_identity_unit (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) :
    (ordinaryFiniteUnitPullback A (𝟙 S)).hom =
      (affineLinearPullbackId A S).hom.app (ordinaryFiniteUnit A S) := by
  simp only [ordinaryFiniteUnitPullback, ordinaryFiniteSinglePullbackIso,
    ordinaryFiniteSingleExactPullbackIso_eq, ordinaryFiniteSingleFunctor_eq,
    affineLinearPullbackId,
    Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Functor.mapIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc]
  rw [constant_identity]
  rw [exact_identity_single]
  rfl

end AlgebraicGeometry.Etale
