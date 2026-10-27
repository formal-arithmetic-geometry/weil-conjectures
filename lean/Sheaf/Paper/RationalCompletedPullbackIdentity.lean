/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.Paper.RationalRealizationPullbackComparison
public import Sheaf.Paper.PbcActualRingedExchange

/-! # Completed identity and descent to all raw rational fraction arrows.

Source: Bhatt--Scholze, Remark 6.8.15, p. 62; Stacks Tags 03CB, 0D6D, 07A4, 099N.
(blueprint: lem-per-rational-completed-pullback-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]


set_option maxHeartbeats 800000 in
-- Nested chart conversions arise in the explicit tensor-section normalization.
/-- Completed identity and descent to all raw rational fraction arrows.
Source: Stacks Tags 099N, 099J, 0A0E, 0B65 and 0DV0; BS Remark 6.8.15.

Proof: restrict QuotientCompleted.identity to bounded constructible complete
objects. QuotientCompleted.identity_unit gives the displayed strict unit equation,
with the recorded object inclusions. The unit_isIso field makes gamma_id invertible.
The normalized ordinary comparison and the supplied tensor identity determine the
ordinary identity square, by testing on generators and flat-term K-flat resolutions;
hderived and derived_normalization retain the fixed derived counits. Substitute
alpha_normalization and cancel realization of gamma_id to obtain the identity
square on integral objects. On a raw object define rawId by rationalizing the
integral identity and inserting raw_objects. Its inverse rationalizes the inverse.
The inverse identities are functoriality. On each f/varpi^n, raw_fractions reduces
naturality to the integral identity naturality multiplied by the same central
scalar varpi^(-n). Every raw object has an integral representative, so the object
calculation gives the displayed equality of natural transformations on the entire
raw category, without any full-faithfulness hypothesis.
(blueprint: lem-per-rational-completed-pullback-identity). -/
theorem rationalCompletedPullbackIdentity (sX : RationalModuleRealization l E X)
    (a : RationalRealizationPullbackComparison l E (𝟙 X) sX sX)
    (hcoefficient : (a.rationalCoefficient =
  (proEtaleRingInverseImageId X).hom.app
    (rationalCoefficientSheaf l X E)))
    (moduleId : rationalPullModule l E (𝟙 X) a.rationalCoefficient ≅ 𝟭 _)
    (hmodule :
      let unitSection {S T : Scheme.{u}} (g : S ⟶ T)
          (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
          (M : pbcModules T (rationalCoefficientSheaf l T E))
          (V : T.ProEt) (m : M.val.obj (op V)) :
          ((rationalPullModule l E g c).obj M).val.obj
            (op ((proEtaleBaseChange g).obj V)) :=
        pbcTensorSection c
          ((proEtaleRingModulePullback g (rationalCoefficientSheaf l T E)
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
              (rationalCoefficientSheaf l T E)) (Iso.refl _)).obj M)
          (op ((proEtaleBaseChange g).obj V)) 1
          (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l T E)
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
              (rationalCoefficientSheaf l T E)) (Iso.refl _) M V m)
      let scalarMul (T : Scheme.{u})
          (M : pbcModules T (rationalCoefficientSheaf l T E)) (V : T.ProEtᵒᵖ)
          (e : (rationalCoefficientSheaf l T E).obj.obj V) (m : M.val.obj V) : M.val.obj V :=
        e • m
      (∀ (M : pbcModules X (rationalCoefficientSheaf l X E)) (V : X.ProEt)
        (m : M.val.obj (op V))
        (e : (rationalCoefficientSheaf l X E).obj.obj (op ((proEtaleBaseChange (𝟙 X)).obj V))),
      (moduleId.hom.app M).val.app (op ((proEtaleBaseChange (𝟙 X)).obj V))
          (scalarMul X
            ((rationalPullModule l E (𝟙 X) a.rationalCoefficient).obj M)
            (op ((proEtaleBaseChange (𝟙 X)).obj V)) e
            (unitSection (𝟙 X) a.rationalCoefficient M V m)) =
        scalarMul X M (op ((proEtaleBaseChange (𝟙 X)).obj V)) e
          (M.val.map ((MorphismProperty.Over.pullbackId _ _ X).hom.app V).op m)))
    (ambientId : rationalPullDerived l E (𝟙 X) a.rationalCoefficient ≅ 𝟭 _)
    (hderived : (∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
  ambientId.hom.app (DerivedCategory.Q.obj P) =
    rationalPullComplexCounit l E (𝟙 X) a.rationalCoefficient P ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex moduleId (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P))) :
    ∃ (integralId : a.integral.completedFunctor l E ≅ 𝟭 _),
      (∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
      (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (𝟙 X)).app K.obj ≫
        (integralId.hom.app K).hom =
          (pbcActualDerivedPullIdIso (pbcIntegralDatum l E) X).hom.app K.obj) ∧
      ∃ (rawId : a.rawPull ≅ 𝟭 _),
      (∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
      rawId.hom.app
          ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
        eqToHom (a.raw_objects K) ≫
          (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map
            (integralId.hom.app K)) ∧
      (a.alpha.hom ≫ whiskerLeft sX.J ambientId.hom = whiskerRight rawId.hom sX.J) := by sorry

end AlgebraicGeometry.Scheme
