/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.Paper.RationalRealizationPullbackComparison
public import Sheaf.Paper.PbcActualRingedExchange

/-! # Ordinary rational coefficient identity and the normalized module and derived identity.

Source: Bhatt--Scholze, Remark 6.8.15, p. 62; Stacks Tags 03CB, 0D6D, 07A4, 099N.
(blueprint: lem-per-rational-ordinary-pullback-identity).
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
/-- Ordinary rational coefficient identity and the normalized module and derived identity.
Source: Stacks Tags 03EL, 0D6D and 07A4; BS Remark 6.8.15.

Proof: coefficient restriction normalization identifies the identity coefficient map
with the inverse-image identity on continuous functions. The ordinary identity
comparison multiplies the coefficient into the module and restricts along the
specified pullbackId chart isomorphism; its inverse inserts one. Balancing and
local generation prove both inverse identities and the displayed section formula.
Derive this isomorphism on flat-term K-flat representatives, then use the fixed
computation counits to obtain the displayed equation on arbitrary complexes.
The identity counit is precisely the chain map of scalar multiplication.
(blueprint: lem-per-rational-ordinary-pullback-identity). -/
theorem rationalOrdinaryPullbackIdentity (sX : RationalModuleRealization l E X)
    (a : RationalRealizationPullbackComparison l E (𝟙 X) sX sX) :
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
    (a.rationalCoefficient =
    (proEtaleRingInverseImageId X).hom.app
      (rationalCoefficientSheaf l X E)) ∧
    ∃ (moduleId : rationalPullModule l E (𝟙 X) a.rationalCoefficient ≅ 𝟭 _),
    (∀ (M : pbcModules X (rationalCoefficientSheaf l X E)) (V : X.ProEt)
      (m : M.val.obj (op V))
      (e : (rationalCoefficientSheaf l X E).obj.obj (op ((proEtaleBaseChange (𝟙 X)).obj V))),
    (moduleId.hom.app M).val.app (op ((proEtaleBaseChange (𝟙 X)).obj V))
        (scalarMul X
          ((rationalPullModule l E (𝟙 X) a.rationalCoefficient).obj M)
          (op ((proEtaleBaseChange (𝟙 X)).obj V)) e
          (unitSection (𝟙 X) a.rationalCoefficient M V m)) =
      scalarMul X M (op ((proEtaleBaseChange (𝟙 X)).obj V)) e
        (M.val.map ((MorphismProperty.Over.pullbackId _ _ X).hom.app V).op m)) ∧
    ∃ (ambientId : rationalPullDerived l E (𝟙 X) a.rationalCoefficient ≅ 𝟭 _),
    (∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
    ambientId.hom.app (DerivedCategory.Q.obj P) =
      rationalPullComplexCounit l E (𝟙 X) a.rationalCoefficient P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex moduleId (.up ℤ) ≪≫
            Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P)) := by sorry

end AlgebraicGeometry.Scheme
