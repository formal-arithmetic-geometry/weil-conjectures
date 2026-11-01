/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorResolution
public import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent

/-! # Normalized tensor descent before specialization

Source: Stacks Tags 07A4 and 04VK.
(blueprint: lem-sf-finite-scalar-tensor-descent).
 -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf

universe u v w u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

-- Share the already proved coefficient-instance shortcuts used by the canonical map.
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat

attribute [local instance 10000] WeilConjectures.finiteScalarCountableColimits
  WeilConjectures.finiteScalarTensorTotal
  WeilConjectures.finiteScalarIntrinsicCountableColimits
  WeilConjectures.finiteScalarFunctorAdditive WeilConjectures.finiteScalarFunctorEquivalence
  WeilConjectures.finiteScalarFixedTensorPreadditive

-- Use the same inherited data as the native derived tensor and exact-functor APIs.
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms

-- Match the native additive data in the published complex tensor models.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive

namespace WeilConjectures

/-- Curry an uncurried tensor comparison, with the postcomposition conversions explicit.
Source: Stacks 04VK (blueprint: lem-sf-finite-scalar-tensor-descent). -/
def finiteScalarCurryRealizationIso
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (T : C ⥤ C ⥤ C) (F : C ⥤ D) (S : D × D ⥤ D)
    (e : uncurry.obj T ⋙ F ≅ (F.prod F) ⋙ S) :
    (postcompose₂.obj F).obj T ≅
      (((whiskeringLeft₂ D).obj F).obj F).obj (curry.obj S) :=
  currying.unitIso.app _ ≪≫
    curry.mapIso (finiteScalarUncurryPostcomposeIso T F).symm ≪≫
    curry.mapIso e ≪≫ curryObjProdComp F F S

/-- Currying leaves the tensor comparison's actual component unchanged.
Source: Stacks 04VK (blueprint: lem-sf-finite-scalar-tensor-descent). -/
@[simp] theorem finiteScalarCurryRealizationIso_hom_app
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (T : C ⥤ C ⥤ C) (F : C ⥤ D) (S : D × D ⥤ D)
    (e : uncurry.obj T ⋙ F ≅ (F.prod F) ⋙ S) (X Y : C) :
    ((finiteScalarCurryRealizationIso T F S e).hom.app X).app Y = e.hom.app (X, Y) := by
  simp [finiteScalarCurryRealizationIso, finiteScalarUncurryPostcomposeIso]

/-- Construct a curried comparison from the unique normalized representative descent.
Source: Stacks 04VK and 07A4
(blueprint: lem-sf-finite-scalar-tensor-descent). -/
@[irreducible] def finiteScalarTensorRealizationOfRepresentatives
    {K : Type u₁} [Category.{v₁} K] {H : Type u₂} [Category.{v₂} H]
    {D : Type u₃} [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E]
    (q : K ⥤ D) (q' : H ⥤ E) (F : K ⥤ H) (LF : D ⥤ E)
    (eps : q ⋙ LF ≅ F ⋙ q')
    (P : ObjectProperty K) (S : ObjectProperty H)
    (hF : ∀ X, P X → S (F.obj X))
    (ff : ((whiskeringLeft (P.FullSubcategory × P.FullSubcategory) (D × D) E).obj
      ((P.ι ⋙ q).prod (P.ι ⋙ q))).FullyFaithful)
    (t : K × K ⥤ K) (t' : H × H ⥤ H)
    (T : D ⥤ D ⥤ D) (T' : E × E ⥤ E)
    (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ uncurry.obj T)
    (r' : (S.ι.prod S.ι) ⋙ t' ⋙ q' ≅ ((S.ι ⋙ q').prod (S.ι ⋙ q')) ⋙ T')
    (b : t ⋙ F ≅ (F.prod F) ⋙ t') :
    (postcompose₂.obj LF).obj T ≅
      (((whiskeringLeft₂ E).obj LF).obj LF).obj (curry.obj T') :=
  finiteScalarCurryRealizationIso T LF T'
    (Classical.choose (tensorComparisonDescent q q' F LF eps.hom P S hF ff
      t t' (uncurry.obj T) T' r r' b
      (fun X _ ↦ (eps.app X).isIso_hom)
      (fun X Y _ _ ↦ (eps.app (t.obj (X, Y))).isIso_hom)).exists)

/-- The constructed comparison satisfies its actual representative equation.
Source: Stacks 04VK and 07A4
(blueprint: lem-sf-finite-scalar-tensor-descent). -/
theorem finiteScalarTensorRealizationOfRepresentatives_fac
    {K : Type u₁} [Category.{v₁} K] {H : Type u₂} [Category.{v₂} H]
    {D : Type u₃} [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E]
    (q : K ⥤ D) (q' : H ⥤ E) (F : K ⥤ H) (LF : D ⥤ E)
    (eps : q ⋙ LF ≅ F ⋙ q')
    (P : ObjectProperty K) (S : ObjectProperty H)
    (hF : ∀ X, P X → S (F.obj X))
    (ff : ((whiskeringLeft (P.FullSubcategory × P.FullSubcategory) (D × D) E).obj
      ((P.ι ⋙ q).prod (P.ι ⋙ q))).FullyFaithful)
    (t : K × K ⥤ K) (t' : H × H ⥤ H)
    (T : D ⥤ D ⥤ D) (T' : E × E ⥤ E)
    (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ uncurry.obj T)
    (r' : (S.ι.prod S.ι) ⋙ t' ⋙ q' ≅ ((S.ι ⋙ q').prod (S.ι ⋙ q')) ⋙ T')
    (b : t ⋙ F ≅ (F.prod F) ⋙ t')
    (X Y : K) (hx : P X) (hy : P Y) :
    LF.map (r.hom.app (⟨X, hx⟩, ⟨Y, hy⟩)) ≫
        ((finiteScalarTensorRealizationOfRepresentatives q q' F LF eps P S hF ff
          t t' T T' r r' b).hom.app (q.obj X)).app (q.obj Y) ≫
        T'.map (Prod.mkHom (eps.hom.app X) (eps.hom.app Y)) =
      eps.hom.app (t.obj (X, Y)) ≫ q'.map (b.hom.app (X, Y)) ≫
        r'.hom.app (⟨F.obj X, hF X hx⟩, ⟨F.obj Y, hF Y hy⟩) := by
  simpa only [finiteScalarTensorRealizationOfRepresentatives,
    finiteScalarCurryRealizationIso_hom_app] using
    (Classical.choose_spec (tensorComparisonDescent q q' F LF eps.hom P S hF ff
      t t' (uncurry.obj T) T' r r' b
      (fun X _ ↦ (eps.app X).isIso_hom)
      (fun X Y _ _ ↦ (eps.app (t.obj (X, Y))).isIso_hom)).exists) X Y hx hy

/-- Perform the fixed-model step before specializing the coefficient category.
Source: Stacks 07A4 and 04VK
(blueprint: lem-sf-finite-scalar-tensor-descent). -/
@[irreducible] def finiteScalarTensorRealizationForCoefficients
    (B : Type u₁) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (T : Scheme.{u})
    {H : Type u₂} [Category.{v₂} H] {E : Type u₄} [Category.{v₄} E]
    (q' : H ⥤ E) (F : CochainComplex (Sheaf (ProEt.topology T) B) ℤ ⥤ H)
    (LF : DerivedCategory (Sheaf (ProEt.topology T) B) ⥤ E)
    (eps : DerivedCategory.Q ⋙ LF ≅ F ⋙ q')
    (P : ObjectProperty (CochainComplex (Sheaf (ProEt.topology T) B) ℤ))
    (hP : ∀ Q, P Q → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q)
    (S : ObjectProperty H) (hF : ∀ X, P X → S (F.obj X))
    (ff : ((whiskeringLeft (P.FullSubcategory × P.FullSubcategory)
      (DerivedCategory (Sheaf (ProEt.topology T) B) ×
        DerivedCategory (Sheaf (ProEt.topology T) B)) E).obj
      ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q))).FullyFaithful)
    (t' : H × H ⥤ H) (T' : E × E ⥤ E)
    (r' : (S.ι.prod S.ι) ⋙ t' ⋙ q' ≅ ((S.ι ⋙ q').prod (S.ι ⋙ q')) ⋙ T')
    (b : uncurry.obj ((curriedTensor (Sheaf (ProEt.topology T) B)).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ F ≅ (F.prod F) ⋙ t') :
    (postcompose₂.obj LF).obj (ProEtale.derivedTensor B T) ≅
      (((whiskeringLeft₂ E).obj LF).obj LF).obj (curry.obj T') :=
  finiteScalarTensorRealizationOfRepresentatives DerivedCategory.Q q' F LF eps P S hF ff
    _ t' (ProEtale.derivedTensor B T) T'
    (finiteScalarFixedTensorRepresentativeForCoefficients B T P hP) r' b

end WeilConjectures
