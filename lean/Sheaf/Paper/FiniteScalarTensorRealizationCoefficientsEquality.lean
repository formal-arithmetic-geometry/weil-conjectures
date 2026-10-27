/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteScalarTensorRealization

/-! # Definitional bridge for the coefficient realization

Source: Stacks Project, Tags 04VK and 07A4.
(blueprint: lem-sf-finite-scalar-tensor-realization-coefficients-equality).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor MonoidalCategory
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
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive

universe u u₁ u₂ u₃ u₄ v₂ v₄
namespace WeilConjectures

/-- The coefficient realization is the representative descent comparison it specializes.

Proof: unfold the coefficient-level constructor.  Its tensor input is the
fixed representative comparison supplied by `finiteScalarFixedTensorRepresentativeForCoefficients`,
and its output is exactly `finiteScalarTensorRealizationOfRepresentatives` with
the same ordinary and derived tensor functors.  The two natural isomorphisms
therefore agree componentwise by the constructor equation.

Source: Stacks Tags 04VK and 07A4.
(blueprint: lem-sf-finite-scalar-tensor-realization-coefficients-equality).
-/
theorem finiteScalarTensorRealizationForCoefficients_eq_representatives
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
    (S : ObjectProperty H) (hF : ∀ Q, P Q → S (F.obj Q))
    (ff : ((whiskeringLeft (P.FullSubcategory × P.FullSubcategory)
      (DerivedCategory (Sheaf (ProEt.topology T) B) ×
        DerivedCategory (Sheaf (ProEt.topology T) B)) E).obj
      ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q))).FullyFaithful)
    (t' : H × H ⥤ H) (T' : E × E ⥤ E)
    (r' : (S.ι.prod S.ι) ⋙ t' ⋙ q' ≅ ((S.ι ⋙ q').prod (S.ι ⋙ q')) ⋙ T')
    (b : uncurry.obj ((curriedTensor (Sheaf (ProEt.topology T) B)).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ F ≅ (F.prod F) ⋙ t') :
    finiteScalarTensorRealizationForCoefficients B T q' F LF eps P hP S hF ff t' T' r' b =
      finiteScalarTensorRealizationOfRepresentatives DerivedCategory.Q q' F LF eps P S hF ff
        _ t' (ProEtale.derivedTensor B T) T'
        (finiteScalarFixedTensorRepresentativeForCoefficients B T P hP) r' b := by sorry

end WeilConjectures
