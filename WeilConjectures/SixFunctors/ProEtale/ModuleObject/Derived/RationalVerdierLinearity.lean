/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.LocallyConstantPerfectComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CtfLocallyClosedPerfectGeneration
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-! # Scalar linearity of the ordinary derived internal dual

Source: thm-coef-rational-verdier.proof.md, paragraph 2, precomposition by scalars.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite BraidedCategory
open scoped CategoryTheory.Obj

private theorem internalPre_smul
    {R C : Type*} [Ring R] [Category* C] [Preadditive C] [Linear R C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear R C] [MonoidalClosed C]
    {K L : C} (r : R) (f : K ⟶ L) (W : C) :
    (MonoidalClosed.pre (r • f)).app W = r • (MonoidalClosed.pre f).app W := by
  apply MonoidalClosed.uncurry_injective
  simp only [MonoidalClosed.uncurry_eq,
    MonoidalLinear.whiskerLeft_smul, MonoidalLinear.smul_whiskerRight,
    Linear.smul_comp, MonoidalClosed.id_tensor_pre_app_comp_ev]

private theorem derivedScalar
    {R C : Type*} [Ring R] [Category* C] [Abelian C] [HasDerivedCategory C] [Linear R C]
    (r : R) (τ : 𝟭 C ⟶ 𝟭 C) (hτ : ∀ M, τ.app M = r • 𝟙 M)
    (K : DerivedCategory C) :
    (Functor.mapDerivedCategoryIdIso C).inv.app K ≫
        (Functor.mapDerivedCategoryNatTrans τ).app K ≫
        (Functor.mapDerivedCategoryIdIso C).hom.app K = r • 𝟙 K := by
  have hm : Functor.mapDerivedCategoryNatTrans τ =
      r • 𝟙 ((𝟭 C).mapDerivedCategory) := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    intro P
    apply (cancel_mono ((𝟭 C).mapDerivedCategoryFactors.hom.app P)).mp
    rw [Functor.mapDerivedCategoryNatTrans_fac]
    have he : (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app P =
        r • 𝟙 (((𝟭 C).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
      ext n
      exact hτ (P.X n)
    rw [he, Functor.map_smul]
    change (𝟭 C).mapDerivedCategoryFactors.hom.app P ≫
        (r • DerivedCategory.Q.map (𝟙 _)) =
      (r • 𝟙 _) ≫ (𝟭 C).mapDerivedCategoryFactors.hom.app P
    simp only [CategoryTheory.Functor.map_id, Linear.comp_smul, Linear.smul_comp]
    exact congrArg (fun f ↦ r • f) ((Category.comp_id _).trans (Category.id_comp _).symm)
  rw [hm]
  simp

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Proved locally: the coefficient scalar action commutes with relative tensor product.
private theorem moduleMonoidalLinear
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : AlgebraicGeometry.Scheme.{u}) :
    letI := Mod.linearGlobalSections (condensedRingObj Λ X)
    MonoidalLinear (MonObj.Γ (condensedRingObj Λ X))
      (Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) := by
  let R := condensedRingObj Λ X
  let := Mod.linearGlobalSections R
  refine ⟨?_, ?_⟩
  · intro M N P r f
    have h (A B : Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) Ab.{u + 1}) R) :
        A ◁ (r • 𝟙 B) = r • 𝟙 (A ⊗ B) := by
      rw [Mod.linearOfRingHom_smul_id (RingHom.id _),
        Mod.linearOfRingHom_smul_id (RingHom.id _), Mod.smulNatTrans_app_tensor]
    calc
      M ◁ (r • f) = M ◁ (f ≫ (r • 𝟙 P)) := by simp
      _ = (M ◁ f) ≫ (r • 𝟙 (M ⊗ P)) := by rw [whiskerLeft_comp, h]
      _ = r • (M ◁ f) := by simp
  · intro r N P f M
    apply (cancel_epi (β_ M N).hom).mp
    rw [← braiding_naturality_right, Linear.comp_smul, ← braiding_naturality_right]
    rw [show M ◁ (r • f) = r • (M ◁ f) from ?_]
    · simp
    · have h (A B : Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) Ab.{u + 1}) R) :
          A ◁ (r • 𝟙 B) = r • 𝟙 (A ⊗ B) := by
        rw [Mod.linearOfRingHom_smul_id (RingHom.id _),
          Mod.linearOfRingHom_smul_id (RingHom.id _), Mod.smulNatTrans_app_tensor]
      calc
        M ◁ (r • f) = M ◁ (f ≫ (r • 𝟙 P)) := by simp
        _ = (M ◁ f) ≫ (r • 𝟙 (M ⊗ P)) := by rw [whiskerLeft_comp, h]
        _ = r • (M ◁ f) := by simp

/-- The derived dual carries precomposition by an actual coefficient section to
multiplication by that section. Both scalar maps are obtained from the same
termwise multiplication transformation, normalized by the canonical derived
identity isomorphism.

Source: thm-coef-rational-verdier.proof.md, paragraph 2
(blueprint: lem-coef-rational-verdier-derived-linearity).

Proof: global coefficient sections act centrally on module objects. The relative
tensor product is linear for this action, and its K-flat derived tensor product
inherits linearity. Tensor-Hom adjunction shows that precomposition is linear,
by uncurrying and moving the scalar across tensor product. On complexes the
scalar multiplication transformation is degreewise multiplication. The universal
property of derived localization identifies its induced transformation with the
scalar multiple of the identity. Conjugation by the canonical derived identity
isomorphism gives the displayed normalization. Functorial precomposition then
proves the equality. This holds on the unbounded ambient category, including
zero objects, and needs no constructibility assumption. -/
theorem rationalVerdier_derived_linearity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : AlgebraicGeometry.Scheme.{u})
    (W : moduleDerived Λ X) (z : MonObj.Γ (condensedRingObj Λ X))
    (K L : moduleDerived Λ X) (f : K ⟶ L) :
    let D := (derivedHom Λ X).flip.obj W
    let m := Functor.mapDerivedCategoryNatTrans (Mod.smulNatTrans z.hom)
    let scalar {A B : moduleDerived Λ X} (g : A ⟶ B) :=
      g ≫ (Functor.mapDerivedCategoryIdIso _).inv.app B ≫ m.app B ≫
        (Functor.mapDerivedCategoryIdIso _).hom.app B
    D.map (scalar f).op = scalar (D.map f.op) := by
  let R := condensedRingObj Λ X
  let C := Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) Ab.{u + 1}) R
  let := Mod.linearGlobalSections R
  let : MonoidalLinear (MonObj.Γ R) C := moduleMonoidalLinear Λ X
  have hτ (M : C) : (Mod.smulNatTrans z.hom).app M = z • 𝟙 M :=
    (Mod.linearOfRingHom_smul_id (RingHom.id _) z M).symm
  have hs := derivedScalar z (Mod.smulNatTrans z.hom) hτ
  dsimp only
  simp only [hs, Linear.comp_smul, Category.comp_id]
  exact internalPre_smul z f W

end AlgebraicGeometry.ProEtale.CondensedRing
