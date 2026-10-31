/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedOpenImageDeltaDefs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero

/-! Naturality of the condensed open-image connecting morphism.

Source: latest blueprint, p-dl-a1-exact, Step 1
(blueprint: new-dl-a1-naturality).

Proof: apply connecting-map naturality to the image of the canonical morphism of
short-exact-sequence triangles. Naturality of the inverse canonical degree-zero
comparison identifies the source with ordinary direct image.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Generic form of the naturality calculation, for any left exact functor. -/
private theorem singleTriangle_delta_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact) (τ : S ⟶ T) :
    F.map τ.τ₃ ≫ (F.singleRightDerivedH0Iso T.X₃).inv ≫
        DerivedCategory.HomologySequence.δ
          (F.rightDerivedFunctor.mapTriangle.obj hT.singleTriangle) 0 1 rfl =
      ((F.singleRightDerivedH0Iso S.X₃).inv ≫
        DerivedCategory.HomologySequence.δ
          (F.rightDerivedFunctor.mapTriangle.obj hS.singleTriangle) 0 1 rfl) ≫
        (DerivedCategory.homologyFunctor _ 1).map
          (F.rightDerivedFunctor.map ((DerivedCategory.singleFunctor _ 0).map τ.τ₁)) := by
  have hn : F.map τ.τ₃ ≫ (F.singleRightDerivedH0Iso T.X₃).inv =
      (F.singleRightDerivedH0Iso S.X₃).inv ≫
        (DerivedCategory.homologyFunctor _ 0).map
          (F.rightDerivedFunctor.map ((DerivedCategory.singleFunctor _ 0).map τ.τ₃)) := by
    simpa only [Functor.singleRightDerivedH0Iso_def,
      Functor.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso,
      NatIso.ofComponents_inv_app, Functor.comp_map] using
      F.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso.inv.naturality τ.τ₃
  have hd := (DerivedCategory.homologyFunctor _ 0).homologySequenceδ_naturality
    (F.rightDerivedFunctor.mapTriangle.obj hS.singleTriangle)
    (F.rightDerivedFunctor.mapTriangle.obj hT.singleTriangle)
    (F.rightDerivedFunctor.mapTriangle.map
      (ShortComplex.ShortExact.singleTriangle.map hS hT τ)) 0 1 rfl
  rw [← Category.assoc, hn, Category.assoc, Category.assoc]
  exact congrArg ((F.singleRightDerivedH0Iso S.X₃).inv ≫ ·) hd

/-- Naturality of `dlOpenImageDelta` for an arbitrary morphism of schemes. -/
private theorem dlOpenImageDelta_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U C : Scheme.{u}} (j : U ⟶ C)
    {S T : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))} (hS : S.ShortExact) (hT : T.ShortExact) (τ : S ⟶ T) :
    (lowerStar Λ j).map τ.τ₃ ≫ dlOpenImageDelta Λ j T hT =
      dlOpenImageDelta Λ j S hS ≫
        (DerivedCategory.homologyFunctor _ 1).map
          ((moduleObjectDerivedPushforward Λ j).map
            ((DerivedCategory.singleFunctor _ 0).map τ.τ₁)) :=
  singleTriangle_delta_naturality (lowerStar Λ j) hS hT τ

/-- The connecting morphism is natural under morphisms of constructible short exact
sequences on the geometric open. -/
theorem condensedOpenImage_naturality
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p)
    (_iota : PadicAlgCl ell →+* ℂ)
    (U₀ C₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
    [SmoothOfRelativeDimension 1 C₀.hom]
    (j₀ : U₀ ⟶ C₀) [IsOpenImmersion j₀.left] [QuasiCompact j₀.left]
    [IsDominant j₀.left] :
    ∀ (S T : ShortComplex
      (Mod (Sheaf (Scheme.ProEt.topology
        ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap D.k₀ D.k)))).obj U₀).left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ell)
          ((Over.pullback (Spec.map (CommRingCat.ofHom
            (algebraMap D.k₀ D.k)))).obj U₀).left)))
      (hS : S.ShortExact) (hT : T.ShortExact) (τ : S ⟶ T),
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj U₀).left S.X₁ →
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj U₀).left S.X₂ →
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj U₀).left S.X₃ →
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj U₀).left T.X₁ →
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj U₀).left T.X₂ →
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj U₀).left T.X₃ →
      (lowerStar (Profinite.padicAlgClRingObj ell) (dlGeometricOpen D j₀)).map τ.τ₃ ≫
          dlOpenImageDelta (Profinite.padicAlgClRingObj ell)
            (dlGeometricOpen D j₀) T hT =
        dlOpenImageDelta (Profinite.padicAlgClRingObj ell)
            (dlGeometricOpen D j₀) S hS ≫
          (DerivedCategory.homologyFunctor _ 1).map
            ((moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ell)
              (dlGeometricOpen D j₀)).map
              ((DerivedCategory.singleFunctor _ 0).map τ.τ₁)) := by
  intro S T hS hT τ _ _ _ _ _ _
  exact dlOpenImageDelta_naturality _ _ hS hT τ

end AlgebraicGeometry.ProEtale.CondensedRing
