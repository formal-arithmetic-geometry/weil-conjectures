/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedOpenImageDeltaDefs
import WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerStarFullyFaithful

/-! Constructibility and positive-degree restriction for the condensed open image.

Source: latest blueprint, p-dl-a1-exact, Step 2
(blueprint: new-dl-a1-constructibility).

Proof: apply the restricted-functor constructibility theorem to every homology object
of the derived pushforward, then use exactness of upper restriction and the open
localization counit to transport the positive-degree vanishing. The finite-type,
quasi-compact and separated hypotheses provide the bounded constructible target.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory

private theorem overHomMk_left {S : Scheme.{u}} {X Y : Over S}
    (f : X.left ⟶ Y.left) (w : f ≫ Y.hom = X.hom) :
    Over.Hom.left (Over.homMk f w) = f := by
  rfl

private theorem exact_restriction_positive
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : D ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory D ⥤ DerivedCategory C)
    (R : DerivedCategory C ⥤ DerivedCategory D)
    (eL : L ≅ F.mapDerivedCategory) (adj : L ⊣ R) [IsIso adj.counit]
    (M : C) (r : ℤ) (hr : 0 < r) :
    IsZero (F.obj ((DerivedCategory.homologyFunctor D r).obj
      (R.obj ((DerivedCategory.singleFunctor C 0).obj M)))) := by
  let K0 := (DerivedCategory.singleFunctor C 0).obj M
  let Kpush := R.obj K0
  have hzero : IsZero ((DerivedCategory.homologyFunctor C r).obj K0) :=
    DerivedCategory.isZero_of_isLE _ 0 r hr
  have hi : IsIso (adj.counit.app K0) := inferInstance
  let e := (F.mapDerivedCategoryHomologyFunctorIso r).app Kpush
  let ec := (eL.app Kpush).symm ≪≫ asIso (adj.counit.app K0)
  exact hzero.of_iso (e ≪≫ (DerivedCategory.homologyFunctor C r).mapIso ec)

private theorem restriction_positive_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (r : ℤ) (hr : 0 < r) :
    IsZero ((upperStar Λ j).obj ((DerivedCategory.homologyFunctor _ r).obj
      ((moduleObjectDerivedPushforward Λ j).obj
        ((DerivedCategory.singleFunctor _ 0).obj F)))) := by
  exact exact_restriction_positive (upperStar Λ j)
    (upperStar Λ j).leftDerivedFunctor (lowerStar Λ j).rightDerivedFunctor
    (leftDerivedUpperStarIsoMapDerivedCategory Λ j)
    (derivedUpperStarLowerStarAdjunction Λ j) F r hr

private theorem finite_type_open_constructibility
    (k : Type u) [Field k] [Fact (ringChar k).Prime]
    (ell : ℕ) [Fact ell.Prime] [Fact (ringChar k ≠ ell)]
    (Xo Yo : Over (Spec (.of k)))
    [LocallyOfFiniteType Xo.hom] [QuasiCompact Xo.hom] [IsSeparated Xo.hom]
    [LocallyOfFiniteType Yo.hom] [QuasiCompact Yo.hom] [IsSeparated Yo.hom]
    (f : Xo ⟶ Yo) (hf : IsOpenImmersion f.left)
    (M : ConstantModelConstructible (Profinite.padicAlgClRingObj ell) Xo.left) :
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) Yo.left
        ((lowerStar (Profinite.padicAlgClRingObj ell) f.left).obj M.obj) ∧
      (∀ r : ℤ, IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
        Yo.left ((DerivedCategory.homologyFunctor _ r).obj
          ((moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ell) f.left).obj
            ((DerivedCategory.singleFunctor _ 0).obj M.obj)))) ∧
      (∀ r : ℤ, 0 < r → IsZero ((upperStar (Profinite.padicAlgClRingObj ell)
        f.left).obj ((DerivedCategory.homologyFunctor _ r).obj
          ((moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ell) f.left).obj
            ((DerivedCategory.singleFunctor _ 0).obj M.obj))))) := by
  let : IsOpenImmersion f.left := hf
  have hcmp (N : Mod (Sheaf (Scheme.ProEt.topology Yo.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) Yo.left))
      (hN : IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicAlgClRingObj ell) Yo.left) N) :
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) Yo.left N := by
    let : IsLocallyNoetherian Yo.left := LocallyOfFiniteType.isLocallyNoetherian Yo.hom
    let : CompactSpace Yo.left := QuasiCompact.compactSpace_of_compactSpace Yo.hom
    exact (adicConstructibilityPredicateComparison ell Yo.left
      (Profinite.padicAlgClRingObj ell) .algebraicClosure).1 N |>.mp hN
  have hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj ell) Xo.left) M.obj := by
    let : IsLocallyNoetherian Xo.left := LocallyOfFiniteType.isLocallyNoetherian Xo.hom
    let : CompactSpace Xo.left := QuasiCompact.compactSpace_of_compactSpace Xo.hom
    exact (adicConstructibilityPredicateComparison ell Xo.left
      (Profinite.padicAlgClRingObj ell) .algebraicClosure).1 M.obj |>.mpr M.property
  have hhom (r : ℤ) : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj ell) Yo.left)
      ((DerivedCategory.homologyFunctor _ r).obj
        ((moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ell) f.left).obj
          ((DerivedCategory.singleFunctor _ 0).obj M.obj))) := by
    exact finiteTypeDirectImage_single_constructible ell f M.obj hF r
  have hlow : IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) Yo.left
      ((lowerStar (Profinite.padicAlgClRingObj ell) f.left).obj M.obj) := by
    apply hcmp
    let L := lowerStar (Profinite.padicAlgClRingObj ell) f.left
    exact (finiteTypeDirectImage_single_constructible ell f M.obj hF 0).of_iso
      (L.singleRightDerivedH0Iso M.obj)
  refine ⟨hlow, fun r ↦ hcmp _ (hhom r), ?_⟩
  exact fun r hr ↦ restriction_positive_isZero _ f.left M.obj r hr

private theorem datum_ringChar_eq (D : WeilConjectures.FiniteFieldDatum) :
    ringChar D.k = D.p := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  exact ringChar.eq D.k D.p

/-- The constructible-heart and positive-degree part of the geometric assertions,
with the negative and degree-zero clauses isolated in `condensedOpenImage_basic`. -/
theorem condensedOpenImage_constructibility
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p)
    (_iota : PadicAlgCl ell →+* ℂ)
    (U₀ C₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
    [SmoothOfRelativeDimension 1 C₀.hom]
    (j₀ : U₀ ⟶ C₀) [IsOpenImmersion j₀.left] [QuasiCompact j₀.left]
    [IsDominant j₀.left] :
    ∀ M : ConstantModelConstructible (Profinite.padicAlgClRingObj ell)
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj U₀).left,
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj C₀).left
        ((lowerStar (Profinite.padicAlgClRingObj ell) (dlGeometricOpen D j₀)).obj M.obj) ∧
      (∀ r : ℤ, IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj C₀).left
        ((DerivedCategory.homologyFunctor _ r).obj
          ((moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ell)
            (dlGeometricOpen D j₀)).obj
            ((DerivedCategory.singleFunctor _ 0).obj M.obj)))) ∧
      (∀ r : ℤ, 0 < r → IsZero ((upperStar (Profinite.padicAlgClRingObj ell)
        (dlGeometricOpen D j₀)).obj
        ((DerivedCategory.homologyFunctor _ r).obj
          ((moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ell)
            (dlGeometricOpen D j₀)).obj
            ((DerivedCategory.singleFunctor _ 0).obj M.obj))))) := by
  let : Fact (ringChar D.k).Prime := ⟨by
    rw [datum_ringChar_eq D]
    exact D.prime⟩
  let : Fact (ringChar D.k ≠ ell) := ⟨by
    rw [datum_ringChar_eq D]
    exact _hEll.symm⟩
  let : LocallyOfFiniteType j₀.left := inferInstance
  let : LocallyOfFiniteType U₀.hom := by
    have h : LocallyOfFiniteType (j₀.left ≫ C₀.hom) := inferInstance
    simpa only [← j₀.w] using h
  let : QuasiCompact U₀.hom := by
    have h : QuasiCompact (j₀.left ≫ C₀.hom) := inferInstance
    simpa only [← j₀.w] using h
  let : IsSeparated U₀.hom := by
    have h : IsSeparated (j₀.left ≫ C₀.hom) := inferInstance
    simpa only [← j₀.w] using h
  let : LocallyOfFiniteType
      (((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap D.k₀ D.k)))).obj U₀).hom) := by
    exact MorphismProperty.baseChange_obj _ _ inferInstance
  let : QuasiCompact
      (((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap D.k₀ D.k)))).obj U₀).hom) := by
    exact MorphismProperty.baseChange_obj _ _ inferInstance
  let : IsSeparated
      (((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap D.k₀ D.k)))).obj U₀).hom) := by
    exact MorphismProperty.baseChange_obj _ _ inferInstance
  let : LocallyOfFiniteType
      (((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap D.k₀ D.k)))).obj C₀).hom) := by
    exact MorphismProperty.baseChange_obj _ _ inferInstance
  let : QuasiCompact
      (((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap D.k₀ D.k)))).obj C₀).hom) := by
    exact MorphismProperty.baseChange_obj _ _ inferInstance
  let : IsSeparated
      (((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap D.k₀ D.k)))).obj C₀).hom) := by
    exact MorphismProperty.baseChange_obj _ _ inferInstance
  intro M
  have h := finite_type_open_constructibility D.k ell
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj U₀)
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj C₀)
    (Over.homMk (dlGeometricOpen D j₀)
      (((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap D.k₀ D.k)))).map j₀).w))
    (by
      change IsOpenImmersion (dlGeometricOpen D j₀)
      exact MorphismProperty.overPullbackMap _ _ inferInstance) M
  rw [overHomMk_left] at h
  exact h

end AlgebraicGeometry.ProEtale.CondensedRing
