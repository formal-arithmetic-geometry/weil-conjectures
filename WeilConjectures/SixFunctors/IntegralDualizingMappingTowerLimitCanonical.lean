/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingMappingTower
public import WeilConjectures.SixFunctors.IntegralDualizingRoosModel
import WeilConjectures.SixFunctors.IntegralDualizingResolvedMappingLimit
import WeilConjectures.Algebra.Homology.RingedSiteGlobalRHomDerivedLimits
import WeilConjectures.Algebra.Homology.RingedSiteGlobalRHomResolvedTowerModels
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Mapping into the canonical integral Roos limit

Source: current blueprint prop-coef-integral-dualizing, second proof paragraph;
Stacks 0B6E, 0D3F and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem complexLimitAdditive
    (A : Type*) [Category A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A] :
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] complexLimitAdditive

private def evaluatedLimitCone
    {A : Type*} [Category A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : Cone I.asFunctor where
  pt := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) |>.obj I
  π :=
    { app := fun n ↦ (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app I
      naturality := by
        intro n m f
        ext q
        change 𝟙 (limit (I.X q)) ≫ limit.π (I.X q) m =
          limit.π (I.X q) n ≫ (I.X q).map f
        rw [Category.id_comp, limit.w] }

private def evaluatedLimitIso
    {A : Type*} [Category A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I ≅
      limit I.asFunctor :=
  (show IsLimit (evaluatedLimitCone I) from
    HomologicalComplex.isLimitOfEval _ _ (fun q ↦ limit.isLimit (I.X q))).conePointUniqueUpToIso
      (limit.isLimit I.asFunctor)

private theorem evaluatedLimitKInjective
    {A : Type*} [Category A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective (limit I.asFunctor) := by
  have : (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).Additive :=
    ⟨fun {_ _} _ _ ↦ rfl⟩
  have := (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ _) ⊣ lim).preservesKInjectiveComplexes
  exact CochainComplex.isKInjective_of_iso (evaluatedLimitIso I)

set_option maxHeartbeats 1200000 in
-- Elaborating the section-scalar Hom bifunctor at both limit endpoints is expensive.
private def resolvedHomLimitIso
    (I : (RingedSiteGlobalRHom.resolvedProperty.{u + 1, u, u}
      (completedIntegralCommRingSheafUnrestricted l E X)).FullSubcategory) :
    (integralDualizingResolvedHom l E X).flip.obj (limit I.obj.asFunctor) ⋙
        DerivedCategory.Q ≅ integralDualizingResolvedHomLimit l E X I.obj := by
  let H := integralDualizingResolvedHom l E X
  have hp (P : (CochainComplex (scalarReductionSource l E X) ℤ)ᵒᵖ) :
      IsIso (limit.post I.obj.asFunctor (H.obj P)) :=
    (RingedSiteGlobalRHom.resolved_tower_models.{u + 1, u, u}
      (completedIntegralCommRingSheafUnrestricted l E X)
      (integralDualizingCoefficients l E) (integralDualizingScalarSections l E X) P.unop).1 I
  refine NatIso.ofComponents
    (fun P ↦ by
      have := hp P
      exact asIso (DerivedCategory.Q.map (limit.post I.obj.asFunctor (H.obj P)))) ?_
  intro P P' f
  change DerivedCategory.Q.map ((H.map f).app (limit I.obj.asFunctor)) ≫
      DerivedCategory.Q.map (limit.post I.obj.asFunctor (H.obj P')) =
    DerivedCategory.Q.map (limit.post I.obj.asFunctor (H.obj P)) ≫
      DerivedCategory.Q.map (lim.map (Functor.whiskerLeft I.obj.asFunctor (H.map f)))
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 1
  apply limit.hom_ext
  intro n
  simp only [Category.assoc, lim_map, limMap_π, limit.post_π_assoc, limit.post_π,
    Functor.whiskerLeft_app]
  exact ((H.map f).naturality (limit.π I.obj.asFunctor n)).symm

private def ambientGlobalHomMapIso
    {M N : DerivedCategory (scalarReductionSource l E X)} (e : M ≅ N) :
    integralDualizingAmbientGlobalHom l E X M ≅ integralDualizingAmbientGlobalHom l E X N :=
  Functor.isoWhiskerRight
    (((Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u}
      (ProEt.topology X) (completedIntegralCommRingSheafUnrestricted l E X))).flip).mapIso e)
    (integralDualizingDerivedSections l E X)

private def ambientMappingTowerMapIso
    {Z W : DerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E X)} (e : Z ≅ W) :
    integralDualizingAmbientMappingTower l E X Z ≅
      integralDualizingAmbientMappingTower l E X W :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (coefHomDerivedConstant l E X).op
      (((Functor.curry.obj (coefHomConstantInternalHom l E X)).flip).mapIso
        ((coefHomEquivalence l E X).inverse.mapDerivedCategory.mapIso e)))
    (coefHomConstantDerivedSections l E X)

set_option linter.unusedSectionVars false in
/-- Global Hom into the canonical limit is computed by the strict mapping tower.

Source: Stacks 0B6E, 0D3F and 0941 (blueprint:
lem-coef-integral-dualizing-mapping-tower-limit-canonical).

Proof: resolve the strict tower by a K-injective complex of injective towers and
apply the global-Hom/derived-limit comparison.  The constant-ring internal-Hom
model identifies the resulting resolved Hom tower with
`integralDualizingMappingTower`; its scalar sections are exactly the prescribed
integral sections.  Products and differentials commute with the ordinary limit,
and the split (hence surjective) transitions identify that ordinary limit with the
Roos-derived limit.  The comparison is natural in the constructible input, so it
assembles to the displayed functor isomorphism.  No finite-level dualizing
identification is used.
(blueprint: lem-coef-integral-dualizing-mapping-tower-limit-canonical). -/
theorem integralDualizing_mapping_tower_limit_canonical
    (T : NormalizedDVRTower l E X D hl) :
    Nonempty (integralDualizingGlobalHom l E X
        ((integralDualizingLimit l E X).obj T.tower) ≅
      integralDualizingMappingTower l E X T.tower ⋙
        CoefTower.totalLimit (integralDualizingCoefficients l E)) := by
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let A := scalarReductionSource l E X
  let C := DerivedCategory.Q.objPreimage T.tower
  obtain ⟨I, q, hq⟩ :=
    (RingedSiteGlobalRHom.preserves_derived_limits.{u + 1, u, u}
      R (integralDualizingCoefficients l E) (integralDualizingScalarSections l E X)
      (DerivedCategory.Q.obj (C.asFunctor.obj (op 0))) (C.asFunctor.obj (op 0))
      (Iso.refl _)).1 C
  have : QuasiIso q := hq
  have : I.obj.IsKInjective := I.property.1
  have : CochainComplex.IsKInjective (limit I.obj.asFunctor) :=
    evaluatedLimitKInjective I.obj
  let eI : DerivedCategory.Q.obj I.obj ≅ T.tower :=
    (asIso (DerivedCategory.Q.map q)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso T.tower
  obtain ⟨η, _, hη, _⟩ :=
    (ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u}
      (ProEt.topology X) (completedIntegralCoefficientSheafUnrestricted l E X)
      (completedIntegralCoefficient_mul_commUnrestricted l E X)).choose_spec
  have : IsIso (η.app I.obj) := hη I.obj I.property.1
  let eLim : DerivedCategory.Q.obj (limit I.obj.asFunctor) ≅
      (integralDualizingLimit l E X).obj T.tower :=
    DerivedCategory.Q.mapIso (evaluatedLimitIso I.obj).symm ≪≫ asIso (η.app I.obj) ≪≫
      (integralDualizingLimit l E X).mapIso eI
  obtain ⟨a⟩ := integralDualizing_resolved_globalHom l E X (limit I.obj.asFunctor)
  obtain ⟨b⟩ := integralDualizing_resolved_mappingLimit l E X I.obj I.property.2
  let e : DerivedCategory.Q.op ⋙
        integralDualizingAmbientGlobalHom l E X
          ((integralDualizingLimit l E X).obj T.tower) ≅
      DerivedCategory.Q.op ⋙ integralDualizingAmbientMappingTower l E X T.tower ⋙
        CoefTower.totalLimit (integralDualizingCoefficients l E) :=
    Functor.isoWhiskerLeft DerivedCategory.Q.op (ambientGlobalHomMapIso l E X eLim).symm ≪≫
      a ≪≫ resolvedHomLimitIso l E X I ≪≫ b.symm ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Q.op
        (Functor.isoWhiskerRight (ambientMappingTowerMapIso l E X eI)
          (CoefTower.totalLimit (integralDualizingCoefficients l E)))
  let e' := (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q.op
    (HomologicalComplex.quasiIso A (.up ℤ)).op
    (DerivedCategory (ModuleCat.{u + 1} (integralDualizingCoefficients l E)))).preimageIso e
  exact ⟨Functor.isoWhiskerLeft (sfIntegralConstructible l E X).ι.op e'⟩

end WeilConjectures
