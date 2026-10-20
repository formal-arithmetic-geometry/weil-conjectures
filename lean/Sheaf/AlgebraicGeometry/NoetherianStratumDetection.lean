/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.ModuleInverseImageAdjunction
import Sheaf.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-!
# Detection by pro-etale covers of finitely many locally closed strata

Source: Stacks Project, Tags 09AH and 09AB, followed by finite-stratum induction
(blueprint: lem-weil-pbc-noetherian-stratum-detection).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable def modelSheafEquivalence (X : Scheme.{u})
    (D : Type*) [Category.{u + 1} D] :
    Sheaf (proEtaleModelTopology X) D ≌ Sheaf (ProEt.topology X) D :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).sheafPushforwardContinuous
      D (ProEt.topology X) (proEtaleModelTopology X))
    ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      D (proEtaleModelTopology X) (ProEt.topology X))
    (Iso.refl _) (Iso.refl _)

@[irreducible] private noncomputable def modelAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type*) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology X) D] :
    (modelSheafEquivalence Y D).functor ⋙ proEtaleSheafInverseImage f D ⋙
      (modelSheafEquivalence X D).inverse ⊣
        (proEtaleModelBaseChange f).sheafPushforwardContinuous D
          (proEtaleModelTopology Y) (proEtaleModelTopology X) :=
  (proEtaleSheafAdjunction f D).restrictFullyFaithful
    (modelSheafEquivalence Y D).fullyFaithfulFunctor
    (modelSheafEquivalence X D).fullyFaithfulFunctor (Iso.refl _) (Iso.refl _)

private theorem modelRingAdjunction_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    (modelAdjunction f RingCat.{u + 1}).unit.app
        ((modelSheafEquivalence Y RingCat.{u + 1}).inverse.obj R) =
      proEtaleRingModelUnit f R := by
  apply (modelSheafEquivalence Y RingCat.{u + 1}).functor.map_injective
  rw [modelAdjunction, Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Iso.refl_hom, NatTrans.id_app]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ringModelPresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    let A := (modelSheafEquivalence Y RingCat.{u + 1}).inverse.obj R
    let B := (modelSheafEquivalence X RingCat.{u + 1}).inverse.obj
      ((proEtaleSheafInverseImage f RingCat.{u + 1}).obj R)
    ∃ p : SheafPullbackUnitPresentation (F := proEtaleModelBaseChange f)
      ((sheafCompose (proEtaleModelTopology Y) (CategoryTheory.forget RingCat.{u + 1})).obj A)
      ((sheafCompose (proEtaleModelTopology X) (CategoryTheory.forget RingCat.{u + 1})).obj B),
      p.unit = (sheafCompose (proEtaleModelTopology Y) (CategoryTheory.forget RingCat.{u + 1})).map
        (proEtaleRingModelUnit f R) := by
  let F := proEtaleModelBaseChange f
  let J := proEtaleModelTopology Y
  let K := proEtaleModelTopology X
  let A := (modelSheafEquivalence Y RingCat.{u + 1}).inverse.obj R
  let B := (modelSheafEquivalence X RingCat.{u + 1}).inverse.obj
    ((proEtaleSheafInverseImage f RingCat.{u + 1}).obj R)
  let : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsEquivalence
  let : PreservesFiniteLimits F := by
    dsimp [F, proEtaleModelBaseChange]
    infer_instance
  let : RepresentablyFlat F := flat_of_preservesFiniteLimits F
  let e := (modelAdjunction f RingCat.{u + 1}).leftAdjointUniq
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F RingCat.{u + 1} J K)
  let c := sheafPullbackForgetIso J K F (CategoryTheory.forget RingCat.{u + 1})
  let iso : (sheafCompose K (CategoryTheory.forget RingCat.{u + 1})).obj B ≅
      (Functor.sheafPullbackConstruction.sheafPullback F (Type (u + 1)) J K).obj
        ((sheafCompose J (CategoryTheory.forget RingCat.{u + 1})).obj A) :=
    (sheafCompose K (CategoryTheory.forget RingCat.{u + 1})).mapIso (e.app A) ≪≫ c.app A
  let unit := (sheafCompose J (CategoryTheory.forget RingCat.{u + 1})).map
    (proEtaleRingModelUnit f R)
  refine ⟨⟨unit, iso, ?_⟩, rfl⟩
  intro U r
  have he := Adjunction.unit_leftAdjointUniq_hom_app (modelAdjunction f RingCat.{u + 1})
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F RingCat.{u + 1} J K) A
  have hc := sheafPullbackForgetIso_unit J K F (CategoryTheory.forget RingCat.{u + 1}) A
  have ht := modelRingAdjunction_unit f R
  have ht' := congrArg (fun z ↦ z.hom.app U) ht
  have htr : ((modelAdjunction f RingCat.{u + 1}).unit.app A).hom.app U r =
      unit.hom.app U r :=
    ConcreteCategory.congr_hom ht' r
  have he' := congrArg (fun z ↦ z.hom.app U) he
  have he0 := ConcreteCategory.congr_hom he' r
  have hc' := congrArg (fun z ↦ z.hom.app U) hc
  have hc0 := ConcreteCategory.congr_hom hc' r
  change (c.hom.app A).hom.app (F.op.obj U)
      ((e.hom.app A).hom.app (F.op.obj U) (unit.hom.app U r)) = _
  exact (congrArg (fun t ↦ (c.hom.app A).hom.app (F.op.obj U)
      ((e.hom.app A).hom.app (F.op.obj U) t)) htr.symm).trans
    ((congrArg (fun t ↦ (c.hom.app A).hom.app (F.op.obj U) t) he0).trans hc0)

private noncomputable def modelAbelianPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (modelSheafEquivalence Y AddCommGrpCat.{u + 1}).inverse ⋙
      Functor.sheafPullbackConstruction.sheafPullback (proEtaleModelBaseChange f)
        AddCommGrpCat.{u + 1} (proEtaleModelTopology Y) (proEtaleModelTopology X) ⋙
      (modelSheafEquivalence X AddCommGrpCat.{u + 1}).functor ≅
        proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} := by
  let a := modelAdjunction f AddCommGrpCat.{u + 1}
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proEtaleModelBaseChange f) AddCommGrpCat.{u + 1}
      (proEtaleModelTopology Y) (proEtaleModelTopology X)
  exact Functor.isoWhiskerLeft (modelSheafEquivalence Y AddCommGrpCat.{u + 1}).inverse
    (Functor.isoWhiskerRight (b.leftAdjointUniq a)
      (modelSheafEquivalence X AddCommGrpCat.{u + 1}).functor)

private theorem ringInverseImageUnderlying {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    Nonempty (proEtaleRingModuleInverseImage f R ⋙ SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf R ⋙ proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}) := by
  let : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsEquivalence
  let : PreservesFiniteLimits (proEtaleModelBaseChange f) := by
    dsimp [proEtaleModelBaseChange]
    infer_instance
  let : RepresentablyFlat (proEtaleModelBaseChange f) := flat_of_preservesFiniteLimits _
  obtain ⟨p, hp⟩ := ringModelPresentation f R
  obtain ⟨e, _⟩ := SheafOfModules.inverseImage_underlying_of_ring_presentation
    (proEtaleRingModelUnit f R) p hp
  let B := (proEtaleSheafInverseImage f RingCat.{u + 1}).obj R
  let L := SheafOfModules.pullback (proEtaleRingModelUnit f R)
  let La := Functor.sheafPullbackConstruction.sheafPullback (proEtaleModelBaseChange f)
    AddCommGrpCat.{u + 1} (proEtaleModelTopology Y) (proEtaleModelTopology X)
  let t : proEtaleModuleToModel R ⋙ SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf R ⋙
        (modelSheafEquivalence Y AddCommGrpCat.{u + 1}).inverse :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl)
  let q : proEtaleModuleFromModel B ⋙ SheafOfModules.toSheaf B ≅
      SheafOfModules.toSheaf _ ⋙
        (modelSheafEquivalence X AddCommGrpCat.{u + 1}).functor :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl)
  exact ⟨Functor.isoWhiskerLeft (proEtaleModuleToModel R ⋙ L) q ≪≫
    Functor.isoWhiskerLeft (proEtaleModuleToModel R)
      (Functor.isoWhiskerRight e (modelSheafEquivalence X AddCommGrpCat.{u + 1}).functor) ≪≫
    Functor.isoWhiskerRight t
      (La ⋙ (modelSheafEquivalence X AddCommGrpCat.{u + 1}).functor) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf R) (modelAbelianPullbackIso f)⟩

/-- Module inverse image over its actual inverse-image ring is exact, including for
noncommutative rings. Source: Stacks, Tag 04JC, first assertion, and Tag 03DA
(blueprint: lem-weil-pbc-noetherian-stratum-detection).
Proof: apply sitePullback_abelian_exact to the underlying abelian inverse image.
The module action is the inverse image of the original action under the finite-product
comparison. Module kernels and cokernels have the underlying abelian kernels and
cokernels, so this functor preserves both; its maps preserve addition. No change to
an independently chosen coefficient ring, or flatness assumption, is involved. -/
theorem proEtaleRingModuleInverseImage_exact {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    (proEtaleRingModuleInverseImage f R).Additive ∧
    PreservesFiniteLimits (proEtaleRingModuleInverseImage f R) ∧
    PreservesFiniteColimits (proEtaleRingModuleInverseImage f R) := by
  let L := proEtaleRingModuleInverseImage f R
  let V := SheafOfModules.toSheaf.{u + 1}
    ((proEtaleSheafInverseImage f RingCat.{u + 1}).obj R)
  let : (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).Additive := ⟨by
    intros
    ext U
    rfl⟩
  let : (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).Additive :=
    (proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).left_adjoint_additive
  let : RepresentablyFlat (proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  let : PreservesFiniteLimits (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}) :=
    inferInstance
  let : PreservesColimitsOfSize.{0, 0}
      (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}) :=
    (proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).leftAdjoint_preservesColimits
  obtain ⟨e⟩ := ringInverseImageUnderlying f R
  let : (L ⋙ V).Additive := Functor.additive_of_iso e.symm
  let : L.Additive := Functor.additive_of_comp_faithful L V
  let : ReflectsFiniteLimits V := reflectsFiniteLimits_of_reflectsIsomorphisms V
  let : PreservesFiniteLimits (L ⋙ V) := preservesFiniteLimits_of_natIso e.symm
  let : PreservesFiniteLimits L := preservesFiniteLimits_of_reflects_of_preserves L V
  let : PreservesFiniteColimits (L ⋙ V) := preservesFiniteColimits_of_natIso e.symm
  let : PreservesFiniteColimits L := preservesFiniteColimits_of_reflects_of_preserves L V
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Additivity of inverse image. Source: Stacks, Tag 04JC
(blueprint: lem-weil-pbc-noetherian-stratum-detection). -/
noncomputable instance proEtaleRingModuleInverseImage_additive {X Y : Scheme.{u}}
    (f : X ⟶ Y) (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    (proEtaleRingModuleInverseImage f R).Additive :=
  (proEtaleRingModuleInverseImage_exact f R).1

/-- Left exactness of inverse image. Source: Stacks, Tag 04JC
(blueprint: lem-weil-pbc-noetherian-stratum-detection). -/
noncomputable instance proEtaleRingModuleInverseImage_preservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    PreservesFiniteLimits (proEtaleRingModuleInverseImage f R) :=
  (proEtaleRingModuleInverseImage_exact f R).2.1

/-- Right exactness of inverse image. Source: Stacks, Tag 04JC
(blueprint: lem-weil-pbc-noetherian-stratum-detection). -/
noncomputable instance proEtaleRingModuleInverseImage_preservesFiniteColimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    PreservesFiniteColimits (proEtaleRingModuleInverseImage f R) :=
  (proEtaleRingModuleInverseImage_exact f R).2.2

/-- The ordinary localization at quasi-isomorphisms for modules over any ring sheaf.
Source: Stacks, Tag 05RU (blueprint: lem-weil-pbc-noetherian-stratum-detection). -/
noncomputable instance proEtaleAllRingModules_hasDerivedCategory (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    HasDerivedCategory (ringedSiteModules.{u + 1} R) :=
  HasDerivedCategory.standard _

/-- The canonical termwise inverse image on the unbounded derived category, with
coefficients the inverse-image ring. This is Mathlib's exact-functor localization.
Source: Stacks, Tag 015F (blueprint: lem-weil-pbc-noetherian-stratum-detection). -/
noncomputable abbrev proEtaleAllRingDerivedInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :=
  (proEtaleRingModuleInverseImage f R).mapDerivedCategory

/-- Abelian sheaves are detected by the chosen pro-etale covers of all strata.
Source: Stacks, Tags 09AH and 09AB, and finite-stratum induction
(blueprint: lem-weil-pbc-noetherian-stratum-detection).
Proof: adjunction and the sectionwise base-change formula for direct image identify
successive inverse images with inverse image along the composite, including identities.
For a covering, localization identifies inverse image with slice restriction; the sheaf
separatedness axiom on base-changed covers detects zero sections. Thus covering
restrictions detect zero sheaves. Induct on the number of nonempty strata. The empty
scheme has only zero abelian sheaves by the empty-cover axiom. Factor each stratum as a
closed immersion into an open neighborhood. Those neighborhoods cover X. Their open
complements are Noetherian and their open inclusions are quasi-compact. Base change the
remaining strata to the complement and discard the empty chosen stratum; induction
makes the restriction there zero. The closed restriction is also zero. The exact
open/closed sequence of Tag 09AH gives zero on each neighborhood; covering detection
gives zero globally. Actual immersion structures are retained, also for nonreduced strata.
The constant integer sheaf action allows use of module localization and detection. -/
theorem proEtale_isZero_of_stratum_cover (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X] (S : Stratification X)
    (V : ∀ a : Fin S.n, Scheme.Cover.{w} proetalePrecoverage (S.domain a))
    (F : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1})
    (hF : ∀ (a : Fin S.n) (j : (V a).I₀),
      IsZero ((proEtaleSheafInverseImage ((V a).f j ≫ S.immersion a)
        AddCommGrpCat.{u + 1}).obj F)) : IsZero F := by
  -- Finite quasi-compact joint detection applies directly to the actual immersions.
  have : IsNoetherian X := {}
  have hstr (a : Fin S.n) :
      IsZero ((proEtaleSheafInverseImage (S.immersion a) AddCommGrpCat.{u + 1}).obj F) := by
    let G := (proEtaleSheafInverseImage (S.immersion a) AddCommGrpCat.{u + 1}).obj F
    let := HasZeroObject.zero'
      (Sheaf (ProEt.topology (S.domain a)) AddCommGrpCat.{u + 1})
    let : ∀ j, WeaklyEtale ((V a).f j) :=
      (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1 (V a).mem₀.2 |>.2
    have hz (j : (V a).I₀) :
        IsZero ((AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1}
          ((V a).f j)).obj G) :=
      (hF a j).of_iso ((AlgebraicGeometry.ProEtale.upperStarComp
        AddCommGrpCat.{u + 1} ((V a).f j) (S.immersion a)).symm.app F)
    have : IsIso (0 : G ⟶ 0) := by
      refine AlgebraicGeometry.ProEtale.isIso_of_isIso_localizationRestriction
        AddCommGrpCat.{u + 1} (0 : G ⟶ 0) (V a).f (V a).mem₀ fun j ↦ ?_
      let e := AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction
        AddCommGrpCat.{u + 1} ((V a).f j) inferInstance
      exact isIso_of_source_target_iso_zero _ ((hz j).of_iso (e.app G).symm).isoZero
        (((AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1}
          ((V a).f j)).map_isZero (isZero_zero _)).of_iso (e.app 0).symm).isoZero
    exact (isZero_zero _).of_iso (asIso (0 : G ⟶ 0))
  have : ∀ a : Fin S.n, TopologicalSpace.NoetherianSpace (S.domain a) := fun a ↦
    (S.immersion a).isEmbedding.noetherianSpace
  have : ∀ a : Fin S.n, QuasiCompact (S.immersion a) := fun a ↦ inferInstance
  rw [IsZero.iff_id_eq_zero]
  apply AlgebraicGeometry.ProEtale.abDetectMaps S.immersion
  · intro x
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
    exact ⟨a, (S.range_immersion a).symm ▸ ha⟩
  · intro a
    rw [(AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1}
      (S.immersion a)).map_id]
    exact (hstr a).eq_of_src _ _

/-- These exact termwise restrictions jointly detect zero objects and isomorphisms
in the unbounded derived category of modules over every ring sheaf.
Source: Stacks, Tags 09AH, 05RU, 015F and 0149, and finite-stratum induction
(blueprint: lem-weil-pbc-noetherian-stratum-detection).
Proof: exactness identifies the cohomology of each restricted complex with the
restriction of its cohomology. Apply proEtale_isZero_of_stratum_cover to the underlying
abelian cohomology sheaves in every integer degree. A complex with zero cohomology
becomes zero in the localization, because its map from the zero complex is a
quasi-isomorphism. This detects zero without a boundedness condition. For a morphism,
complete it to a distinguished triangle. Exact termwise restriction is triangulated.
If all restricted morphisms are invertible, all restricted cones have zero cohomology
and hence are zero. Joint zero detection makes the global cone zero. Exactness of
Hom(W,-) on this triangle and its rotations makes Hom(W,f) bijective for every W;
taking W to be its target and source supplies a two-sided inverse. Conversely, additive
functors preserve zero objects and all functors preserve isomorphisms. Composite
restrictions agree canonically with successive stratum and cover restrictions by the
adjunction composition formula, so the composite notation includes precisely the
inverse images in the informal statement. -/
theorem proEtale_derived_stratum_cover_detection (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X] (S : Stratification X)
    (V : ∀ a : Fin S.n, Scheme.Cover.{w} proetalePrecoverage (S.domain a))
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    (∀ K : DerivedCategory (ringedSiteModules.{u + 1} R),
      (∀ (a : Fin S.n) (j : (V a).I₀),
        IsZero ((proEtaleAllRingDerivedInverseImage
          ((V a).f j ≫ S.immersion a) R).obj K)) → IsZero K) ∧
    (∀ (K L : DerivedCategory (ringedSiteModules.{u + 1} R)) (f : K ⟶ L),
      (∀ (a : Fin S.n) (j : (V a).I₀),
        IsIso ((proEtaleAllRingDerivedInverseImage
          ((V a).f j ≫ S.immersion a) R).map f)) → IsIso f) := by
  have hmodule (M : ringedSiteModules.{u + 1} R)
      (hM : ∀ (a : Fin S.n) (j : (V a).I₀),
        IsZero ((proEtaleRingModuleInverseImage
          ((V a).f j ≫ S.immersion a) R).obj M)) : IsZero M := by
    have hz : IsZero ((SheafOfModules.toSheaf R).obj M) := by
      apply proEtale_isZero_of_stratum_cover X S V
      intro a j
      obtain ⟨e⟩ := ringInverseImageUnderlying ((V a).f j ≫ S.immersion a) R
      exact ((SheafOfModules.toSheaf _).map_isZero (hM a j)).of_iso (e.app M).symm
    apply (IsZero.iff_id_eq_zero M).2
    apply (SheafOfModules.toSheaf R).map_injective
    simpa using hz.eq_of_src ((SheafOfModules.toSheaf R).map (𝟙 M))
      ((SheafOfModules.toSheaf R).map (0 : M ⟶ M))
  have hzero (K : DerivedCategory (ringedSiteModules.{u + 1} R))
      (hK : ∀ (a : Fin S.n) (j : (V a).I₀),
        IsZero ((proEtaleAllRingDerivedInverseImage
          ((V a).f j ≫ S.immersion a) R).obj K)) : IsZero K := by
    apply DerivedCategory.isZero_of_forall_isZero_homology
    intro q
    apply hmodule
    intro a j
    let P := proEtaleRingModuleInverseImage ((V a).f j ≫ S.immersion a) R
    exact ((DerivedCategory.homologyFunctor _ q).map_isZero (hK a j)).of_iso
      ((P.mapDerivedCategoryHomologyFunctorIso q).app K)
  refine ⟨hzero, ?_⟩
  intro K L f hf
  obtain ⟨C, g, h, hT⟩ := CategoryTheory.Pretriangulated.distinguished_cocone_triangle f
  apply (CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).1
  apply hzero
  intro a j
  let P := proEtaleAllRingDerivedInverseImage ((V a).f j ≫ S.immersion a) R
  exact (CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
    (P.map_distinguished _ hT)).2 (hf a j)

end AlgebraicGeometry.Scheme

