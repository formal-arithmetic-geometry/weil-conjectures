/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.CompactifiableOverField
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.KInjectiveResolutions
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.UnboundedProperOpenInterchangeSupplement
import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportNormalization
import WeilConjectures.AlgebraicGeometry.UnboundedProperOpenPastingSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-!
# Unbounded compact supports composed with proper direct image

Source: Stacks Project, More on Étale Cohomology, Tags 0F7H, 0F7I, 0F7J and 0F7B (b)
(blueprint: lem-sf-unbounded-compact-support-proper-composition).

Blueprint use: the first paragraph of the proof of `lem-weil-delta-proper-pushforward`,
where composition of the ambient right adjoints identifies the dualizing objects, followed
by the sentence asserting `Rf_! = Rf_*` for proper `f`. The composition comparison and its
proper normalization below supply precisely these inputs.

The candidates, proper/open tower map and common-refinement comparisons are the existing
ordinary small-etale constructions. Two definitions assemble the proper normalization and
its composition comparison. The three statements specify arbitrary proper refinements,
their K-injective representatives and coherence, and normalization on every tower.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Compare a compact-support candidate for a proper morphism with its ordinary direct image,
using the trivial compactification and the canonical identity-open isomorphism.
Source: Stacks Project, Tag 0F7H
(blueprint: lem-sf-unbounded-compact-support-proper-composition). -/
noncomputable def unboundedEtaleProperCandidateIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      R((f)_*[ModuleCat.{u + 1} A]) :=
  rightDerivedLowerShriekOfCompactificationIso A c (Compactification.ofIsProper f) ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
        (Adjunction.leftAdjointIdIso
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
          (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
        Functor.mapDerivedCategoryIdIso _) _ ≪≫
      Functor.leftUnitor _

/-- The proper-input composition comparison, assembled from the closure tower `c.ofComp d`,
the inverse proper normalization on its restricted compactification, the existing proper/open
tower map, and the common-refinement comparison to the requested output compactification.
Source: Stacks Project, Tag 0F7J
(blueprint: lem-sf-unbounded-compact-support-proper-composition). -/
noncomputable def unboundedEtaleProperCompositionIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsProper f] [QuasiCompact g]
    (d : Compactification g) (c : Compactification (f ≫ g)) :
    R((f)_*[ModuleCat.{u + 1} A]) ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  Functor.isoWhiskerRight (unboundedEtaleProperCandidateIso A f (c.ofComp d).restrict).symm
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d) ≪≫
    rightDerivedLowerShriekOfCompactificationCompIso A d (c.ofComp d) ≪≫
      rightDerivedLowerShriekOfCompactificationIso A (d.comp (c.ofComp d)) c

section NormalizationModels
universe w₁ w₂ v₁ v₂ u₁ u₂
open CategoryTheory.Abelian CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  [HasKInjectiveResolutions C]
omit [HasKInjectiveResolutions C] in
private lemma exact_factor_Q (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (J : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient C (.up ℤ)).obj J) ≫
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app J) ≫
      F.mapDerivedCategoryFactors.hom.app J =
    (DerivedCategory.quotientCompQhIso D).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj J) := by
  have he : F.mapDerivedCategoryFactorsh.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj J) =
    F.mapDerivedCategory.mapIso ((DerivedCategory.quotientCompQhIso C).app J) ≪≫
      F.mapDerivedCategoryFactors.app J ≪≫
        ((DerivedCategory.quotientCompQhIso D).app
          ((F.mapHomologicalComplex (.up ℤ)).obj J)).symm := by
    apply Iso.ext
    simp only [Iso.app_hom, Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
      Functor.mapDerivedCategoryFactorsh_hom_app, Functor.mapHomotopyCategoryFactors,
      Quotient.lift.isLift_inv]
    erw [DerivedCategory.Qh.map_id, Category.comp_id]
    rfl
  have hi := congrArg Iso.inv he
  change F.mapDerivedCategoryFactorsh.inv.app _ = _ at hi
  rw [hi]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv,
    Iso.app_hom, Category.assoc, ]
  rw [← F.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app, F.mapDerivedCategory.map_id,
    Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
universe w₃ v₃ u₃
variable {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory.{w₃} E]

omit [HasKInjectiveResolutions C] in
private lemma comparison_complex_fac
    [HasKInjectiveResolutions D]
    (S : C ⥤ E) (O : C ⥤ D) (R : D ⥤ E)
    [S.Additive] [O.Additive] [R.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    (a : S ⟶ O ⋙ R)
    (σ : S.mapDerivedCategory ⟶ O.mapDerivedCategory ⋙ R.rightDerivedFunctor)
    (hσ : ∀ K : HomotopyCategory C (.up ℤ),
      σ.app (DerivedCategory.Qh.obj K) =
        S.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).app K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ R)) (.up ℤ)).inv.app K) ≫
        R.rightDerivedFunctorUnit.app ((O.mapHomotopyCategory (.up ℤ)).obj K) ≫
        R.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.inv.app K))
    (J : CochainComplex C ℤ) :
    σ.app (DerivedCategory.Q.obj J) ≫
        R.rightDerivedFunctor.map (O.mapDerivedCategoryFactors.hom.app J) =
      S.mapDerivedCategoryFactors.hom.app J ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).app J) ≫
        R.rightDerivedFunctorUnitQ ((O.mapHomologicalComplex (.up ℤ)).obj J) := by
  let q := DerivedCategory.quotientCompQhIso C
  have hn := σ.naturality (q.hom.app J)
  simp only [Functor.comp_map] at hn
  rw [← cancel_epi (S.mapDerivedCategory.map (q.hom.app J))]
  rw [reassoc_of% hn, hσ]
  simp only [Category.assoc]
  slice_lhs 5 7 =>
    rw [← R.rightDerivedFunctor.map_comp_assoc, ← R.rightDerivedFunctor.map_comp,
      Category.assoc, exact_factor_Q O J]
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  have hc : (Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ R)) (.up ℤ)
      ).inv.app ((HomotopyCategory.quotient _ (.up ℤ)).obj J) = 𝟙 _ := by
    rw [← cancel_epi ((Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ R)) (.up ℤ)
      ).hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj J))]
    rw [Iso.hom_inv_id_app, Functor.mapHomotopyCategoryCompIso_refl_hom_app]
    exact (Category.comp_id _).symm
  rw [hc]
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
  erw [DerivedCategory.Qh.map_id, Category.id_comp, DerivedCategory.Qh.map_id,
    Category.id_comp]
  have ha : (a.mapHomotopyCategory (.up ℤ)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj J) =
    (HomotopyCategory.quotient _ (.up ℤ)).map
      ((a.mapHomologicalComplex (.up ℤ)).app J) := rfl
  erw [ha, DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  simp only [Category.assoc]
  rfl

end NormalizationModels

private lemma compactification_comparison_mono_aux
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    {U X : Scheme.{u}} {f : U ⟶ X} (c : Compactification f)
    (M : Sheaf U.smallEtaleTopology B)
    (hM : Mono ((openImmersionLowerShriekToLowerStar B c.i).app M)) :
    Mono ((lowerStar B c.g).map ((openImmersionLowerShriekToLowerStar B c.i).app M) ≫
      (lowerStarComp B c.i c.g f c.comm).hom.app M) := by
  let := hM
  infer_instance

private lemma compactification_comparison_mono (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} {f : U ⟶ X} (c : Compactification f)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Mono ((compactificationSheafToDirectImage A c).app M) :=
  compactification_comparison_mono_aux (ModuleCat.{u + 1} A) c M
    (mono_openImmersionLowerShriekToLowerStar_app A c.i M)

private lemma theta_normalization
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B]
    {X C D : Scheme.{u}} (j : X ⟶ C) (q : C ⟶ D) (k : X ⟶ D)
    [IsOpenImmersion j] [IsOpenImmersion k] (hk : j ≫ q = k)
    (θ : lowerStar B (𝟙 X) ⋙ openImmersionLowerShriek B k ≅
      openImmersionLowerShriek B j ⋙ lowerStar B q)
    (hθ : ∀ M, θ.hom.app M ≫
      (lowerStar B q).map ((openImmersionLowerShriekToLowerStar B j).app M) ≫
      (lowerStarComp B j q).hom.app M =
        (openImmersionLowerShriekToLowerStar B k).app ((lowerStar B (𝟙 X)).obj M) ≫
        (lowerStarComp B (𝟙 X) k (j ≫ q) (by simp [hk])).hom.app M)
    (M : Sheaf X.smallEtaleTopology B) :
    (openImmersionLowerShriek B k).map ((lowerStarId B X).inv.app M) ≫
      θ.hom.app M ≫
      (lowerStar B q).map ((openImmersionLowerShriekToLowerStar B j).app M) ≫
      (lowerStarComp B j q k hk.symm).hom.app M =
        (openImmersionLowerShriekToLowerStar B k).app M := by
  subst k
  rw [hθ, lowerStarComp_id_left]
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  rw [← (openImmersionLowerShriekToLowerStar B (j ≫ q)).naturality_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  dsimp only [Functor.id_obj]
  erw [Category.comp_id]

private lemma open_sheaf_comparison
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    {U Z : Scheme.{u}} (k : U ⟶ Z) [IsOpenImmersion k]
    (M : Sheaf U.smallEtaleTopology B) :
    etaleLowerShriekToLowerStar B k M =
      (openImmersionLowerShriekToLowerStar B k).app M := by
  have he : (lowerStarUnit B k).app M =
      inv ((openImmersionRestrictionLowerStarAdjunction B k).counit.app M) := by
    apply (cancel_mono ((openImmersionRestrictionLowerStarAdjunction B k).counit.app M)).1
    rw [IsIso.inv_hom_id]
    exact congr_app (lowerStarUnit_comp_counit B k) M
  rw [etaleLowerShriekToLowerStar, etaleLowerShriekRestrictionAdjunction,
    etaleLowerShriekUpperStarAdjunction]
  rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply,
    Adjunction.homEquiv_ofNatIsoRight_symm_apply]
  simp only [Iso.symm_inv, Category.assoc, ]
  rw [he, Adjunction.homEquiv_counit]
  rw [openImmersionLowerShriekToLowerStar_app]
  simp only [ Iso.inv_hom_id_app, Category.comp_id,
    NatIso.isIso_inv_app]
  rfl


/-- Every proper refinement is specified by the sheaf identification that is the identity
on the source open, and by the prescribed map on every K-injective representative.
Source: Stacks Project, Tags 0F7B (b) and 0F7I
(blueprint: lem-sf-unbounded-compact-support-proper-composition).

Proof: step 1 of the node gives Noetherianity from finite type over the field and properness
of each ambient. In step 2 apply lem-amb-unbounded-proper-open-interchange to the square with
left map the identity and right map the refinement. Its sheaf support normalization gives
exactly theta below. Its representative formula, after the identity direct image is removed,
gives gamma on every K-injective J and every resolution of its open extension. Compose with
the canonical derived direct-image compositor of
lem-weil-pbc-ringed-topoi-derived-pushforward-composition. Step 3 identifies the result with
the existing common-refinement comparison using
lem-amb-unbounded-compact-support-comparisons. No cartesianness or density is assumed. -/
theorem unboundedEtaleProperRefinement_normalization
    (k : Type u) [Field k] (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    {c d : Compactification h} (r : c.Refinement d) :
    ∃ (θ : (d.i)_!open[ModuleCat.{u + 1} A] ≅
        (c.i)_!open[ModuleCat.{u + 1} A] ⋙ (r.hom)_*[ModuleCat.{u + 1} A])
      (γ : D((d.i)_!open[ModuleCat.{u + 1} A]) ≅
        D((c.i)_!open[ModuleCat.{u + 1} A]) ⋙ R((r.hom)_*[ModuleCat.{u + 1} A])),
      (∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
        θ.hom.app F ≫
            (r.hom)_*[ModuleCat.{u + 1} A].map
              ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) c.i r.hom d.i r.i_hom.symm).hom.app F =
          (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) d.i).app F) ∧
      (∀ (J : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [J.IsKInjective]
        (I : CochainComplex (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [I.IsKInjective]
        (ρ : ((c.i)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
        [QuasiIso ρ],
        γ.hom.app (DerivedCategory.Q.obj J) ≫
            R((r.hom)_*[ModuleCat.{u + 1} A]).map
              (((c.i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J ≫
                DerivedCategory.Q.map ρ) ≫
            (((r.hom)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso I).hom =
          ((d.i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J ≫
            DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app J) ≫
            DerivedCategory.Q.map
              (((r.hom)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).map ρ)) ∧
      (rightDerivedLowerShriekOfCompactificationIso A d c).hom =
        Functor.whiskerRight γ.hom R((d.g)_*[ModuleCat.{u + 1} A]) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft D((c.i)_!open[ModuleCat.{u + 1} A])
            (Functor.rightDerivedFunctorCompIso'
              ((r.hom)_*[ModuleCat.{u + 1} A]) ((d.g)_*[ModuleCat.{u + 1} A])
              (lowerStarComp (ModuleCat.{u + 1} A) r.hom d.g c.g r.hom_g.symm)).hom := by
  classical
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsNoetherian X := ⟨⟩
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : IsNoetherian Y := ⟨⟩
  let : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  let : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  let : IsNoetherian c.Z := ⟨⟩
  let : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  let : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  let : IsNoetherian d.Z := ⟨⟩
  let B := ModuleCat.{u + 1} A
  let N := canonicalEtaleCompactSupportNormalization A
  let sq : CommSq c.i (𝟙 X) r.hom d.i := ⟨by simpa using r.i_hom⟩
  obtain ⟨θ₀, Γ, hθ₀, _⟩ := unboundedProperOpenInterchange A
  let θ : (d.i)_!open[B] ≅ (c.i)_!open[B] ⋙ (r.hom)_*[B] :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (lowerStarId B X).symm _ ≪≫ θ₀ c.i (𝟙 X) r.hom d.i sq
  let γ := unboundedEtaleRefinementOpenComparison A r N
  have hθ (F : Sheaf X.smallEtaleTopology B) :
      θ.hom.app F ≫ (r.hom)_*[B].map
          ((openImmersionLowerShriekToLowerStar B c.i).app F) ≫
        (lowerStarComp B c.i r.hom d.i r.i_hom.symm).hom.app F =
      (openImmersionLowerShriekToLowerStar B d.i).app F := by
    simpa only [θ, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_inv_app,
      Category.id_comp, Category.assoc] using
      theta_normalization B c.i r.hom d.i r.i_hom
        (θ₀ c.i (𝟙 X) r.hom d.i sq) (hθ₀ c.i (𝟙 X) r.hom d.i sq) F
  have hs : N.sheafComparison d.i (refinementOpenCompactification r) = θ.hom := by
    apply NatTrans.ext
    funext F
    have := compactification_comparison_mono A (refinementOpenCompactification r) F
    apply (cancel_mono
      ((compactificationSheafToDirectImage A (refinementOpenCompactification r)).app F)).1
    rw [N.sheaf_normalization, open_sheaf_comparison]
    exact (hθ F).symm
  refine ⟨θ, γ, hθ, ?_, ?_⟩
  · intro J hJ I hI ρ hρ
    let := hJ
    let := hI
    let := hρ
    have hfac := comparison_complex_fac
      (C := Sheaf X.smallEtaleTopology B) (D := Sheaf c.Z.smallEtaleTopology B)
      (E := Sheaf d.Z.smallEtaleTopology B)
      (d.i)_!open[B] (c.i)_!open[B] (r.hom)_*[B] θ.hom γ.hom
      (fun K ↦ by
        change (N.comparison d.i (refinementOpenCompactification r)).inv.app _ = _
        rw [N.derived_normalization, hs]
        rfl) J
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hfac]
    rw [← reassoc_of% (Functor.rightDerivedFunctorUnitQ_naturality (r.hom)_*[B] ρ)]
    dsimp only [B, refinementOpenCompactification]
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    erw [Iso.inv_hom_id, Category.comp_id]
  · exact unboundedEtaleCompactSupport_refinement_normalization A h r N


/-- Identity, cocycle and arbitrary-common-refinement independence of the normalized
comparison. Together with the preceding representative formula these give identity and
composition for all proper refinements, including noncartesian ones.
Source: Stacks Project, Tag 0F7I
(blueprint: lem-sf-unbounded-compact-support-proper-composition).

Proof: apply step 3 of the node, namely the comparison coherence of
lem-amb-unbounded-compact-support-comparisons. The preceding normalization identifies every
proper-refinement comparison with the existing pairwise comparison. The identity and cocycle
equations therefore imply identity and composition for refinements. Apply the cocycle to any
common refinement and cancel its invertible factor; the resulting pairwise map is independent
of both the common refinement and its arrows. -/
theorem unboundedEtaleProperRefinement_coherence
    (k : Type u) [Field k] (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    : (∀ c : Compactification h,
      rightDerivedLowerShriekOfCompactificationIso A c c = Iso.refl _) ∧
      (∀ c d e : Compactification h,
        rightDerivedLowerShriekOfCompactificationIso A c d ≪≫
          rightDerivedLowerShriekOfCompactificationIso A d e =
            rightDerivedLowerShriekOfCompactificationIso A c e) ∧
      (∀ (c d e : Compactification h) (_r : e.Refinement c) (_s : e.Refinement d),
        (rightDerivedLowerShriekOfCompactificationIso A c e).hom ≫
            (rightDerivedLowerShriekOfCompactificationIso A d e).inv =
          (rightDerivedLowerShriekOfCompactificationIso A c d).hom) := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsNoetherian X := ⟨⟩
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : IsNoetherian Y := ⟨⟩
  obtain ⟨hid, hcomp⟩ := unboundedEtaleCompactSupport_comparison_coherence A h
  refine ⟨hid, hcomp, ?_⟩
  intro c d e _r _s
  have hc := congrArg Iso.hom (hcomp c d e)
  simp only [Iso.trans_hom] at hc
  rw [← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]


private lemma proper_candidate_chosen
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [HasCompactification f] (c : Compactification f) :
    unboundedEtaleProperCandidateIso A f c =
      rightDerivedLowerShriekIso A c ≪≫ (rightDerivedLowerShriekIso A
        (Compactification.ofIsProper f)).symm ≪≫
          unboundedEtaleProperCandidateIso A f (Compactification.ofIsProper f) := by
  obtain ⟨hid, hcomp⟩ := unboundedEtaleCompactSupport_comparison_coherence A f
  have he : rightDerivedLowerShriekIso A c ≪≫
      (rightDerivedLowerShriekIso A (Compactification.ofIsProper f)).symm =
        rightDerivedLowerShriekOfCompactificationIso A c (Compactification.ofIsProper f) := by
    apply Iso.ext
    have hh := congrArg Iso.hom
      (hcomp c (Compactification.ofIsProper f) (HasCompactification.compactification f))
    simp only [Iso.trans_hom] at hh
    simp only [Iso.trans_hom, Iso.symm_hom, rightDerivedLowerShriekIso]
    rw [← hh, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Iso.trans_assoc, he]
  simp only [unboundedEtaleProperCandidateIso, hid, Iso.refl_trans]

private lemma proper_tower_chosen
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y S : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian S]
    (f : X ⟶ Y) (g : Y ⟶ S) [IsProper f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (d : Compactification g) (c : Compactification (f ≫ g))
    (e : Compactification (f ≫ d.i)) :
    Functor.whiskerRight (unboundedEtaleProperCandidateIso A f e.restrict).inv
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d) ≫
      (rightDerivedLowerShriekOfCompactificationCompIso A d e).hom ≫
      (rightDerivedLowerShriekOfCompactificationIso A (d.comp e) c).hom =
    Functor.whiskerRight
        ((rightDerivedLowerShriekIso A (Compactification.ofIsProper f)).symm ≪≫
          unboundedEtaleProperCandidateIso A f (Compactification.ofIsProper f)).inv
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d) ≫
      Functor.whiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
        (rightDerivedLowerShriekIso A d).hom ≫
      (unboundedEtaleLowerShriekCompIso A f g).hom ≫
      (rightDerivedLowerShriekIso A c).inv := by
  have ht := unboundedEtaleLowerShriekCompIso_tower A f g d e
  have hc := (unboundedEtaleCompactSupport_comparison_coherence A (f ≫ g)).2
    (d.comp e) c (HasCompactification.compactification (f ≫ g))
  have hhc := congrArg Iso.hom hc
  simp only [Iso.trans_hom] at hhc
  have hout : (rightDerivedLowerShriekOfCompactificationIso A (d.comp e) c).hom =
      (rightDerivedLowerShriekIso A (d.comp e)).hom ≫
        (rightDerivedLowerShriekIso A c).inv := by
    rw [rightDerivedLowerShriekIso, rightDerivedLowerShriekIso, ← hhc,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [proper_candidate_chosen A f e.restrict, ht, hout]
  ext K
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatTrans.hcomp_app, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_app_assoc]

/-- The proper normalization is compatible with compactification changes, is the
identity-open normalization at `(id,f)`, and gives the specified composition map on every
proper/open tower. The map commutes with changes of both input and output compactifications.
Source: Stacks Project, Tags 0F7H, 0F7I and 0F7J
(blueprint: lem-sf-unbounded-compact-support-proper-composition).

Proof, following the five steps of the node:
1. A field is Noetherian. Apply lem-weil-pbc-finite-type-over-noetherian to X, Y, S and
   all proper compactification ambients. Properness supplies separated finite type for f;
   lem-weil-pbc-proper-fp-permanence supplies these properties for the composite. The finite
   coefficient ring is a torsion ring, so the unbounded case of
   lem-amb-unbounded-proper-open-interchange applies without an invertibility assumption.
2. That interchange on the identity/refinement square gives the preceding K-injective
   formula. Apply the ambient direct image and its canonical compositor from
   lem-weil-pbc-ringed-topoi-derived-pushforward-composition.
3. Apply lem-amb-unbounded-compact-support-comparisons separately to f, g and their
   composite. Its comparisons agree with those of step 2 because the sheaf maps restrict
   to the identity on the source. This gives the preceding refinement coherence.
4. Use (id,f) for proper f. The degreewise identity extension by zero is the identity by
   def-weil-pbc-extension-by-zero. Compare every candidate with this trivial one. The cocycle
   gives compatibility with all choices and the identity-open value at the trivial choice.
5. Take the composition isomorphism of lem-amb-unbounded-compact-support-comparisons and
   precompose with the inverse proper normalization. Its every-tower characterization is
   exactly the proper/open interchange followed by the open and direct-image compositors.
   Its refinement compatibility gives the final equation. All maps are natural isomorphisms
   on the whole ordinary unbounded category; no constructibility condition is used. -/
theorem unboundedEtaleProperComposition_normalization
    (k : Type u) [Field k] (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y S : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (f : X ⟶ Y) (g : Y ⟶ S)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [IsProper f] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :
    (∀ c d : Compactification f,
      rightDerivedLowerShriekOfCompactificationIso A c d ≪≫
        unboundedEtaleProperCandidateIso A f d = unboundedEtaleProperCandidateIso A f c) ∧
    (unboundedEtaleProperCandidateIso A f (Compactification.ofIsProper f) =
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso
          (Adjunction.leftAdjointIdIso
            (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
            (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
          Functor.mapDerivedCategoryIdIso _) _ ≪≫ Functor.leftUnitor _) ∧
    (∀ (d : Compactification g) (c : Compactification (f ≫ g))
      (e : Compactification (f ≫ d.i)),
      (unboundedEtaleProperCompositionIso A f g d c).hom =
        Functor.whiskerRight (unboundedEtaleProperCandidateIso A f e.restrict).inv
            (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d) ≫
          (rightDerivedLowerShriekOfCompactificationCompIso A d e).hom ≫
          (rightDerivedLowerShriekOfCompactificationIso A (d.comp e) c).hom) ∧
    (∀ (d₁ d₂ : Compactification g) (c₁ c₂ : Compactification (f ≫ g)),
      Functor.whiskerLeft R((f)_*[ModuleCat.{u + 1} A])
          (rightDerivedLowerShriekOfCompactificationIso A d₁ d₂).hom ≫
          (unboundedEtaleProperCompositionIso A f g d₂ c₂).hom =
        (unboundedEtaleProperCompositionIso A f g d₁ c₁).hom ≫
          (rightDerivedLowerShriekOfCompactificationIso A c₁ c₂).hom) := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsNoetherian X := ⟨⟩
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : IsNoetherian Y := ⟨⟩
  let : IsLocallyNoetherian S :=
    LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of k))
  let : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
  let : IsNoetherian S := ⟨⟩
  let := hasCompactification_of_finiteType_over_field k X Y f
  let := hasCompactification_of_finiteType_over_field k Y S g
  let := hasCompactification_of_finiteType_over_field k X S (f ≫ g)
  obtain ⟨hid, hcomp⟩ := unboundedEtaleCompactSupport_comparison_coherence A f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c d
    dsimp only [unboundedEtaleProperCandidateIso]
    rw [← Iso.trans_assoc, hcomp]
  · simp only [unboundedEtaleProperCandidateIso, hid, Iso.refl_trans]
  · intro d c e
    change (Functor.whiskerRight _ _ ≫ _ ≫ _) = _
    simp only [Iso.symm_hom]
    rw [proper_tower_chosen A f g d c (c.ofComp d), proper_tower_chosen A f g d c e]
  · intro d₁ d₂ c₁ c₂
    have hleft := proper_tower_chosen A f g d₁ c₁ (c₁.ofComp d₁)
    have hright := proper_tower_chosen A f g d₂ c₂ (c₂.ofComp d₂)
    change _ ≫ (Functor.whiskerRight _ _ ≫ _ ≫ _) =
      (Functor.whiskerRight _ _ ≫ _ ≫ _) ≫ _
    simp only [Iso.symm_hom]
    rw [hleft, hright]
    have hd := congrArg Iso.hom
      ((unboundedEtaleCompactSupport_comparison_coherence A g).2 d₁ d₂
        (HasCompactification.compactification g))
    have hc := congrArg Iso.hom
      ((unboundedEtaleCompactSupport_comparison_coherence A (f ≫ g)).2 c₁ c₂
        (HasCompactification.compactification (f ≫ g)))
    simp only [Iso.trans_hom] at hd hc
    change (rightDerivedLowerShriekOfCompactificationIso A d₁ d₂).hom ≫
      (rightDerivedLowerShriekIso A d₂).hom = (rightDerivedLowerShriekIso A d₁).hom at hd
    change (rightDerivedLowerShriekOfCompactificationIso A c₁ c₂).hom ≫
      (rightDerivedLowerShriekIso A c₂).hom = (rightDerivedLowerShriekIso A c₁).hom at hc
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc]
    have hdK := NatTrans.congr_app hd
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K)
    have hcK := NatTrans.congr_app hc K
    simp only [NatTrans.comp_app] at hdK hcK
    have hout : (rightDerivedLowerShriekIso A c₁).inv.app K ≫
        (rightDerivedLowerShriekOfCompactificationIso A c₁ c₂).hom.app K =
      (rightDerivedLowerShriekIso A c₂).inv.app K := by
      apply (cancel_epi ((rightDerivedLowerShriekIso A c₁).hom.app K)).1
      simp only [Iso.hom_inv_id_app_assoc]
      rw [← hcK, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    have hn := (rightDerivedLowerShriekOfCompactificationIso A d₁ d₂).hom.naturality
      (((rightDerivedLowerShriekIso A (Compactification.ofIsProper f)).symm ≪≫
        unboundedEtaleProperCandidateIso A f (Compactification.ofIsProper f)).inv.app K)
    dsimp only [rightDerivedLowerShriekOfCompactification, Functor.comp_map] at hn ⊢
    rw [← reassoc_of% hn, reassoc_of% hdK, hout]

end AlgebraicGeometry.Etale
