/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-! # Etale locality of the ordinary ambient adjoint

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-etale-adjoint-locality.md
(blueprint: lem-amb-etale-adjoint-locality).

Sheaf-level exactness is the existing `preservesFiniteLimits_etaleLowerShriek`, together
with preservation of colimits by its existing left-adjoint structure. The first declaration
below descends the existing sheaf adjunction, without any boundedness restriction. The second
states locality for arbitrary right adjoints of the ordinary compact-support candidates.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private noncomputable abbrev openLocalization {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] : U.Etale ⥤ X.Etale :=
  MorphismProperty.Over.map ⊤ (inferInstance : Etale j)

private lemma openLocalization_terminal {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (V : X.Etaleᵒᵖ)
    (t : CostructuredArrow (openLocalization j).op V) [IsIso t.hom] :
    Nonempty (IsTerminal t) := by
  have : (openLocalization j).Full :=
    MorphismProperty.Over.full_map (P := @Etale) (Q := ⊤) (f := j) _
  have : (openLocalization j).Faithful :=
    MorphismProperty.Over.faithful_map (P := @Etale) (Q := ⊤) (f := j) _
  have hL : (openLocalization j).op.FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful (openLocalization j)).op
  refine ⟨IsTerminal.ofUniqueHom (fun s ↦ CostructuredArrow.homMk
    (hL.preimage (s.hom ≫ inv t.hom)) (by
      erw [hL.map_preimage]
      simp)) (fun s m ↦ ?_)⟩
  ext
  apply hL.map_injective
  erw [hL.map_preimage]
  simp [← CostructuredArrow.w m]

private lemma openLocalization_iso {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (V : X.Etaleᵒᵖ)
    (s : CostructuredArrow (openLocalization j).op V) :
    ∃ t : CostructuredArrow (openLocalization j).op V, IsIso t.hom := by
  let W : U.Etale := s.left.unop
  let g : V.unop.left ⟶ W.left := s.hom.unop.left
  have hg : g ≫ W.hom ≫ j = V.unop.hom := by
    simpa [g] using MorphismProperty.Over.w s.hom.unop
  have : Etale ((g ≫ W.hom) ≫ j) := by
    rw [Category.assoc, hg]
    exact V.unop.prop
  have : Etale (g ≫ W.hom) := Etale.of_comp _ j
  let V' : U.Etale := MorphismProperty.Over.mk ⊤ (g ≫ W.hom) inferInstance
  let e : (openLocalization j).obj V' ≅ V.unop :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by simpa [V'] using hg.symm)
  exact ⟨CostructuredArrow.mk (Y := Opposite.op V') e.inv.op, inferInstanceAs (IsIso e.inv.op)⟩

private lemma mono_open_lan (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {P : U.Etaleᵒᵖ ⥤ A} {Q : X.Etaleᵒᵖ ⥤ A}
    (ψ : (openLocalization j).op.lan.obj P ⟶ Q)
    (hψ : Mono ((openLocalization j).op.lanUnit.app P ≫
      Functor.whiskerLeft (openLocalization j).op ψ)) : Mono ψ := by
  have (V : X.Etaleᵒᵖ) : Mono (ψ.app V) := by
    by_cases h : Nonempty (CostructuredArrow (openLocalization j).op V)
    · obtain ⟨s⟩ := h
      obtain ⟨t, ht⟩ := openLocalization_iso j V s
      obtain ⟨hT⟩ := openLocalization_terminal j V t
      have h₂ := ((openLocalization j).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit
        P V).isIso_ι_app_of_isTerminal t hT
      change IsIso (((openLocalization j).op.lanUnit.app P).app t.left ≫
        ((openLocalization j).op.lan.obj P).map t.hom) at h₂
      have key : (((openLocalization j).op.lanUnit.app P).app t.left ≫
          ((openLocalization j).op.lan.obj P).map t.hom) ≫ ψ.app V =
          ((openLocalization j).op.lanUnit.app P ≫
            Functor.whiskerLeft (openLocalization j).op ψ).app t.left ≫
            Q.map t.hom := by
        rw [Category.assoc, ψ.naturality]
        simp
      have hm : Mono ((((openLocalization j).op.lanUnit.app P).app t.left ≫
          ((openLocalization j).op.lan.obj P).map t.hom) ≫ ψ.app V) := by
        rw [key]
        infer_instance
      rw [← IsIso.inv_hom_id_assoc (((openLocalization j).op.lanUnit.app P).app t.left ≫
        ((openLocalization j).op.lan.obj P).map t.hom) (ψ.app V)]
      infer_instance
    · have : IsEmpty (CostructuredArrow (openLocalization j).op V) :=
        not_nonempty_iff.mp h
      have hP := (isColimitEquivIsInitialOfIsEmpty A _).1
        ((openLocalization j).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit P V)
      exact (hP.isZero).mono _
  exact NatTrans.mono_of_mono_app ψ

private lemma open_unit_presheaf (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology A) :
    (sheafToPresheaf _ A).map
        ((openImmersionLowerShriekAdjunction A j).unit.app F) =
      (openLocalization j).op.lanUnit.app F.obj ≫
        Functor.whiskerLeft (openLocalization j).op
          (toSheafify _ ((openLocalization j).op.lan.obj F.obj)) := by
  dsimp only [openImmersionLowerShriekAdjunction, localizationLowerShriekAdjunction,
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
  erw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp [Functor.lanAdjunction_unit]

private lemma mono_open_of_mono_transpose (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {F : Sheaf U.smallEtaleTopology A}
    {N : Sheaf X.smallEtaleTopology A}
    (φ : (openImmersionLowerShriek A j).obj F ⟶ N)
    (hφ : Mono ((openImmersionLowerShriekAdjunction A j).unit.app F ≫
      (openImmersionRestriction A j).map φ)) : Mono φ := by
  let adj := sheafificationAdjunction X.smallEtaleTopology A
  let ψ := adj.homEquiv _ _ φ
  have hψ : Mono ψ := by
    refine mono_open_lan A j ψ ?_
    have e : (openLocalization j).op.lanUnit.app F.obj ≫
        Functor.whiskerLeft (openLocalization j).op ψ =
        (sheafToPresheaf _ A).map
          ((openImmersionLowerShriekAdjunction A j).unit.app F ≫
            (openImmersionRestriction A j).map φ) := by
      rw [Functor.map_comp, open_unit_presheaf, Category.assoc]
      congr 1
    have h := (sheafToPresheaf _ A).map_mono
      ((openImmersionLowerShriekAdjunction A j).unit.app F ≫
        (openImmersionRestriction A j).map φ)
    rw [← e] at h
    exact h
  have : φ = (presheafToSheaf _ A).map ψ ≫ adj.counit.app N := by
    exact ((adj.homEquiv _ _).symm_apply_apply φ).symm.trans (adj.homEquiv_counit (g := ψ))
  rw [this]
  have : Mono ((presheafToSheaf X.smallEtaleTopology A).map ψ) :=
    (presheafToSheaf X.smallEtaleTopology A).map_mono ψ
  exact mono_comp _ _

private lemma mono_open_to_star (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology A) :
    Mono ((openImmersionLowerShriekToLowerStar A j).app F) := by
  refine mono_open_of_mono_transpose A j _ ?_
  rw [openImmersionLowerShriekToLowerStar_app, Functor.map_comp, ← Category.assoc]
  erw [(openImmersionLowerShriekAdjunction A j).unit_naturality,
    Category.assoc,
    (openImmersionLowerShriekAdjunction A j).right_triangle_components,
    Category.comp_id]
  infer_instance

private lemma mono_compactification_to_star (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} {f : U ⟶ X} (c : Compactification f)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Mono ((compactificationSheafToDirectImage A c).app F) :=
  mono_compactification_to_star_aux (ModuleCat.{u + 1} A) c F

private lemma normalization_comparison_eq
    (A : Type (u + 1)) [CommRing A]
    (N N' : EtaleCompactSupportNormalization A)
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsNoetherian U] [IsNoetherian X] (c : Compactification f) :
    N.comparison f c = N'.comparison f c := by
  have hs : N.sheafComparison f c = N'.sheafComparison f c := by
    apply NatTrans.ext
    funext F
    have := mono_compactification_to_star A c F
    apply (cancel_mono ((compactificationSheafToDirectImage A c).app F)).1
    rw [N.sheaf_normalization, N'.sheaf_normalization]
  apply Iso.ext_inv
  apply (Functor.whiskeringLeft _ _ _).obj DerivedCategory.Qh |>.map_injective
  apply NatTrans.ext
  funext K
  change (N.comparison f c).inv.app (DerivedCategory.Qh.obj K) =
    (N'.comparison f c).inv.app (DerivedCategory.Qh.obj K)
  rw [N.derived_normalization, N'.derived_normalization, hs]

/-- The termwise derived sum-extension/restriction adjunction on whole unbounded categories.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-etale-adjoint-locality.md,
first assertion (blueprint: lem-amb-etale-adjoint-locality).
Both sheaf functors are exact; the degreewise unit and counit descend through localization,
and their triangle identities descend as well. The construction uses the existing sheaf
adjunction and the general exact-functor derived-adjunction construction. -/
noncomputable def etaleAmbientLeftComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X S : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ S)
    [Etale u] [IsSeparated u] [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (c : Compactification f) (d : Compactification (u ≫ f)) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d :=
  Functor.isoWhiskerRight (N.comparison u (d.ofComp c).restrict).symm _ ≪≫
    rightDerivedLowerShriekOfCompactificationCompIso A c (d.ofComp c) ≪≫
    rightDerivedLowerShriekOfCompactificationIso A (c.comp (d.ofComp c)) d

theorem existsUnique_etaleAmbientAdjointLocalityIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X S : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ S)
    [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (c : Compactification f) (d : Compactification (u ≫ f))
    (F : DerivedCategoryModule A S ⥤ DerivedCategoryModule A X)
    (G : DerivedCategoryModule A S ⥤ DerivedCategoryModule A U)
    (adjF : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ F)
    (adjG : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ G) :
    ∃! e : F ⋙ (upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory ≅ G,
      ∀ (N : EtaleCompactSupportNormalization A) (K : DerivedCategoryModule A S),
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
            (e.hom.app K) ≫ adjG.counit.app K =
          (etaleAmbientLeftComparison A N u f c d).inv.app
              ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj (F.obj K)) ≫
            (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
              ((derivedEtaleLowerShriekUpperStarAdjunction
                (ModuleCat.{u + 1} A) u inferInstance).counit.app (F.obj K)) ≫
            adjF.counit.app K := by
  obtain ⟨N₀⟩ := nonempty_etaleCompactSupportNormalization A
  let adjU := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) u inferInstance
  let adj := (adjU.comp adjF).ofNatIsoLeft (etaleAmbientLeftComparison A N₀ u f c d)
  refine ⟨adj.rightAdjointUniq adjG, ?_, ?_⟩
  · intro N K
    have hN : etaleAmbientLeftComparison A N₀ u f c d =
        etaleAmbientLeftComparison A N u f c d := by
      unfold etaleAmbientLeftComparison
      rw [normalization_comparison_eq A N₀ N u (d.ofComp c).restrict]
    rw [← hN]
    simpa [adj, Adjunction.ofNatIsoLeft_counit, Adjunction.comp_counit_app,
      Category.assoc] using Adjunction.rightAdjointUniq_hom_app_counit adj adjG K
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext K
    apply (adjG.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit, he N₀ K,
      Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
    simp [adj, Adjunction.ofNatIsoLeft_counit, Adjunction.comp_counit_app,
      adjU]

end AlgebraicGeometry.Etale
