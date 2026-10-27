/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.StratumHomComparisonData
import all Sheaf.AlgebraicGeometry.EtaleGenericStratumMate
import Sheaf.AlgebraicGeometry.StratumHomPairingIdentity
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Construction of the normalized stratum Hom isomorphisms

Source: Weil blueprint, latest, finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate).

The normalized isomorphisms are constructed by parametrized adjunction. The comparison
of their evaluation pairings is a separate statement; invertibility follows here by
cancellation from that equality and the specified direct-image comparison isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u u₁ v₁
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped CategoryTheory.Functor MonoidalCategory
attribute [local instance high] GrothendieckTopology.W.monoidal
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
namespace AlgebraicGeometry.StratumHomComparisonMate

attribute [local irreducible] AlgebraicGeometry.Etale.derivedTensor
  AlgebraicGeometry.ProEtale.derivedTensor AlgebraicGeometry.Etale.derivedHom
  AlgebraicGeometry.ProEtale.derivedHom AlgebraicGeometry.Etale.derivedTensorHomAdjunction₂
  AlgebraicGeometry.ProEtale.derivedTensorHomAdjunction₂
  ImmersionProjectionComparison.Etale.symmetry ImmersionProjectionComparison.ProEtale.symmetry
  Etale.extensionIso ProEtale.extensionIso


private theorem transportProjectionNat
    {C D : Type*} [Category C] [Category D]
    (TX : C ⥤ C ⥤ C) (TS : D ⥤ D ⥤ D)
    {F F' : D ⥤ C} (L : C ⥤ D) (e : F ≅ F')
    (p : ∀ K P, (TX.obj K).obj (F'.obj P) ⟶ F'.obj ((TS.obj (L.obj K)).obj P))
    (hn : ∀ K K' P P' (f : K ⟶ K') (g : P ⟶ P'),
      (TX.map f).app (F'.obj P) ≫ (TX.obj K').map (F'.map g) ≫ p K' P' =
        p K P ≫ F'.map ((TS.map (L.map f)).app P ≫ (TS.obj (L.obj K')).map g))
    (K K' : C) (P P' : D) (f : K ⟶ K') (g : P ⟶ P') :
    (TX.map f).app (F.obj P) ≫ (TX.obj K').map (F.map g) ≫
        ((TX.obj K').map (e.hom.app P') ≫ p K' P' ≫
          e.inv.app ((TS.obj (L.obj K')).obj P')) =
      ((TX.obj K).map (e.hom.app P) ≫ p K P ≫
          e.inv.app ((TS.obj (L.obj K)).obj P)) ≫
        F.map ((TS.map (L.map f)).app P ≫ (TS.obj (L.obj K')).map g) := by
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, e.hom.naturality, Functor.map_comp_assoc]
  rw [← (TX.map f).naturality_assoc, reassoc_of% (hn K K' P P' f g)]
  rw [e.inv.naturality]

private theorem transportProjectionIso
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C) {F F' : D ⥤ C} (e : F ≅ F')
    (P Q : D) (p : T.obj (F'.obj P) ⟶ F'.obj Q) [IsIso p] :
    IsIso (T.map (e.hom.app P) ≫ p ≫ e.inv.app Q) := by
  infer_instance

private theorem etaleProjectionIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] (K : Etale.D A X) (P : Etale.D A S) :
    IsIso (Etale.projection A c v K P) := by
  have : IsIso (ImmersionProjectionComparison.Etale.projection A c v K P) :=
    (ImmersionProjectionComparison.immersion_projection_site_comparison A c v).1.1 K P
  exact transportProjectionIso
    ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj K)
    (Etale.extensionIso A c v) P _
    (ImmersionProjectionComparison.Etale.projection A c v K P)

private theorem proetaleProjectionIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] (K : ProEtale.D A X) (P : ProEtale.D A S) :
    IsIso (ProEtale.projection A c v K P) := by
  have : IsIso (ImmersionProjectionComparison.ProEtale.projection A c v K P) :=
    (ImmersionProjectionComparison.immersion_projection_site_comparison A c v).2.1.1 K P
  exact transportProjectionIso
    ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj K)
    (ProEtale.extensionIso A c v) P _
    (ImmersionProjectionComparison.ProEtale.projection A c v K P)

private theorem etaleProjectionNat
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (K K' : Etale.D A X) (P P' : Etale.D A S) (f : K ⟶ K') (g : P ⟶ P') :
    ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X).map f).app
        ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P) ≫
      ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj K').map
        ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).map g) ≫
      Etale.projection A c v K' P' =
    Etale.projection A c v K P ≫
      (AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).map
        (((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S).map
          ((ImmersionProjectionComparison.Etale.pull A c).map
            ((ImmersionProjectionComparison.Etale.pull A v).map f))).app P ≫
          ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S).obj
            ((ImmersionProjectionComparison.Etale.pull A c).obj
              ((ImmersionProjectionComparison.Etale.pull A v).obj K'))).map g) := by
  have hn := (ImmersionProjectionComparison.immersion_projection_site_comparison A c v).1.2
  have h := transportProjectionNat
    (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S)
    (ImmersionProjectionComparison.Etale.pull A v ⋙
      ImmersionProjectionComparison.Etale.pull A c)
    (Etale.extensionIso A c v)
    (ImmersionProjectionComparison.Etale.projection A c v) hn K K' P P' f g
  simpa only [Etale.projection, Functor.comp_obj, Functor.comp_map, Category.assoc] using h


private theorem internalHomIsoNormalized
    {C D : Type*} [Category C] [Category D]
    {TS : D ⥤ D ⥤ D} {HS : Dᵒᵖ ⥤ D ⥤ D}
    {TX : C ⥤ C ⥤ C} {HX : Cᵒᵖ ⥤ C ⥤ C}
    {F : D ⥤ C} {G : C ⥤ D} {L : C ⥤ D} {R : D ⥤ C}
    (aS : TS ⊣₂ HS) (aX : TX ⊣₂ HX)
    (σS : TS ≅ TS.flip) (σX : TX ≅ TX.flip) (a : L ⊣ R) (b : F ⊣ G)
    (p : ∀ (K : C) (P : D), (TX.obj K).obj (F.obj P) ⟶
      F.obj ((TS.obj (L.obj K)).obj P)) [hiso : ∀ K P, IsIso (p K P)]
    (hn : ∀ (K K' : C) (P P' : D) (f : K ⟶ K') (g : P ⟶ P'),
      ((TX.map f).app (F.obj P) ≫ (TX.obj K').map (F.map g)) ≫ p K' P' =
        p K P ≫ F.map ((TS.map (L.map f)).app P ≫ (TS.obj (L.obj K')).map g)) :
    ∃ χ : F.op.prod (𝟭 C) ⋙ Functor.uncurry.obj HX ≅
        (𝟭 Dᵒᵖ).prod G ⋙ Functor.uncurry.obj HS ⋙ R,
      ∀ P B,
        (TX.map (χ.inv.app (op P, B))).app (F.obj P) ≫
          (σX.hom.app ((HX.obj (op (F.obj P))).obj B)).app (F.obj P) ≫
          (aX.adj (F.obj P)).counit.app B =
        p (R.obj ((HS.obj (op P)).obj (G.obj B))) P ≫
          F.map ((TS.map (a.counit.app ((HS.obj (op P)).obj (G.obj B)))).app P) ≫
          F.map ((σS.hom.app ((HS.obj (op P)).obj (G.obj B))).app P ≫
            (aS.adj P).counit.app (G.obj B)) ≫ b.counit.app B := by
  obtain ⟨χ, hχ⟩ := CategoryTheory.internalHomIsoOfProjectionData
    aS aX σS σX a b p hn
  refine ⟨χ, ?_⟩
  intro P B
  simpa [Adjunction.homEquiv_counit] using hχ P B _ (𝟙 _)



private theorem proetaleProjectionNat
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (K K' : ProEtale.D A X) (P P' : ProEtale.D A S) (f : K ⟶ K') (g : P ⟶ P') :
    ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).map f).app
        ((AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v).obj P) ≫
      ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj K').map
        ((AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v).map g) ≫
      ProEtale.projection A c v K' P' =
    ProEtale.projection A c v K P ≫
      (AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v).map
        (((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S).map
          ((ImmersionProjectionComparison.ProEtale.pull A c).map
            ((ImmersionProjectionComparison.ProEtale.pull A v).map f))).app P ≫
          ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S).obj
            ((ImmersionProjectionComparison.ProEtale.pull A c).obj
              ((ImmersionProjectionComparison.ProEtale.pull A v).obj K'))).map g) := by
  have hn := (ImmersionProjectionComparison.immersion_projection_site_comparison A c v).2.1.2
  have h := transportProjectionNat
    (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S)
    (ImmersionProjectionComparison.ProEtale.pull A v ⋙
      ImmersionProjectionComparison.ProEtale.pull A c)
    (ProEtale.extensionIso A c v)
    (ImmersionProjectionComparison.ProEtale.projection A c v) hn K K' P P' f g
  simpa only [ProEtale.projection, Functor.comp_obj, Functor.comp_map, Category.assoc] using h


private theorem normalizedWithEvaluations
    {C D : Type*} [Category C] [Category D]
    {TS : D ⥤ D ⥤ D} {HS : Dᵒᵖ ⥤ D ⥤ D}
    {TX : C ⥤ C ⥤ C} {HX : Cᵒᵖ ⥤ C ⥤ C}
    {F : D ⥤ C} {G : C ⥤ D} {L : C ⥤ D} {R : D ⥤ C}
    (aS : TS ⊣₂ HS) (aX : TX ⊣₂ HX)
    (σS : TS ≅ TS.flip) (σX : TX ≅ TX.flip) (a : L ⊣ R) (b : F ⊣ G)
    (evS : ∀ P B, (TS.obj ((HS.obj (op P)).obj B)).obj P ⟶ B)
    (evX : ∀ P B, (TX.obj ((HX.obj (op P)).obj B)).obj P ⟶ B)
    (heS : ∀ P B, evS P B = (σS.hom.app ((HS.obj (op P)).obj B)).app P ≫
      (aS.adj P).counit.app B)
    (heX : ∀ P B, evX P B = (σX.hom.app ((HX.obj (op P)).obj B)).app P ≫
      (aX.adj P).counit.app B)
    (p : ∀ (K : C) (P : D), (TX.obj K).obj (F.obj P) ⟶
      F.obj ((TS.obj (L.obj K)).obj P)) [hiso : ∀ K P, IsIso (p K P)]
    (hn : ∀ (K K' : C) (P P' : D) (f : K ⟶ K') (g : P ⟶ P'),
      ((TX.map f).app (F.obj P) ≫ (TX.obj K').map (F.map g)) ≫ p K' P' =
        p K P ≫ F.map ((TS.map (L.map f)).app P ≫ (TS.obj (L.obj K')).map g)) :
    ∃ χ : stratumHomIsoType HS HX F G R,
      tensorHomNormalization TS HS TX HX F G L R a b evX evS p χ := by
  obtain ⟨χ, hχ⟩ := internalHomIsoNormalized aS aX σS σX a b p hn
  refine ⟨χ, ?_⟩
  unfold tensorHomNormalization
  intro P B
  simpa only [heS, heX, Category.assoc] using hχ P B

private theorem etaleNormalizedIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (a : AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints A c) :
    ∃ χ : Etale.HomIso A c v a, Etale.Normalized A c v a χ := by
  have hi : ∀ K P, IsIso (Etale.projection A c v K P) :=
    fun K P ↦ etaleProjectionIso A c v K P
  exact normalizedWithEvaluations (hiso := hi)
    (TS := AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S)
    (HS := AlgebraicGeometry.Etale.derivedHom (ModuleCat.{u + 1} A) S)
    (TX := AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X)
    (HX := AlgebraicGeometry.Etale.derivedHom (ModuleCat.{u + 1} A) X)
    (F := AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v)
    (G := a.etaleRight v)
    (L := ImmersionProjectionComparison.Etale.pull A v ⋙
      ImmersionProjectionComparison.Etale.pull A c)
    (R := (AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)
      ).rightDerivedFunctor)
    (AlgebraicGeometry.Etale.derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} A) S)
    (AlgebraicGeometry.Etale.derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} A) X)
    (ImmersionProjectionComparison.Etale.symmetry A S)
    (ImmersionProjectionComparison.Etale.symmetry A X)
    (Etale.ordinaryAdjunction A c v) (a.etalePasted v)
    (Etale.evaluation A S) (Etale.evaluation A X)
    (by intros; rfl) (by intros; rfl)
    (Etale.projection A c v)
    (by
      intro K K' P P' f g
      rw [Category.assoc]
      exact etaleProjectionNat A c v K K' P P' f g)


private theorem proetaleNormalizedIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (a : AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints A c) :
    ∃ χ : ProEtale.HomIso A c v a, ProEtale.Normalized A c v a χ := by
  have hi : ∀ K P, IsIso (ProEtale.projection A c v K P) :=
    fun K P ↦ proetaleProjectionIso A c v K P
  exact normalizedWithEvaluations (hiso := hi)
    (TS := AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S)
    (HS := AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) S)
    (TX := AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X)
    (HX := AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) X)
    (F := AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v)
    (G := a.proetaleRight v)
    (L := ImmersionProjectionComparison.ProEtale.pull A v ⋙
      ImmersionProjectionComparison.ProEtale.pull A c)
    (R := (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)
      ).rightDerivedFunctor)
    (AlgebraicGeometry.ProEtale.derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} A) S)
    (AlgebraicGeometry.ProEtale.derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} A) X)
    (ImmersionProjectionComparison.ProEtale.symmetry A S)
    (ImmersionProjectionComparison.ProEtale.symmetry A X)
    (ProEtale.ordinaryAdjunction A c v) (a.proetalePasted v)
    (ProEtale.evaluation A S) (ProEtale.evaluation A X)
    (by intros; rfl) (by intros; rfl)
    (ProEtale.projection A c v)
    (by
      intro K K' P P' f g
      rw [Category.assoc]
      exact proetaleProjectionNat A c v K K' P P' f g)



private theorem directImageMate_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (s : S ⟶ X) [QuasiCompact s] [QuasiSeparated s]
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso (directImageMate A s K) := by
  change IsIso ((AlgebraicGeometry.ProEtale.fixedDirectImageComparisonIso A s).hom.app K)
  infer_instance

private theorem identityAndIso_of_identity
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] [QuasiCompact (c ≫ v)]
    (z : AlgebraicGeometry.ProEtale.LocallyClosedExceptionalComparison A c v)
    (P : Etale.D A S) (M : AlgebraicGeometry.Etale.BoundedConstructibleDerivedCategory A X)
    (χe : Etale.HomIso A c v z.adjoints) (χp : ProEtale.HomIso A c v z.adjoints)
    (hK : DerivedCategory.TStructure.t.plus
      (Etale.hom A S P ((z.adjoints.etaleRight v).obj M.obj)))
    (h : AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X
        ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P) M.obj ≫
      homChange A c v P M.obj ≫
      χp.hom.app (op ((ImmersionProjectionComparison.comparison A S).obj P),
        (ImmersionProjectionComparison.comparison A X).obj M.obj) =
      (ImmersionProjectionComparison.comparison A X).map (χe.hom.app (op P, M.obj)) ≫
        directImageMate A (c ≫ v) ⟨_, hK⟩ ≫
        (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A)
          (c ≫ v)).rightDerivedFunctor.map (stratumMap A c v z P M)) :
    IdentityAndIsomorphisms A c v z P M χe χp hK := by
  refine ⟨h, ?_⟩
  intro hβ
  have : IsIso (homChange A c v P M.obj) := by
    unfold homChange
    infer_instance
  have : IsIso (directImageMate A (c ≫ v) ⟨_, hK⟩) := directImageMate_isIso A _ _
  have : IsIso (stratumMap A c v z P M) := by
    unfold stratumMap
    infer_instance
  have hcomp : IsIso
      (AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X
        ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P) M.obj ≫
        homChange A c v P M.obj ≫
        χp.hom.app (op ((ImmersionProjectionComparison.comparison A S).obj P),
          (ImmersionProjectionComparison.comparison A X).obj M.obj)) := by
    rw [h]
    infer_instance
  have := IsIso.of_isIso_comp_right
    (AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X
      ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P) M.obj)
    (homChange A c v P M.obj ≫
      χp.hom.app (op ((ImmersionProjectionComparison.comparison A S).obj P),
        (ImmersionProjectionComparison.comparison A X).obj M.obj))
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩

private theorem homPlus_of_adjunction
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [IsGrothendieckAbelian.{v₁} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (K : DerivedCategory C) [K.IsLE 0]
    (G : DerivedCategory C ⥤ DerivedCategory C) (a : MonoidalCategory.tensorLeft K ⊣ G)
    (N : DerivedCategory C) (hN : DerivedCategory.TStructure.t.plus N) :
    DerivedCategory.TStructure.t.plus (G.obj N) := by
  obtain ⟨n, hn⟩ := hN
  have : N.IsGE n := hn
  exact ⟨n, by simpa only [sub_zero] using
    DerivedCategory.isGE_obj_of_adjunction a N 0 n⟩

private theorem etaleHom_bounded
    (A : Type (u + 1)) [CommRing A] {S : Scheme.{u}}
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Etale.D A S) (hN : DerivedCategory.TStructure.t.plus N) :
    DerivedCategory.TStructure.t.plus
      (Etale.hom A S (ImmersionProjectionComparison.single A L) N) := by
  have adj : MonoidalCategory.tensorLeft (ImmersionProjectionComparison.single A L) ⊣
      (AlgebraicGeometry.Etale.derivedHom (ModuleCat.{u + 1} A) S).obj
        (op (ImmersionProjectionComparison.single A L)) := by
    simpa only [AlgebraicGeometry.Etale.derivedTensor, MonoidalCategory.tensorLeft,
      MonoidalCategory.curriedTensor] using
      AlgebraicGeometry.Etale.derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
        (ImmersionProjectionComparison.single A L)
  exact homPlus_of_adjunction (ImmersionProjectionComparison.single A L) _ adj N hN

/-- The stratum Hom composite is exactly the evaluation comparison under the canonical
identifications, with the stated conditional invertibility, using only ambient adjoints.
Source: Weil blueprint, latest, sec-smooth-purity/sk-lem-sp-tower,
lem-weil-finite-duality-site-comparison.proof.md, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate).

Proof:
1. Finite type over the field makes X Noetherian. Internal Hom from the degree-zero
sheaf L preserves boundedness below by the tensor-left adjunction cohomological bound.
2. Transport projection through the derived/exact extension isomorphisms on each site.
Its invertibility and naturality allow the parametrized adjunction construction to
produce a natural stratum Hom isomorphism for the actual exceptional right adjoint.
The counit formula is precisely its inverse evaluation normalization.
3. Apply normalizedComparisonIdentity to the two constructed isomorphisms and the
boundedness witness. This is the separate evaluation-pairing step of the argument.
4. If stratum beta is invertible, Hom of gamma and stratumMap are invertible. The
fixed ordinary direct-image mate is invertible for the qcqs immersion. Functors
preserve inverses. Cancel the invertible Hom of Delta and chi_p from the equality
to obtain invertibility of ambient beta and every displayed arrow.
-/
theorem stratumHomComparisonMate
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {S V X : Scheme.{u}}
    (aS : S ⟶ Spec (.of D.k)) (aX : X ⟶ Spec (.of D.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS]
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (c : S ⟶ V) (v : V ⟶ X) [IsClosedImmersion c] [IsOpenImmersion v]
    (_hs : (c ≫ v) ≫ aX = aS) :
    ∃ hX : IsNoetherian X, ∃ hqc : QuasiCompact (c ≫ v),
      @Conclusion (Padic.coefficientExtensionRing l E (n + 1)) inferInstance
        (Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))
        S V X hX c v inferInstance inferInstance hqc := by
  have hX : IsNoetherian X := by
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
    let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
    exact {}
  have hqc : QuasiCompact (c ≫ v) := inferInstance
  refine ⟨hX, hqc, ?_⟩
  intro z L hL hflat M hM
  obtain ⟨χe, he⟩ := etaleNormalizedIso _ c v z.adjoints
  obtain ⟨χp, hp⟩ := proetaleNormalizedIso _ c v z.adjoints
  refine ⟨χe, χp, he, hp, etaleHom_bounded _ L _ (z.bounded M), ?_⟩
  exact identityAndIso_of_identity _ c v z _ M χe χp _
    (normalizedComparisonIdentity _ c v z _ M χe χp he hp _)

end AlgebraicGeometry.StratumHomComparisonMate
