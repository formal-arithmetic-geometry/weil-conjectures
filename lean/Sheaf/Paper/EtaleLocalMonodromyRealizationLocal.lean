/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.Paper.EtaleMonodromyRealizationData
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Sheaf.AlgebraicGeometry.FiniteTypeNoetherianSpectrum
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import Sheaf.Paper.MonodromyObjectCover

/-! # Connected pointed refinements and lifting finite diagrams

Source: Bhatt--Scholze, Corollary 6.8.5.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

private theorem exists_noetherian_affine_neighborhood
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [TopologicalSpace.NoetherianSpace S] (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ TopologicalSpace.NoetherianSpace U := by
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ f ⁻¹ᵁ V from hxV)
  have : TopologicalSpace.NoetherianSpace V :=
    Topology.IsInducing.noetherianSpace Topology.IsInducing.subtypeVal
  have hnV : TopologicalSpace.NoetherianSpace (Spec Γ(S, V)) :=
    (TopologicalSpace.noetherianSpace_iff_of_homeomorph hV.isoSpec.hom.homeomorph).mp
      inferInstance
  have : TopologicalSpace.NoetherianSpace (PrimeSpectrum Γ(S, V)) := by
    exact hnV
  have hn : TopologicalSpace.NoetherianSpace (PrimeSpectrum Γ(X, U)) :=
    noetherianSpace_primeSpectrum_of_finiteType _ _ (f.appLE V U hUV).hom
      (f.finiteType_appLE hV hU hUV)
  have : TopologicalSpace.NoetherianSpace (Spec Γ(X, U)) := by
    change TopologicalSpace.NoetherianSpace (PrimeSpectrum Γ(X, U))
    exact hn
  exact ⟨U, hU, hxU,
    (TopologicalSpace.noetherianSpace_iff_of_homeomorph hU.isoSpec.inv.homeomorph).mp
      inferInstance⟩

private theorem exists_monodromy_point (T : Scheme.{u}) [ConnectedSpace T]
    [CompactSpace T] [QuasiSeparatedSpace T] [TopologicalSpace.NoetherianSpace T] :
    Nonempty (SfMonodromyPoint T) := by
  classical
  let x : T := Classical.choice inferInstance
  let Ω := AlgebraicClosure (T.residueField x)
  let pt : Spec (.of Ω) ⟶ T :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField x) Ω)) ≫
      T.fromSpecResidueField x
  obtain ⟨G, act, hG⟩ := FiniteEtale.exists_isFundamentalGroup pt
  exact ⟨{
    connected := inferInstance
    compact := inferInstance
    quasiSeparated := inferInstance
    noetherian := inferInstance
    Ω := Ω
    field := inferInstance
    closed := inferInstance
    point := pt
    group := G
    actions := act
    fundamental := hG }⟩

private theorem exists_monodromy_neighborhood
    {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    [TopologicalSpace.NoetherianSpace S] (x : X) :
    ∃ (T : Scheme.{u}) (g : T ⟶ X), IsOpenImmersion g ∧
      x ∈ Set.range g ∧ Nonempty (SfMonodromyPoint T) := by
  obtain ⟨U, _, hxU, hU⟩ := exists_noetherian_affine_neighborhood f x
  have : TopologicalSpace.NoetherianSpace U.toScheme := hU
  let y : U.toScheme := ⟨x, hxU⟩
  let C : U.toScheme.Opens :=
    ⟨connectedComponent y, TopologicalSpace.NoetherianSpace.isOpen_connectedComponent y⟩
  have hC : ConnectedSpace C :=
    Subtype.connectedSpace (isConnected_connectedComponent (x := y))
  have : TopologicalSpace.NoetherianSpace C :=
    Topology.IsInducing.noetherianSpace Topology.IsInducing.subtypeVal
  have : CompactSpace C := inferInstance
  have : QuasiSeparatedSpace C := inferInstance
  refine ⟨C.toScheme, C.ι ≫ U.ι, inferInstance, ?_, exists_monodromy_point C.toScheme⟩
  exact ⟨⟨y, mem_connectedComponent⟩, rfl⟩

private theorem exists_monodromy_refinement
    (S : Scheme.{u}) [TopologicalSpace.NoetherianSpace S]
    {I : Type (u + 1)} (Y : I → S.Etale) (hY : S.smallEtaleTopology.CoversTop Y) :
    ∃ (K : Type (u + 1)) (Z : K → S.Etale) (j : K → I)
      (g : ∀ k : K, Z k ⟶ Y (j k)),
      S.smallEtaleTopology.CoversTop Z ∧ (IsEmpty S → IsEmpty K) ∧
        (∀ k : K, IsOpenImmersion (g k).left) ∧
        ∀ k : K, Nonempty (SfMonodromyPoint (Z k).left) := by
  classical
  have H := fun (i : I) (x : (Y i).left) ↦ exists_monodromy_neighborhood (S := S) (Y i).hom x
  choose T a ha hxa hp using H
  have := ha
  let K := Σ i : I, (Y i).left
  let Z : K → S.Etale := fun k ↦ Etale.mk (a k.1 k.2 ≫ (Y k.1).hom)
  let g : ∀ k : K, Z k ⟶ Y k.1 := fun k ↦ MorphismProperty.Over.homMk (a k.1 k.2) rfl
  refine ⟨K, Z, Sigma.fst, g, ?_, ?_, (fun k ↦ ha k.1 k.2), fun k ↦ hp k.1 k.2⟩
  · rw [S.smallEtaleTopology.coversTop_iff_of_isTerminal (Etale.mk (𝟙 S))
      (Etale.isTerminalMkId S), mem_smallEtaleTopology_iff]
    intro x
    obtain ⟨W, b, ⟨i, ⟨c⟩⟩, w, hw⟩ :=
      (mem_smallEtaleTopology_iff _).mp (hY (Etale.mk (𝟙 S))) x
    obtain ⟨z, hz⟩ := hxa i (c.left w)
    refine ⟨Z ⟨i, c.left w⟩,
      MorphismProperty.Over.homMk (a i (c.left w) ≫ (Y i).hom)
        (by dsimp [Z]; exact Category.comp_id _),
      ⟨⟨i, c.left w⟩, ⟨𝟙 _⟩⟩, z, ?_⟩
    change (Y i).hom (a i (c.left w) z) = x
    rw [hz]
    have hc := congrArg (fun q : W.left ⟶ S ↦ q w) c.w
    have hb := congrArg (fun q : W.left ⟶ S ↦ q w) b.w
    change (Y i).hom (c.left w) = W.hom w at hc
    change b.left w = W.hom w at hb
    exact hc.trans (hb.symm.trans hw)
  · intro hS
    exact ⟨fun k ↦ hS.false ((Y k.1).hom k.2)⟩

private theorem lift_diagram_arrows
    {C D : Type*} [Category C] [Category D] (J : C ⥤ D)
    (hJ : J.FullyFaithful) {A B : Type*} (s t : B → A)
    (V : A → C) (P : A → D) (e : ∀ a : A, J.obj (V a) ≅ P a)
    (f : ∀ b : B, P (s b) ⟶ P (t b)) :
    ∃ h : ∀ b : B, V (s b) ⟶ V (t b),
      ∀ b : B, J.map (h b) ≫ (e (t b)).hom = (e (s b)).hom ≫ f b := by
  let h := fun b : B ↦ hJ.preimage ((e (s b)).hom ≫ f b ≫ (e (t b)).inv)
  refine ⟨h, fun b ↦ ?_⟩
  dsimp only [h]
  rw [hJ.map_preimage]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]



private theorem monodromy_restriction_congr (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {S T : Scheme.{u}} (f g : T ⟶ S)
    [Etale f] [Etale g] (h : f = g) :
    PresheafOfModules.pushforward
        (ProEtale.lisseEtaleCoefficientIdentificationSized l E f) =
      PresheafOfModules.pushforward
        (ProEtale.lisseEtaleCoefficientIdentificationSized l E g) := by
  subst g
  rfl

/-- Object models on an etale cover lift to finite diagrams on connected pointed charts.
Source: Bhatt--Scholze, proof of Corollary 6.8.5, pp. 59--60.
(blueprint: lem-sfb-etale-local-monodromy-realization-local) -/
theorem etale_local_monodromy_realization_local (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (R : ∀ (T : Scheme.{u}) (p : SfMonodromyPoint T), SfMonodromyRealization l E p) :
    ∀ (S : Scheme.{u}) [TopologicalSpace.NoetherianSpace S]
        (A B : Type (u + 1)) [Finite A] [Finite B] (s t : B → A)
        (L : A → SfRationalModules l E S) (f : ∀ b : B, L (s b) ⟶ L (t b)),
        (∀ a : A, (L a).IsFiniteLocallyFree) →
          ∃ (I : Type (u + 1)) (Y : I → S.Etale),
            S.smallEtaleTopology.CoversTop Y ∧ (IsEmpty S → IsEmpty I) ∧
            ∃ (p : ∀ i : I, SfMonodromyPoint (Y i).left)
              (V : ∀ i : I, A → SfContinuousRepresentations l E (p i))
              (h : ∀ (i : I) (b : B), V i (s b) ⟶ V i (t b))
              (e : ∀ (i : I) (a : A),
                ((R (Y i).left (p i)).functor.obj (V i a)).val ≅
                  (PresheafOfModules.pushforward
                    (ProEtale.lisseEtaleCoefficientIdentificationSized l E (Y i).hom)).obj
                      (L a).val),
              ∀ (i : I) (b : B),
                ((R (Y i).left (p i)).functor.map (h i b)).val ≫ (e i (t b)).hom =
                  (e i (s b)).hom ≫
                    (PresheafOfModules.pushforward
                      (ProEtale.lisseEtaleCoefficientIdentificationSized l E (Y i).hom)).map
                        (f b).val  := by
  classical
  intro S _ A B _ _ s t L f hL
  obtain ⟨I, Y, hY, H⟩ := exists_sf_monodromy_object_cover l E S A L hL
  obtain ⟨K, Z, j, g, hZ, hempty, hg, hp⟩ := exists_monodromy_refinement S Y hY
  let p := fun k : K ↦ Classical.choice (hp k)
  have H' : ∀ k : K, ∃ V : A → SfContinuousRepresentations l E (p k),
      ∀ a : A, Nonempty (((R (Z k).left (p k)).functor.obj (V a)).val ≅
        (PresheafOfModules.pushforward
          (ProEtale.lisseEtaleCoefficientIdentificationSized l E (Z k).hom)).obj
            (L a).val) := by
    intro k
    have : IsOpenImmersion (g k).left := hg k
    have hcomp : (g k).left ≫ (Y (j k)).hom = (Z k).hom := by
      exact (g k).w
    have Hk := H (j k) (Z k).left (g k).left (p k) (R (Z k).left (p k))
    change ∃ V : A → SfContinuousRepresentations l E (p k),
      ∀ a : A, Nonempty (((R (Z k).left (p k)).functor.obj (V a)).val ≅
        (PresheafOfModules.pushforward
          (ProEtale.lisseEtaleCoefficientIdentificationSized l E
            ((g k).left ≫ (Y (j k)).hom))).obj (L a).val) at Hk
    rw [monodromy_restriction_congr l E _ _ hcomp] at Hk
    exact Hk
  choose V he using H'
  let e := fun (k : K) (a : A) ↦ Classical.choice (he k a)
  have HH : ∀ k : K, ∃ h : ∀ b : B, V k (s b) ⟶ V k (t b),
      ∀ b : B, ((R (Z k).left (p k)).functor.map (h b)).val ≫ (e k (t b)).hom =
        (e k (s b)).hom ≫
          (PresheafOfModules.pushforward
            (ProEtale.lisseEtaleCoefficientIdentificationSized l E (Z k).hom)).map
              (f b).val := by
    intro k
    let J := (R (Z k).left (p k)).functor
    let F := SheafOfModules.forget
      ((sheafCompose (ProEt.topology (Z k).left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (ProEtale.lisseFieldSheafSized l E (Z k).left))
    have hff : (J ⋙ F).FullyFaithful :=
      (R (Z k).left (p k)).fullyFaithful.comp (SheafOfModules.fullyFaithfulForget _)
    exact lift_diagram_arrows (J ⋙ F) hff s t (V k) _ (e k) (fun b ↦
      (PresheafOfModules.pushforward
        (ProEtale.lisseEtaleCoefficientIdentificationSized l E (Z k).hom)).map (f b).val)
  choose h hh using HH
  exact ⟨K, Z, hZ, hempty, p, V, h, e, hh⟩

end AlgebraicGeometry.Scheme
