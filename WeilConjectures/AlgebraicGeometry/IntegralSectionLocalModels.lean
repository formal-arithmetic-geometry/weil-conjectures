/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralCompletedCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions
public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectModels
import WeilConjectures.AlgebraicGeometry.IntegralSectionMemberModels
import WeilConjectures.WeilObject.Sheaf.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement

/-! # Finite scalar models under the normalized integral section comparison

Source: Bhatt--Scholze, Definition 6.8.10; integral constructibility bridge, step 7.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  CondensedRing.upperStar CondensedRing.lowerStar CategoryTheory.Sheaf.monoidalCategory
  CondensedRing.upperStarComp upperStarFromPointComp Mod.extendScalarsIsoComapInv
  laxBraided_upperStarFromPoint monoidal_upperStarFromPoint
  integralSectionFunctor Scheme.integralDetailedCoefficientComparison
  Scheme.proEtaleModuleInverseImage Scheme.integralConstantModule

private noncomputable def pointModelPullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    (CondensedRing.upperStar Λ f).obj (((upperStarFromPoint X).mapMod Λ).obj P) ≅
      ((upperStarFromPoint Y).mapMod Λ).obj P := by
  exact (CondensedRing.upperStarFromPointModComp Λ f).app P

private noncomputable def modulePullbackComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (CondensedRing.upperStar Λ (f ≫ g)).obj M ≅
      (CondensedRing.upperStar Λ f).obj ((CondensedRing.upperStar Λ g).obj M) :=
  (CondensedRing.upperStarComp Λ f g).app M

set_option backward.isDefEq.respectTransparency.types false in
private theorem coverPredicate_on_sieve {S : Scheme.{u}}
    (P : ∀ {Y : Scheme.{u}}, (Y ⟶ S) → Prop)
    (hP : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ S) (b : Z ⟶ Y), P f → P (b ≫ f)) :
    (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ i, P (C.f i)) ↔
      ∃ V : Sieve (⊤_ S.ProEt), V ∈ Scheme.ProEt.topology S (⊤_ S.ProEt) ∧
        ∀ (U : S.ProEt) (f : U ⟶ ⊤_ S.ProEt), V f → P (Y := U.left) U.hom := by
  classical
  have hT : IsTerminal (Scheme.ProEt.mk (𝟙 S)) :=
    MorphismProperty.Over.mkIdTerminal _ _
  have t : Scheme.ProEt.mk (𝟙 S) ≅ ⊤_ S.ProEt := hT.uniqueUpToIso terminalIsTerminal
  constructor
  · rintro ⟨C, hC⟩
    let U (i : C.I₀) : S.ProEt :=
      MorphismProperty.Over.mk ⊤ (C.f i)
        ((Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀) ⟨i⟩)
    let a (i : C.I₀) : U i ⟶ ⊤_ S.ProEt :=
      (MorphismProperty.Over.homMk (B := Scheme.ProEt.mk (𝟙 S)) (C.f i)
        (by exact Category.comp_id _)) ≫ t.hom
    refine ⟨Sieve.ofArrows U a, ?_, ?_⟩
    · apply Precoverage.generate_mem_toGrothendieck
      rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
      have : IsIso t.hom.left :=
        (Scheme.ProEt.forget S ⋙ Over.forget S).map_isIso t.hom
      change (Presieve.ofArrows (fun i ↦ C.X i)
        (fun i ↦ C.f i ≫ t.hom.left)) ∈ _
      exact (C.pushforward t.hom.left
        (Precoverage.mem_coverings_of_isIso _)).mem₀
    · intro W f hf
      obtain ⟨Z, b, c, ⟨i⟩, hbc⟩ := hf
      have hw : b.left ≫ C.f i = W.hom := MorphismProperty.Over.w b
      rw [← hw]
      exact hP (C.f i) b.left (hC i)
  · rintro ⟨V, hV, hmodels⟩
    obtain ⟨R, hR, hRV⟩ := Scheme.ProEt.mem_topology_iff.mp hV
    obtain ⟨I, U, f, rfl⟩ := R.exists_eq_ofArrows
    have hc : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
        Scheme.proetalePrecoverage S := by
      let C₀ : Scheme.Cover Scheme.proetalePrecoverage (⊤_ S.ProEt).left :=
        ⟨⟨I, fun i ↦ (U i).left, fun i ↦ (f i).left⟩, by
          simpa only [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows,
            Functor.comp_obj, Functor.comp_map, Scheme.ProEt.forget,
            MorphismProperty.Over.forget, MorphismProperty.Comma.forget, Over.forget,
            Comma.fst, PreZeroHypercover.presieve₀] using hR⟩
      have : IsIso t.inv.left :=
        (Scheme.ProEt.forget S ⋙ Over.forget S).map_isIso t.inv
      have he (i : I) : (f i).left ≫ t.inv.left = (U i).hom := by
        have ht := MorphismProperty.Over.w t.inv
        change t.inv.left = (⊤_ S.ProEt).hom at ht
        rw [ht]
        exact MorphismProperty.Over.w (f i)
      have h := (C₀.pushforward t.inv.left
        (Precoverage.mem_coverings_of_isIso _)).mem₀
      change (Presieve.ofArrows (fun i ↦ (U i).left)
        (fun i ↦ (f i).left ≫ t.inv.left)) ∈ _ at h
      rw [show (fun i ↦ (f i).left ≫ t.inv.left) = (fun i ↦ (U i).hom)
        from funext he] at h
      exact h
    let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage S :=
      ⟨⟨I, fun i ↦ (U i).left, fun i ↦ (U i).hom⟩, hc⟩
    have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
    let q := Precoverage.ZeroHypercover.Small.restrictFun.{u} C
    let D : Scheme.Cover.{u} Scheme.proetalePrecoverage S :=
      ⟨⟨Precoverage.ZeroHypercover.Small.Index.{u} C,
        fun i ↦ (U (q i)).left, fun i ↦ (U (q i)).hom⟩,
        Precoverage.ZeroHypercover.Small.mem₀ C⟩
    refine ⟨D, fun i ↦ ?_⟩
    let j : I := q i
    exact hmodels (U j) (f j) (hRV _ _ ⟨j⟩)

private theorem sectionPointModelAlong_stable
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S Y Z : Scheme.{u}} (g : S ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (f : Y ⟶ S) (b : Z ⟶ Y) :
    sectionPointModelAlong Λ g M f → sectionPointModelAlong Λ g M (b ≫ f) := by
  rintro ⟨Q, hQ, ⟨e⟩⟩
  exact ⟨Q, hQ, ⟨(CondensedRing.upperStarCongr Λ (Category.assoc b f g)).app M ≪≫
    modulePullbackComp Λ b (f ≫ g) M ≪≫
    (CondensedRing.upperStar Λ b).mapIso e ≪≫ pointModelPullback Λ b Q⟩⟩

private theorem sectionPointModelAlong_cover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (g : S ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    HasFiniteConstantLocalModel Λ S ((CondensedRing.upperStar Λ g).obj M) ↔
      ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage S,
        ∀ i, sectionPointModelAlong Λ g M (C.f i) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun i ↦ ?_⟩
    obtain ⟨Q, hQ, ⟨e⟩⟩ := hC i
    exact ⟨Q, hQ, ⟨modulePullbackComp Λ (C.f i) g M ≪≫ e⟩⟩
  · rintro ⟨C, hC⟩
    refine ⟨C, fun i ↦ ?_⟩
    obtain ⟨Q, hQ, ⟨e⟩⟩ := hC i
    exact ⟨Q, hQ, ⟨(modulePullbackComp Λ (C.f i) g M).symm ≪≫ e⟩⟩

private theorem stratifiedModels_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (Q : ∀ {S : Scheme.{u}}, (S ⟶ X) → S.ProEt → Prop)
    (hQ : ∀ {S : Scheme.{u}} (g : S ⟶ X) (U : S.ProEt),
      sectionPointModelAlong Λ g M U.hom ↔ Q g U) :
    IsFiniteConstantStratified Λ X M ↔
      ∃ s : Scheme.Stratification X, ∀ i : Fin s.n,
        ∃ V : Sieve (⊤_ (s.domain i).ProEt),
          V ∈ Scheme.ProEt.topology (s.domain i) (⊤_ (s.domain i).ProEt) ∧
            ∀ (U : (s.domain i).ProEt) (f : U ⟶ ⊤_ (s.domain i).ProEt), V f →
              Q (s.immersion i) U := by
  apply exists_congr
  intro s
  apply forall_congr'
  intro i
  apply (sectionPointModelAlong_cover Λ (s.immersion i) M).trans
  apply (coverPredicate_on_sieve (sectionPointModelAlong Λ (s.immersion i) M)
    (fun f b ↦ sectionPointModelAlong_stable _ _ _ f b)).trans
  apply exists_congr
  intro V
  apply and_congr_right
  intro hV
  apply forall_congr'
  intro U
  apply forall_congr'
  intro f
  apply imp_congr_right
  intro hf
  exact hQ _ U

/-- Finite constant local models can be expressed on covering sieves on the same
finite stratification, entirely over the pulled-back condensed coefficient ring.

Source: the integral-criterion paragraph of the proof of
`lem-sfb-dc-lower-star-preserves`, and the definition of constructible modules.
(blueprint: lem-sfb-integral-section-local-models).

Proof: Noetherianity selects the finite-stratification branch. On each stratum,
compose pullbacks to identify local models with point models along the composite
map to X. Such a model remains a model after any further pullback, by the
composition and point-pullback isomorphisms. A pro-etale cover therefore generates
a covering sieve all of whose members admit models. Conversely, choose a covering
presieve inside the given sieve, identify the terminal pro-etale object with X,
and restrict the resulting cover to a small subfamily. Keep the same point modules,
finite presentations and stratification in both directions. Empty covers and
rank-zero presentations are included. -/
theorem integralSectionLocalModels
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsConstantModelConstructible Λ X M ↔
      ∃ s : Scheme.Stratification X, ∀ i : Fin s.n,
        ∃ V : Sieve (⊤_ (s.domain i).ProEt),
          V ∈ Scheme.ProEt.topology (s.domain i) (⊤_ (s.domain i).ProEt) ∧
            ∀ (U : (s.domain i).ProEt) (f : U ⟶ ⊤_ (s.domain i).ProEt), V f →
              sectionPointModelAlong Λ (s.immersion i) M U.hom := by
  classical
  have hqc : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  have hbranch : IsConstantModelConstructible Λ X M ↔
      IsFiniteConstantStratified Λ X M := by
    simp only [IsConstantModelConstructible, if_pos hqc]
  apply hbranch.trans
  exact stratifiedModels_transport Λ X M
    (fun g U ↦ sectionPointModelAlong Λ g M U.hom) (fun _ _ ↦ Iff.rfl)

end AlgebraicGeometry.ProEtale
