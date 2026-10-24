/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.SourceExchangeTransport

/-!

# The class of the coefficient pushforward

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

lemma Adjunction.map_comp_mateEquiv_app_comp_counit {C₁ C₂ D₁ D₂ : Type*} [Category C₁]
    [Category C₂] [Category D₁] [Category D₂] {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {L₂ : C₂ ⥤ D₂}
    {R₂ : D₂ ⥤ C₂} {G : C₁ ⥤ C₂} {H : D₁ ⥤ D₂} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) {A : C₂} {B : C₁} {Xd : D₁} (γ : A ⟶ G.obj B) (u : B ⟶ R₁.obj Xd) :
    L₂.map (γ ≫ G.map u ≫ (mateEquiv adj₁ adj₂ α).app Xd) ≫ adj₂.counit.app (H.obj Xd) =
      L₂.map γ ≫ α.app B ≫ H.map (L₁.map u ≫ adj₁.counit.app Xd) := by
  have h₁ := mateEquiv_counit adj₁ adj₂ α Xd
  have h₂ := α.naturality u
  simp only [Functor.comp_map] at h₁ h₂
  simp only [Functor.map_comp, Category.assoc, h₁, reassoc_of% h₂]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Generic

variable {C Y : Over (Spec (.of k))} [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
  [IsSeparated C.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

lemma lowerShriek_map_comp_eqToHom_comp_counit {s t : C ⟶ Y} (h : t = s)
    {N : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (w : N ⟶ (boundedConstructibleUpperShriek _ ℓ t).obj M) :
    (boundedConstructibleLowerShriek _ ℓ s).map
        (w ≫ eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperShriek _ ℓ r).obj M) h)) ≫
      (boundedConstructibleUpperShriekAdjunction _ ℓ s).counit.app M =
    eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek _ ℓ r).obj N) h.symm) ≫
      (boundedConstructibleLowerShriek _ ℓ t).map w ≫
      (boundedConstructibleUpperShriekAdjunction _ ℓ t).counit.app M := by
  subst h
  simp

lemma lowerShriek_map_comp_comp_eqToHom_comp_counit {s t : C ⟶ Y} (h : t = s)
    {N N' : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (v : N' ⟶ N)
    (w : N ⟶ (boundedConstructibleUpperShriek _ ℓ t).obj M) :
    (boundedConstructibleLowerShriek _ ℓ s).map
        (v ≫ w ≫ eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperShriek _ ℓ r).obj M) h)) ≫
      (boundedConstructibleUpperShriekAdjunction _ ℓ s).counit.app M =
    (boundedConstructibleLowerShriek _ ℓ s).map v ≫
      eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek _ ℓ r).obj N) h.symm) ≫
      (boundedConstructibleLowerShriek _ ℓ t).map w ≫
      (boundedConstructibleUpperShriekAdjunction _ ℓ t).counit.app M := by
  subst h
  simp

end Generic

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence.ProperPushforwardDiagram

variable {ℓ} {c : Correspondence ℓ K} {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (P : c.ProperPushforwardDiagram Y)

set_option maxHeartbeats 2000000 in
-- the compactly supported direct images are unfolded in the defeq checks
/-- The core of `class_pushforward`: the two ways of transporting `Rp₁'_! (Lp₂'^* K' ⊗ Rb_! 𝟙)`
to `Rf_* Rc₁_! Lc₂^* K` agree. -/
theorem class_pushforward_core :
    (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        (Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ P.pushforward.support)
            ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff) (𝟙_ _) ≫
          (boundedConstructibleLowerShriek _ ℓ P.pushforward.support).map
            ((ρ_ _).hom ≫ (boundedConstructibleUpperStarComp _ ℓ P.pushforward.support
              prod.snd).inv.app P.coeff)) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ P.pushforward.support prod.fst).inv.app
        ((boundedConstructibleUpperStar _ ℓ (P.pushforward.support ≫ prod.snd)).obj P.coeff) ≫
      (boundedConstructibleLowerShriek _ ℓ (P.pushforward.support ≫ prod.fst)).map
        (eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj P.coeff)
          P.pushforward.support_snd)) ≫
      eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek _ ℓ r).obj
        ((boundedConstructibleUpperStar _ ℓ P.b₂).obj P.coeff)) P.pushforward.support_fst) ≫
      (boundedConstructibleLowerShriek _ ℓ P.b₁).map P.pushforwardCoeffUnit ≫
      (lowerStarLowerShriekCompIso ℓ P.w₁).hom.app
        ((boundedConstructibleUpperStar _ ℓ c.c₂).obj K) =
    (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff ◁
          (boundedConstructibleLowerShriek _ ℓ P.pushforward.support).map
            ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ P.g).unit.app (𝟙_ _) ≫
              (boundedConstructibleLowerStar _ ℓ P.g).map
                (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ P.g)).inv)) ≫
      (boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj P.coeff ◁
          (lowerStarLowerShriekCompIso ℓ P.g_comp_support).hom.app (𝟙_ _)) ≫
      (classTransport ℓ P.f K).app ((boundedConstructibleLowerShriek _ ℓ c.support).obj (𝟙_ _)) ≫
      (boundedConstructibleLowerStar _ ℓ P.f).map
        ((boundedConstructibleLowerShriek _ ℓ (prod.fst : X ⨯ X ⟶ X)).map
            (Verdier.leftProjection (boundedConstructibleExceptionalProjection _ ℓ c.support)
                ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).obj K) (𝟙_ _) ≫
              (boundedConstructibleLowerShriek _ ℓ c.support).map
                ((ρ_ _).hom ≫ (boundedConstructibleUpperStarComp _ ℓ c.support prod.snd).inv.app K)) ≫
          (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c.support prod.fst).inv.app
            ((boundedConstructibleUpperStar _ ℓ (c.support ≫ prod.snd)).obj K) ≫
          (boundedConstructibleLowerShriek _ ℓ (c.support ≫ prod.fst)).map
            (eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj K)
              c.support_snd)) ≫
          eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek _ ℓ r).obj
            ((boundedConstructibleUpperStar _ ℓ c.c₂).obj K)) c.support_fst)) := by
  sorry

set_option maxHeartbeats 2000000 in
-- the compactly supported direct images are unfolded in the defeq checks
/-- **The class of the coefficient pushforward** (blueprint `lem-trf-trace-source-exchange`,
identity (b)): `[δ ∘ Rg_* u ∘ γ] = Φ ∘ Rq_* [u] ∘ Ξ ∘ Rb_! η_g`. -/
theorem class_pushforward :
    P.pushforward.class =
      (boundedConstructibleLowerShriek _ ℓ P.pushforward.support).map
          ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ P.g).unit.app (𝟙_ _) ≫
            (boundedConstructibleLowerStar _ ℓ P.g).map
              (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ P.g)).inv) ≫
        (lowerStarLowerShriekCompIso ℓ P.g_comp_support).hom.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar _ ℓ (prod.map P.f P.f)).map c.class ≫
        classTransportMap ℓ P.f K := by
  apply classTest_injective
  rw [classTest_comp, classTest_comp, classTest_map_comp_classTransportMap]
  simp only [Correspondence.class]
  rw [classTest_correspondenceClassEquiv_symm, classTest_correspondenceClassEquiv_symm,
    lowerShriek_map_comp_comp_eqToHom_comp_counit ℓ P.pushforward.support_fst.symm,
    lowerShriek_map_comp_comp_eqToHom_comp_counit ℓ c.support_fst.symm]
  simp only [pushforwardCoeff, pushforwardCoeffCounit, lowerStarUpperShriekExchange]
  rw [Adjunction.map_comp_mateEquiv_app_comp_counit]
  have h := congrArg (· ≫ (boundedConstructibleLowerStar _ ℓ P.f).map
    ((boundedConstructibleLowerShriek _ ℓ c.c₁).map c.u ≫
      (boundedConstructibleUpperShriekAdjunction _ ℓ c.c₁).counit.app K)) P.class_pushforward_core
  simpa only [Functor.map_comp, Category.assoc] using h

end Correspondence.ProperPushforwardDiagram

end AlgebraicGeometry.ProEtale.CondensedRing
