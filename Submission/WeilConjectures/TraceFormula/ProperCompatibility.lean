/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.TraceFormula.ProperCompatibilityEvaluation
public import Submission.WeilConjectures.TraceFormula.ProperCompatibilitySupport
public import Submission.WeilConjectures.TraceFormula.SourceExchange

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!

# Proper pushforward compatibility of the trace class

For a proper pushforward diagram `(f, g) : (C, c) ⟶ (D, b)` with induced proper map of fixed
loci `h`, the Borel–Moore pushforward of the trace class of `u` is the trace class of the pushed
correspondence: `h_* Tr_c(u) = Tr_b([f, g]_! u)` (blueprint `thm-trf-trace-proper-compatibility`,
`sk-p-proper`). The proof goes through the exchange of the evaluation kernels along `f`
(`ProEtale.CondensedRing.kernelPushforward_comp_evaluationKernel_lowerStar`, blueprint
`lem-trf-trace-map-exchange`, (1)), of the support isomorphisms (`lem-trf-trace-map-exchange`,
(2)) and of the trace-class sources (`lem-trf-trace-source-exchange`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- Bookkeeping for the proper pushforward of the trace class (blueprint
`thm-trf-trace-proper-compatibility`, Step 4): two chains of points through a square agree. -/
private lemma comp_eq_comp_of_points {C : Type*} [Category C]
    {P₀ P₁ P₂ P₃ P₄ P₅ Q₁ Q₂ Q₃ Q₄ Q₅ R₁ R₂ S₁ S₂ N : C}
    (a₁ : P₀ ⟶ P₁) (a₂ : P₁ ⟶ P₂) (a₃ : P₂ ⟶ P₃) (a₄ : P₃ ⟶ P₄) (t : P₄ ⟶ P₅)
    (b₁ : P₀ ⟶ Q₁) (b₂ : Q₁ ⟶ Q₂) (b₃ : Q₂ ⟶ Q₃) (b₄ : Q₃ ⟶ Q₄) (t' : Q₄ ⟶ Q₅)
    (e₁ : Q₅ ⟶ R₁) (e₂ : R₁ ⟶ R₂) (e₃ : R₂ ⟶ P₅) (f₁ : Q₄ ⟶ S₁) (f₂ : S₁ ⟶ S₂) (f₃ : S₂ ⟶ P₄)
    (z : P₀ ⟶ S₁) (w : P₀ ⟶ S₂) (r : P₅ ⟶ N)
    (hnat : t' ≫ e₁ ≫ e₂ ≫ e₃ = f₁ ≫ f₂ ≫ f₃ ≫ t) (hpg : b₁ ≫ b₂ ≫ b₃ ≫ b₄ ≫ f₁ = z)
    (htr : z ≫ f₂ = w) (hhb : a₁ ≫ a₂ ≫ a₃ ≫ a₄ = w ≫ f₃) :
    a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ t ≫ r = b₁ ≫ b₂ ≫ b₃ ≫ b₄ ≫ t' ≫ e₁ ≫ e₂ ≫ e₃ ≫ r := by
  rw [reassoc_of% hnat]
  simp only [← Category.assoc] at hpg hhb ⊢
  rw [hpg, hhb, ← htr]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence.ProperPushforwardDiagram

variable {c : Correspondence ℓ K} {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (P : c.ProperPushforwardDiagram Y) (Fc : c.FixedLocus)
  (Fb : P.pushforward.FixedLocus)

set_option maxHeartbeats 3000000 in
-- composite functors on bounded constructible complexes are unfolded
/-- The point `T_b = 𝔱 ∘ ũ` of the pushed correspondence is obtained from that of `c` by
transport along `g` (blueprint `thm-trf-trace-proper-compatibility`, Step 3):
`T_b = Ri_{b*} τ_h ∘ Rg_* T_c ∘ η_g`. -/
lemma mate_comp_traceMap_pushforward :
    P.pushforward.mate ≫ P.pushforward.traceMap Fb =
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ P.g).unit.app (𝟙_ _) ≫
          (boundedConstructibleLowerStar ℓ P.g).map
            (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ P.g)).inv) ≫
        (boundedConstructibleLowerStar ℓ P.g).map (c.mate ≫ c.traceMap Fc) ≫
        (boundedConstructibleLowerStarComp ℓ Fc.ι P.g).hom.app (dualizingComplex' ℓ Fc.F) ≫
        eqToHom (by rw [← P.fixMap_ι]) ≫
        (boundedConstructibleLowerStarComp ℓ (P.fixMap Fc Fb) Fb.ι).inv.app
          (dualizingComplex' ℓ Fc.F) ≫
        (boundedConstructibleLowerStar ℓ Fb.ι).map
          (lowerStarDualizingComplexTrace ℓ (P.fixMap Fc Fb)) := by
  have e4 := Adjunction.homEquiv_comp_mateEquiv_of_eq
    (boundedConstructibleUpperShriekAdjunction ℓ c.support)
    (boundedConstructibleUpperShriekAdjunction ℓ P.pushforward.support)
    (lowerStarLowerShriekCompIso ℓ P.g_comp_support).hom
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ P.g).unit.app (𝟙_ _) ≫
      (boundedConstructibleLowerStar ℓ P.g).map
        (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ P.g)).inv)
    c.kernelClass (evaluationKernel ℓ K)
    ((boundedConstructibleLowerStarComp ℓ (diag X) (prod.map P.f P.f)).hom.app
          (dualizingComplex' ℓ X) ≫
        eqToHom (by rw [P.diag_comp_prodMap]) ≫
        (boundedConstructibleLowerStarComp ℓ P.f (diag Y)).inv.app (dualizingComplex' ℓ X) ≫
        (boundedConstructibleLowerStar ℓ (diag Y)).map (lowerStarDualizingComplexTrace ℓ P.f))
    (c.mate ≫ c.traceMap Fc) Fc.supportIso.hom
    (by rw [Category.assoc]; exact (mate_comp_traceMap_comp_supportIso c Fc).symm) _
    (lowerStarUpperShriekExchange ℓ P.g_comp_support)
    (by unfold lowerStarUpperShriekExchange; rfl)
    (P.lowerStar_map_supportIso_comp_exchange Fc Fb)
  have e1 := mate_comp_traceMap_comp_supportIso P.pushforward Fb
  rw [P.kernelClass_pushforward] at e1
  simp only [Category.assoc, P.kernelPushforward_comp_evaluationKernel] at e1
  have e5 := e1.trans e4
  rw [← cancel_mono Fb.supportIso.hom]
  simpa only [Category.assoc] using e5

set_option maxHeartbeats 3000000 in
-- composite functors on bounded constructible complexes are unfolded
/-- **Proper pushforward compatibility of the trace class** (blueprint
`thm-trf-trace-proper-compatibility`, `sk-p-proper`; Varshavsky 1.2.5): for a proper pushforward
diagram `(f, g) : (C, c) ⟶ (D, b)` with induced proper map of fixed loci `h`,
`h_* Tr_c(u) = Tr_b([f, g]_! u)`. No properness over `s` and no cartesian leg square are needed.
The special case `f = 𝟙` is blueprint `lem-trf-proper-pushforward-trace-class`. The proof goes
through the exchange of the trace maps (`lem-trf-trace-map-exchange`) and of the trace-class
sources (`lem-trf-trace-source-exchange`). -/
theorem traceClassPushforward_eq :
    P.traceClassPushforward Fc Fb = P.pushforward.traceClass Fb := by
  have hTc : c.mate ≫ c.traceMap Fc =
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ Fc.ι).homEquiv _ _
        ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ Fc.ι)).inv ≫
          c.traceClass Fc) := by
    rw [traceClass, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]
  have key : (boundedConstructibleUpperStarLowerStarAdjunction ℓ Fb.ι).homEquiv _ _
      ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ Fb.ι)).inv ≫
        P.traceClassPushforward Fc Fb) = P.pushforward.mate ≫ P.pushforward.traceMap Fb := by
    rw [P.mate_comp_traceMap_pushforward Fc Fb, hTc]
    simp only [Adjunction.homEquiv_unit, traceClassPushforward, BorelMooreSection.pushforward,
      lowerStarDualizingComplexTrace, Functor.map_comp, Category.assoc]
    have hpg := Adjunction.unit_map_comp_unit_map
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ Fc.ι)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ P.g)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ
        (Fc.ι ≫ P.g))
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ Fc.ι P.g)
      (boundedConstructibleLowerStarComp ℓ Fc.ι P.g)
      rfl _ _ _ (boundedConstructibleUpperStarComp_hom_app_unit ℓ Fc.ι P.g)
    have hhb := Adjunction.unit_map_comp_unit_map
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ
        (P.fixMap Fc Fb))
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ Fb.ι)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ
        (P.fixMap Fc Fb ≫ Fb.ι))
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
        (P.fixMap Fc Fb) Fb.ι)
      (boundedConstructibleLowerStarComp ℓ
        (P.fixMap Fc Fb) Fb.ι)
      rfl _ _ _
      (boundedConstructibleUpperStarComp_hom_app_unit ℓ (P.fixMap Fc Fb) Fb.ι)
    have htr := unit_comp_map_εIso_inv_comp_eqToHom_of_eq (ℓ := ℓ) (P.fixMap_ι Fc Fb).symm
    have n1 := (boundedConstructibleLowerStarComp ℓ
      Fc.ι P.g).hom.naturality (c.traceClass Fc)
    have n2 := lowerStar_map_comp_eqToHom_of_eq (ℓ := ℓ) (P.fixMap_ι Fc Fb).symm
      (c.traceClass Fc)
    have n3 := (boundedConstructibleLowerStarComp ℓ
      (P.fixMap Fc Fb) Fb.ι).inv.naturality (c.traceClass Fc)
    simp only [Functor.comp_map] at n1 n3
    refine comp_eq_comp_of_points _ _ _ _ _ _ _ _ _ _ _ _ _
      ((boundedConstructibleLowerStarComp ℓ
        Fc.ι P.g).hom.app (𝟙_ _))
      (eqToHom (congrArg (fun r : Fc.F ⟶ P.D ↦
        (boundedConstructibleLowerStar ℓ r).obj (𝟙_ _))
          (P.fixMap_ι Fc Fb).symm))
      ((boundedConstructibleLowerStarComp ℓ (P.fixMap Fc Fb)
        Fb.ι).inv.app (𝟙_ _))
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
          (Fc.ι ≫ P.g)).unit.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar ℓ (Fc.ι ≫ P.g)).map
          (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (Fc.ι ≫ P.g))).inv) _ _
      ?_ ?_ htr ?_
    · rw [reassoc_of% n1, reassoc_of% n2, n3]
    · simp only [Functor.map_comp, Category.assoc] at hpg
      rw [reassoc_of% hpg, Iso.inv_hom_id_app, Category.comp_id]
    · simpa only [Functor.map_comp, Category.assoc] using hhb
  rw [traceClass, ← key, Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]

end Correspondence.ProperPushforwardDiagram

end AlgebraicGeometry.ProEtale.CondensedRing
