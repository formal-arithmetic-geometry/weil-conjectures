/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps
public import Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
import Sheaf.AlgebraicGeometry.StrictTowerDirectImageCoherence
import WeilConjectures.Compactification.Cofiltered
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus

/-!
# Refinement exchange coherence for strict pro-etale towers

Source: Stacks Project, Tags 0F7B, 0F7C and 0F7F; the final independence and naturality
argument of the blueprint proof of `thm-cbc-complete-proetale`
(blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence).

`compositionF`, `compositionC` and `compositionE` are the already published canonical
compactification candidate, refinement comparison and proper/open exchange. The wrappers
below only supply quasi-compactness and invertibility, not a new choice of any operation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The proper-adjunction mate determines the proper/open comparison uniquely.
Source: equality elimination and Stacks, Tag 07A7
(blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence).
Proof: use the displayed mate itself; any other transformation equal to it is the same.
This keeps its large construction behind a theorem when components are compared. -/
private theorem refinementGamma_existsUnique {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : ∃! δ : R B r ⋙ J B i ⟶ J B k ⋙ R B p,
      δ = gamma B k r p i h := by
  exact ⟨_, rfl, fun _ hδ ↦ hδ⟩

/-- The proper/open comparison is exactly the proper-adjunction mate of alpha.
Source: Stacks, Tags 0F7B and 07A7
(blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence). -/
private noncomputable def refinementGamma {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : R B r ⋙ J B i ⟶ J B k ⋙ R B p :=
  Classical.choose (refinementGamma_existsUnique B k r p i h)

/-- The normalized comparison is the original proper-adjunction mate.
Source: Stacks, Tag 07A7 (blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence).
Proof: the defining choice has the displayed equality by its specification. -/
private theorem refinementGamma_eq {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : refinementGamma B k r p i h =
      gamma B k r p i h :=
  (Classical.choose_spec (refinementGamma_existsUnique B k r p i h)).1

private theorem refinementExchange_existsUnique :
    ∃! E : ExchangeFamily (Derived B) (G B) (R B), @E = @exchange.{u} B _ := by
  exact ⟨@exchange.{u} B _, rfl, fun _ hE ↦ hE⟩

private noncomputable def refinementExchange : ExchangeFamily (Derived B) (G B) (R B) :=
  @Classical.choose (ExchangeFamily (Derived B) (G B) (R B)) _
    (refinementExchange_existsUnique B)

private theorem refinementExchange_eq : @refinementExchange.{u} B _ = @exchange.{u} B _ :=
  (@Classical.choose_spec (ExchangeFamily (Derived B) (G B) (R B)) _
    (refinementExchange_existsUnique B)).1

private theorem refinementExchange_app_eq {W X Y Z : Scheme.{u}}
    (a : W ⟶ X) (f' : W ⟶ Y) (f : X ⟶ Z) (b : Y ⟶ Z)
    (w : a ≫ f = f' ≫ b) :
    refinementExchange B a f' f b w = exchange B a f' f b w := by
  exact congrArg (fun E : ExchangeFamily (Derived B) (G B) (R B) ↦ E a f' f b w)
    (refinementExchange_eq B)

private theorem refinementMatePasting :
    matePastingLaw (G B) (R B) (@rCompEq.{u} B _) (@refinementExchange.{u} B _) := by
  exact (congrArg (matePastingLaw (G B) (R B) (@rCompEq.{u} B _))
    (refinementExchange_eq B)).mpr (strictTowerMatePasting B)

private theorem refinementMateIdentity :
    mateIdentityLaw (G B) (R B) (rId B) (@refinementExchange.{u} B _) := by
  exact (congrArg (mateIdentityLaw (G B) (R B) (rId B))
    (refinementExchange_eq B)).mpr (strictTowerMateIdentity B)

/-- The existing normalized refinement map, with open quasi-compactness obtained from f.
The explicit proof argument allows the same construction on a pulled-back f without
adding a quasi-compactness hypothesis on the base change.
Source: Stacks, Tags 0F7B and 0F7C, identity-left proper/open square
(blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence). -/
noncomputable def refinementComparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (hf : QuasiCompact f := by infer_instance) :
    compositionF B c₂ ⟶ compositionF B c₁ := by
  letI : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion hf
  letI : QuasiCompact c₂.i := c₂.quasiCompact_openImmersion hf
  exact compositionC B r

private noncomputable def refinementR {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) :
    R B r.hom ⋙ R B c₂.g ≅ R B c₁.g :=
  rCompEq B r.hom c₂.g c₁.g r.hom_g

private noncomputable def refinementPasting {A C D E : Type*}
    [Category A] [Category C] [Category D] [Category E]
    (J₁ : A ⥤ C) (J₂ : A ⥤ D) (R₀ : A ⥤ A) (R₁ : C ⥤ D) (R₂ : D ⥤ E)
    (H : C ⥤ E) (e₀ : R₀ ≅ 𝟭 A) (e₁ : R₁ ⋙ R₂ ≅ H)
    (g : R₀ ⋙ J₂ ⟶ J₁ ⋙ R₁) : J₂ ⋙ R₂ ⟶ J₁ ⋙ H :=
  Functor.whiskerRight
    ((Functor.leftUnitor J₂).inv ≫ Functor.whiskerRight e₀.inv J₂ ≫ g) R₂ ≫
    (Functor.associator J₁ R₁ R₂).hom ≫ Functor.whiskerLeft J₁ e₁.hom

private theorem comparison_factor_isIso {A C C₂ D : Type*}
    [Category A] [Category C] [Category C₂] [Category D]
    (J₁ : A ⥤ C) (J₂ : A ⥤ C₂) (R₀ : A ⥤ A) (R₁ : C ⥤ C₂) (R₂ : C₂ ⥤ D)
    (H : C ⥤ D) (e₀ : R₀ ≅ 𝟭 A) (e₁ : R₁ ⋙ R₂ ≅ H)
    (g : R₀ ⋙ J₂ ⟶ J₁ ⋙ R₁) (M : A) [IsIso (g.app M)] :
    IsIso ((refinementPasting J₁ J₂ R₀ R₁ R₂ H e₀ e₁ g).app M) := by
  dsimp only [refinementPasting, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

-- Transport before specializing the component formula, to avoid expanding derived functors.
private theorem comparison_transport_isIso {A C D E : Type*}
    [Category A] [Category C] [Category D] [Category E]
    (J₁ : A ⥤ C) (J₂ : A ⥤ D) (R₀ : A ⥤ A) (R₁ : C ⥤ D) (R₂ : D ⥤ E)
    (H : C ⥤ E) (e₀ : R₀ ≅ 𝟭 A) (e₁ : R₁ ⋙ R₂ ≅ H)
    (g : R₀ ⋙ J₂ ⟶ J₁ ⋙ R₁) (a : J₂ ⋙ R₂ ⟶ J₁ ⋙ H)
    (ha : a = refinementPasting J₁ J₂ R₀ R₁ R₂ H e₀ e₁ g)
    (M : A) (hg : IsIso (g.app M)) : IsIso (a.app M) := by
  subst a
  exact comparison_factor_isIso J₁ J₂ R₀ R₁ R₂ H e₀ e₁ g M

private theorem refinementComparison_factor {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) (hf : QuasiCompact f) :
    let : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion hf
    let : QuasiCompact c₂.i := c₂.quasiCompact_openImmersion hf
    refinementComparison B r hf =
      refinementPasting (J B c₁.i) (J B c₂.i) (R B (𝟙 X)) (R B r.hom)
        (R B c₂.g) (R B c₁.g) (rId B X) (refinementR B r)
        (refinementGamma B c₁.i (𝟙 X) r.hom c₂.i
          (r.i_hom.trans (Category.id_comp c₂.i).symm)) := by
  dsimp only
  unfold refinementComparison compositionC refinementR
  rw [refinementGamma_eq, rCompEq_eq]
  rfl

/-- Invertibility of the comparison on the finite scalar etale-origin domain.
Source: Stacks, Tag 0F7B; item proof steps 1 and 2
(blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence).
Proof: the refinement gives the proper/open square with top c₁.i, bottom c₂.i,
left identity and right r.hom. Apply gamma_isIso at M with its given origin at each
level, then apply the functor R of c₂.g. The identity and direct-image compositors
in compositionC are isomorphisms, so the resulting refinement comparison is invertible. -/
theorem refinementComparison_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M)))
    (hf : QuasiCompact f := by infer_instance) :
    IsIso ((refinementComparison B r hf).app M) := by
  let : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion hf
  let : QuasiCompact c₂.i := c₂.quasiCompact_openImmersion hf
  exact comparison_transport_isIso (J B c₁.i) (J B c₂.i) (R B (𝟙 X))
    (R B r.hom) (R B c₂.g) (R B c₁.g) (rId B X)
    (refinementR B r)
    (refinementGamma B c₁.i (𝟙 X) r.hom c₂.i
      (r.i_hom.trans (Category.id_comp c₂.i).symm))
    (refinementComparison B r hf) (refinementComparison_factor B r hf) M
    (by
      rw [refinementGamma_eq]
      exact gamma_isIso B c₁.i (𝟙 X) r.hom c₂.i
        (r.i_hom.trans (Category.id_comp c₂.i).symm) M hM)

/-- Pullback preserves the exact finite scalar etale-origin domain used in this item.
Source: blueprint, thm-cbc-complete-proetale, final naturality argument; Stacks, Tag 04JC
and Section 0735; item proof step 2
(blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence).
Proof: evaluation commutes with G. At level n keep the same finite ring Λ_n and
B-algebra map. Constant-coefficient scalar restriction commutes with inverse image,
and the site-comparison pullback isomorphism identifies pullback of ν*L_n with
ν* of etale inverse image of L_n. Exactness of etale inverse image preserves the
lower bound of this L_n. This supplies a ScalarEtaleOrigin at each n, without a
common coefficient ring or a uniform lower bound. -/
theorem refinementFiniteOrigin_pullback {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M))) :
    ∀ n : ℕ,
      Nonempty (ScalarEtaleOrigin B X' ((ev B X' n).obj ((G B g').obj M))) := by
  intro n
  classical
  let w := Classical.choice (hM n)
  let L := (Etale.upperStar (ModuleCat.{u + 1} w.Λ) g').mapDerivedCategoryPlus.obj
    w.origin.L
  let F := (finiteCoefficientComparison X' w.Λ).mapDerivedCategoryPlus.obj L
  let w' : ScalarEtaleOrigin B X'
      ((finiteRestriction B X' w.Λ w.φ).mapDerivedCategory.obj F.obj) :=
    { Λ := w.Λ
      φ := w.φ
      F := F
      origin := ⟨L, Iso.refl _⟩
      iso := Iso.refl _ }
  have := hPullbackInv_isIso B g' w.Λ w.φ
  let e : (Etale.upperStar (ModuleCat.{u + 1} w.Λ) g').mapDerivedCategoryPlus ⋙
        HD B X' w.Λ w.φ ≅
      HD B X w.Λ w.φ ⋙ (modulePullback B g').mapDerivedCategory :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
          Functor.mapDerivedCategoryPlusNatIso (asIso (hPullbackInv B g' w.Λ w.φ)).symm ≪≫
          Functor.mapDerivedCategoryPlusCompIso _ _) DerivedCategory.Plus.ι ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (H B X w.Λ w.φ).mapDerivedCategoryPlus
        (modulePullback B g').mapDerivedCategoryPlusCompatibility ≪≫
      (Functor.associator _ _ _).symm
  exact ⟨{ w' with
    iso := (originIso B w').symm ≪≫ e.app w.origin.L ≪≫
      (modulePullback B g').mapDerivedCategory.mapIso (originIso B w) ≪≫
      ((evalG B g' n).app M).symm }⟩

/-- The actual common-refinement isomorphism C_{u₂}⁻¹ C_{u₁}, with no arbitrary choice.
Source: blueprint, thm-cbc-complete-proetale, final independence argument; item step 5
(blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence). -/
noncomputable def refinementCommonComparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ d : Compactification f} (u₁ : d.Refinement c₁) (u₂ : d.Refinement c₂)
    (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M)))
    (hf : QuasiCompact f := by infer_instance) :
    (compositionF B c₁).obj M ≅ (compositionF B c₂).obj M := by
  letI := refinementComparison_isIso B u₁ M hM hf
  letI := refinementComparison_isIso B u₂ M hM hf
  exact asIso ((refinementComparison B u₁ hf).app M) ≪≫
    (asIso ((refinementComparison B u₂ hf).app M)).symm


set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
-- Work with whole natural transformations before specializing components.
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] G R J rId rComp gamma adj exchange
  towers_hasDerivedCategory

private theorem normalized_open_comp {A C D E : Type*}
    [Category A] [Category C] [Category D] [Category E]
    (Jc : A ⥤ C) (Jd : A ⥤ D) (Je : A ⥤ E)
    (R₀ : A ⥤ A) (Rr : D ⥤ C) (Rs : E ⥤ D) (Rsr : E ⥤ C)
    (e₀ : R₀ ≅ 𝟭 A) (k : Rs ⋙ Rr ≅ Rsr) (t : R₀ ⋙ R₀ ≅ R₀)
    (gr : R₀ ⋙ Jc ⟶ Jd ⋙ Rr) (gs : R₀ ⋙ Jd ⟶ Je ⋙ Rs)
    (gsr : R₀ ⋙ Jc ⟶ Je ⋙ Rsr) (M : A)
    (ht : t.hom.app M = R₀.map (e₀.hom.app M))
    (hv : Jc.map (t.hom.app M) ≫ gsr.app M ≫ k.inv.app (Je.obj M) =
      gr.app (R₀.obj M) ≫ Rr.map (gs.app M)) :
    Jc.map (e₀.inv.app M) ≫ gsr.app M =
      (Jc.map (e₀.inv.app M) ≫ gr.app M) ≫
        Rr.map (Jd.map (e₀.inv.app M) ≫ gs.app M) ≫ k.hom.app (Je.obj M) := by
  simp only [Functor.map_comp, Category.assoc]
  have hn := gr.naturality (e₀.inv.app M)
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  rw [← Category.assoc (gr.app M), ← hn]
  simp only [Category.assoc]
  rw [← Category.assoc (gr.app (R₀.obj M)), ← hv, ht]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← Category.assoc (Jc.map (R₀.map (e₀.inv.app M)))]
  simp [← Functor.map_comp]

private theorem normalized_comparison_comp {A C D E T : Type*}
    [Category A] [Category C] [Category D] [Category E] [Category T]
    (Jc : A ⥤ C) (Jd : A ⥤ D) (Je : A ⥤ E)
    (P : C ⥤ T) (Q : D ⥤ T) (S : E ⥤ T)
    (Rr : D ⥤ C) (Rs : E ⥤ D) (Rsr : E ⥤ C)
    (pr : Rr ⋙ P ≅ Q) (ps : Rs ⋙ Q ≅ S) (psr : Rsr ⋙ P ≅ S)
    (k : Rs ⋙ Rr ≅ Rsr)
    (tr : Jc ⟶ Jd ⋙ Rr) (ts : Jd ⟶ Je ⋙ Rs) (tsr : Jc ⟶ Je ⋙ Rsr)
    (ht : ∀ M, tsr.app M = tr.app M ≫ Rr.map (ts.app M) ≫ k.hom.app (Je.obj M))
    (hp : ∀ N, P.map (k.hom.app N) ≫ psr.hom.app N =
      pr.hom.app (Rs.obj N) ≫ ps.hom.app N) (M : A) :
    P.map (tsr.app M) ≫ psr.hom.app (Je.obj M) =
      (P.map (tr.app M) ≫ pr.hom.app (Jd.obj M)) ≫
        Q.map (ts.app M) ≫ ps.hom.app (Je.obj M) := by
  rw [ht]
  simp only [Functor.map_comp, Category.assoc]
  rw [hp]
  have hn := pr.hom.naturality (ts.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← Category.assoc (pr.hom.app _), ← hn]
  simp only [Category.assoc]

private theorem normalized_comparison_id {A C D : Type*}
    [Category A] [Category C] [Category D]
    (J₀ : A ⥤ C) (P : C ⥤ D) (I : A ⥤ A) (I' : C ⥤ C)
    (e : I ≅ 𝟭 A) (e' : I' ≅ 𝟭 C) (γ : I ⋙ J₀ ⟶ J₀ ⋙ I')
    (k : I' ⋙ P ≅ P) (M : A)
    (hγ : γ.app M ≫ e'.hom.app (J₀.obj M) = J₀.map (e.hom.app M))
    (hk : k.hom.app (J₀.obj M) = P.map (e'.hom.app (J₀.obj M))) :
    P.map (J₀.map (e.inv.app M) ≫ γ.app M) ≫ k.hom.app (J₀.obj M) = 𝟙 _ := by
  rw [hk, ← P.map_comp, Category.assoc, hγ, ← J₀.map_comp]
  simp

private theorem normalized_open_exchange {A C D A' C' D' : Type*}
    [Category A] [Category C] [Category D]
    [Category A'] [Category C'] [Category D']
    (J₁ : A ⥤ C) (J₂ : A ⥤ D) (J₁' : A' ⥤ C') (J₂' : A' ⥤ D')
    (I : A ⥤ A) (I' : A' ⥤ A') (Rr : C ⥤ D) (Rr' : C' ⥤ D')
    (L : A ⥤ A') (L₁ : C ⥤ C') (L₂ : D ⥤ D')
    (e : I ≅ 𝟭 A) (e' : I' ≅ 𝟭 A')
    (γ : I ⋙ J₂ ⟶ J₁ ⋙ Rr) (γ' : I' ⋙ J₂' ⟶ J₁' ⋙ Rr')
    (β₁ : J₁ ⋙ L₁ ⟶ L ⋙ J₁') (β₂ : J₂ ⋙ L₂ ⟶ L ⋙ J₂')
    (ex : Rr ⋙ L₂ ⟶ L₁ ⋙ Rr') (ex₀ : I ⋙ L ⟶ L ⋙ I') (M : A)
    (hc : L₂.map (γ.app M) ≫ ex.app (J₁.obj M) ≫ Rr'.map (β₁.app M) =
      β₂.app (I.obj M) ≫ J₂'.map (ex₀.app M) ≫ γ'.app (L.obj M))
    (hi : ex₀.app M ≫ e'.hom.app (L.obj M) = L.map (e.hom.app M)) :
    L₂.map (J₂.map (e.inv.app M) ≫ γ.app M) ≫
        ex.app (J₁.obj M) ≫ Rr'.map (β₁.app M) =
      β₂.app M ≫ J₂'.map (e'.inv.app (L.obj M)) ≫ γ'.app (L.obj M) := by
  have hi' : L.map (e.inv.app M) ≫ ex₀.app M = e'.inv.app (L.obj M) := by
    apply (cancel_mono (e'.hom.app (L.obj M))).1
    rw [Category.assoc, hi]
    simp [← Functor.map_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [hc]
  have hn := β₂.naturality (e.inv.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← Category.assoc (L₂.map _), hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, hi']
  rfl

private theorem normalized_comparison_exchange {A C₁ C₂ T A' C₁' C₂' T' : Type*}
    [Category A] [Category C₁] [Category C₂] [Category T]
    [Category A'] [Category C₁'] [Category C₂'] [Category T']
    (J₁ : A ⥤ C₁) (J₂ : A ⥤ C₂) (J₁' : A' ⥤ C₁') (J₂' : A' ⥤ C₂')
    (Rr : C₁ ⥤ C₂) (Rr' : C₁' ⥤ C₂')
    (P₁ : C₁ ⥤ T) (P₂ : C₂ ⥤ T) (P₁' : C₁' ⥤ T') (P₂' : C₂' ⥤ T')
    (L : A ⥤ A') (L₁ : C₁ ⥤ C₁') (L₂ : C₂ ⥤ C₂') (Lt : T ⥤ T')
    (o : J₂ ⟶ J₁ ⋙ Rr) (o' : J₂' ⟶ J₁' ⋙ Rr')
    (κ : Rr ⋙ P₂ ≅ P₁) (κ' : Rr' ⋙ P₂' ≅ P₁')
    (β₁ : J₁ ⋙ L₁ ⟶ L ⋙ J₁') (β₂ : J₂ ⋙ L₂ ⟶ L ⋙ J₂')
    (er : Rr ⋙ L₂ ⟶ L₁ ⋙ Rr')
    (e₁ : P₁ ⋙ Lt ⟶ L₁ ⋙ P₁') (e₂ : P₂ ⋙ Lt ⟶ L₂ ⋙ P₂')
    (ho : ∀ M, L₂.map (o.app M) ≫ er.app (J₁.obj M) ≫ Rr'.map (β₁.app M) =
      β₂.app M ≫ o'.app (L.obj M))
    (hκ : ∀ N, Lt.map (κ.hom.app N) ≫ e₁.app N =
      e₂.app (Rr.obj N) ≫ P₂'.map (er.app N) ≫ κ'.hom.app (L₁.obj N)) (M : A) :
    (e₂.app (J₂.obj M) ≫ P₂'.map (β₂.app M)) ≫
        P₂'.map (o'.app (L.obj M)) ≫ κ'.hom.app (J₁'.obj (L.obj M)) =
      Lt.map (P₂.map (o.app M) ≫ κ.hom.app (J₁.obj M)) ≫
        e₁.app (J₁.obj M) ≫ P₁'.map (β₁.app M) := by
  simp only [Category.assoc, Functor.map_comp]
  rw [← Functor.map_comp_assoc, ← ho]
  simp only [Functor.map_comp, Category.assoc]
  have hn := e₂.naturality (o.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← Category.assoc (e₂.app _), ← hn]
  simp only [Category.assoc]
  have hk := κ'.hom.naturality (β₁.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hk
  rw [hk]
  simpa only [Category.assoc] using congrArg
    (fun t ↦ Lt.map (P₂.map (o.app M)) ≫ t ≫ P₁'.map (β₁.app M))
      (hκ (J₁.obj M)).symm

private theorem refinementPasting_comp {A C D E T : Type*}
    [Category A] [Category C] [Category D] [Category E] [Category T]
    (Jc : A ⥤ C) (Jd : A ⥤ D) (Je : A ⥤ E) (I : A ⥤ A)
    (Rr : D ⥤ C) (Rs : E ⥤ D) (Rsr : E ⥤ C)
    (P : C ⥤ T) (Q : D ⥤ T) (S : E ⥤ T)
    (e : I ≅ 𝟭 A) (t : I ⋙ I ≅ I) (k : Rs ⋙ Rr ≅ Rsr)
    (pr : Rr ⋙ P ≅ Q) (ps : Rs ⋙ Q ≅ S) (psr : Rsr ⋙ P ≅ S)
    (gr : I ⋙ Jc ⟶ Jd ⋙ Rr) (gs : I ⋙ Jd ⟶ Je ⋙ Rs)
    (gsr : I ⋙ Jc ⟶ Je ⋙ Rsr)
    (hu : ∀ M, t.hom.app M = I.map (e.hom.app M))
    (hv : ∀ M, Jc.map (t.hom.app M) ≫ gsr.app M ≫ k.inv.app (Je.obj M) =
      gr.app (I.obj M) ≫ Rr.map (gs.app M))
    (hp : ∀ N, P.map (k.hom.app N) ≫ psr.hom.app N =
      pr.hom.app (Rs.obj N) ≫ ps.hom.app N) :
    refinementPasting Je Jc I Rsr P S e psr gsr =
      refinementPasting Jd Jc I Rr P Q e pr gr ≫
        refinementPasting Je Jd I Rs Q S e ps gs := by
  let tr := (Functor.leftUnitor Jc).inv ≫ Functor.whiskerRight e.inv Jc ≫ gr
  let ts := (Functor.leftUnitor Jd).inv ≫ Functor.whiskerRight e.inv Jd ≫ gs
  let tsr := (Functor.leftUnitor Jc).inv ≫ Functor.whiskerRight e.inv Jc ≫ gsr
  have ht : ∀ M, tsr.app M = tr.app M ≫ Rr.map (ts.app M) ≫ k.hom.app (Je.obj M) := by
    intro M
    simpa only [tr, ts, tsr, NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.whiskerRight_app, Category.id_comp] using
      normalized_open_comp Jc Jd Je I Rr Rs Rsr e k t gr gs gsr M (hu M) (hv M)
  ext M
  simpa only [refinementPasting, tr, ts, tsr, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp] using
    normalized_comparison_comp Jc Jd Je P Q S Rr Rs Rsr pr ps psr k tr ts tsr ht hp M

private theorem refinementPasting_id {A C D : Type*}
    [Category A] [Category C] [Category D]
    (Jc : A ⥤ C) (P : C ⥤ D) (I : A ⥤ A) (I' : C ⥤ C)
    (e : I ≅ 𝟭 A) (e' : I' ≅ 𝟭 C) (γ : I ⋙ Jc ⟶ Jc ⋙ I')
    (k : I' ⋙ P ≅ P)
    (hγ : ∀ M, γ.app M ≫ e'.hom.app (Jc.obj M) = Jc.map (e.hom.app M))
    (hk : ∀ N, k.hom.app N = P.map (e'.hom.app N)) :
    refinementPasting Jc Jc I I' P P e k γ = 𝟙 _ := by
  ext M
  simpa only [refinementPasting, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.leftUnitor_inv_app,
    Category.id_comp, NatTrans.id_app, Functor.comp_obj, Functor.id_obj] using
    normalized_comparison_id Jc P I I' e e' γ k M (hγ M) (hk (Jc.obj M))

private theorem rCompEq_id_id (X : Scheme.{u}) :
    rCompEq B (𝟙 X) (𝟙 X) (𝟙 X) (Category.id_comp _) = rComp B (𝟙 X) (𝟙 X) := by
  rw [rCompEq_eq]
  simp only [eqToIso_refl, Iso.trans_refl]

private theorem normalize_refinement_vertical
    {C : Scheme.{u} → Type*} [∀ X, Category.{u + 2} (C X)]
    (R₀ : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → (C X ⥤ C Y))
    (J₀ : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j], C U ⥤ C X)
    (γ : ∀ {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
      (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (_h : k ≫ p = r ≫ i), R₀ r ⋙ J₀ i ⟶ J₀ k ⋙ R₀ p)
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d e : Compactification f}
    (r : d.Refinement c) (s : e.Refinement d)
    [QuasiCompact c.i] [QuasiCompact d.i] [QuasiCompact e.i]
    (t : R₀ (𝟙 X) ⋙ R₀ (𝟙 X) ≅ R₀ (𝟙 X))
    (q q₀ : R₀ s.hom ⋙ R₀ r.hom ≅ R₀ (s.hom ≫ r.hom))
    (hq : q₀ = q) (M : C X)
    (hv : (J₀ c.i).map (t.hom.app M) ≫
      (γ e.i ((𝟙 X) ≫ (𝟙 X)) (s.hom ≫ r.hom) c.i
        ((s.comp r).i_hom.trans (Category.id_comp _).symm)).app M ≫
      q₀.inv.app ((J₀ e.i).obj M) =
      (γ d.i (𝟙 X) r.hom c.i (r.i_hom.trans (Category.id_comp _).symm)).app
        ((R₀ (𝟙 X)).obj M) ≫
      (R₀ r.hom).map ((γ e.i (𝟙 X) s.hom d.i
        (s.i_hom.trans (Category.id_comp _).symm)).app M)) :
    (J₀ c.i).map (t.hom.app M) ≫
      (γ e.i (𝟙 X) (s.comp r).hom c.i
        ((s.comp r).i_hom.trans (Category.id_comp _).symm)).app M ≫
      q.inv.app ((J₀ e.i).obj M) =
      (γ d.i (𝟙 X) r.hom c.i (r.i_hom.trans (Category.id_comp _).symm)).app
        ((R₀ (𝟙 X)).obj M) ≫
      (R₀ r.hom).map ((γ e.i (𝟙 X) s.hom d.i
        (s.i_hom.trans (Category.id_comp _).symm)).app M) := by
  rw [← hq]
  exact hv

private theorem equation_comp_transfer {C : Type*} [Category C] {X Y Z : C}
    (a a' : X ⟶ Y) (b b' : Y ⟶ Z) (c c' : X ⟶ Z)
    (ha : a = a') (hb : b = b') (hc : c = c') (h : c' = a' ≫ b') :
    c = a ≫ b := by
  rw [ha, hb, hc]
  exact h

private theorem rCompEq_refl {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    rCompEq B f g (f ≫ g) rfl = rComp B f g := by
  rw [rCompEq_eq]
  simp only [eqToIso_refl, Iso.trans_refl]

private theorem refinement_compositor_assoc {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d e : Compactification f} (r : d.Refinement c) (s : e.Refinement d)
    (N : Derived B e.Z) :
    (R B c.g).map ((rCompEq B s.hom r.hom (s.hom ≫ r.hom) rfl).hom.app N) ≫
      (refinementR B (s.comp r)).hom.app N =
    (refinementR B r).hom.app ((R B s.hom).obj N) ≫
      (refinementR B s).hom.app N := by
  simpa only [refinementR, Compactification.Refinement.comp] using
    (strictTowerDirectImageCoherence B).2.1 s.hom r.hom c.g
      (s.hom ≫ r.hom) d.g e.g rfl r.hom_g (s.comp r).hom_g s.hom_g N

private theorem refinementComparison_comp {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d e : Compactification f} (r : d.Refinement c) (s : e.Refinement d)
    (hf : QuasiCompact f) :
    refinementComparison B (s.comp r) hf =
    refinementComparison B r hf ≫ refinementComparison B s hf := by
  let : QuasiCompact c.i := c.quasiCompact_openImmersion hf
  let : QuasiCompact d.i := d.quasiCompact_openImmersion hf
  let : QuasiCompact e.i := e.quasiCompact_openImmersion hf
  refine equation_comp_transfer _ _ _ _ _ _
    (refinementComparison_factor B r hf) (refinementComparison_factor B s hf)
    (refinementComparison_factor B (s.comp r) hf) ?_
  apply refinementPasting_comp (J B c.i) (J B d.i) (J B e.i) (R B (𝟙 X))
    (R B r.hom) (R B s.hom) (R B (s.hom ≫ r.hom))
    (R B c.g) (R B d.g) (R B e.g) (rId B X) (rComp B (𝟙 X) (𝟙 X))
    (rCompEq B s.hom r.hom (s.hom ≫ r.hom) rfl)
  · intro M
    simpa only [rCompEq_id_id] using (strictTowerDirectImageCoherence B).1 (𝟙 X) M
  · intro M
    let raw := (normalizedProperOpenCalculus B).1 e.i d.i c.i
      (𝟙 X) (𝟙 X) s.hom r.hom
      (s.i_hom.trans (Category.id_comp _).symm)
      (r.i_hom.trans (Category.id_comp _).symm)
      ((s.comp r).i_hom.trans (Category.id_comp _).symm) M
    simp only [← refinementGamma_eq] at raw
    exact normalize_refinement_vertical (@R.{u} B _) (@J.{u} B _)
      (@refinementGamma.{u} B _) r s (rComp B (𝟙 X) (𝟙 X))
      (rCompEq B s.hom r.hom (s.hom ≫ r.hom) rfl)
      (rComp B s.hom r.hom) (rCompEq_refl B s.hom r.hom).symm M raw
  · intro N
    exact refinement_compositor_assoc B r s N



private theorem refinementComparison_id {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (hf : QuasiCompact f) :
    refinementComparison B (Compactification.Refinement.id c) hf = 𝟙 _ := by
  let : QuasiCompact c.i := c.quasiCompact_openImmersion hf
  rw [refinementComparison_factor]
  dsimp only [refinementR, Compactification.Refinement.id]
  exact refinementPasting_id (J B c.i) (R B c.g) (R B (𝟙 X)) (R B (𝟙 c.Z))
    (rId B X) (rId B c.Z) (refinementGamma B c.i (𝟙 X) (𝟙 c.Z) c.i _)
    (refinementR B (Compactification.Refinement.id c)) (fun M ↦ by
      simpa only [refinementGamma_eq] using (gamma_identities B).1 c.i _ M)
    (fun N ↦ by
      simpa only [refinementR, Compactification.Refinement.id] using
        (strictTowerDirectImageCoherence B).1 c.g N)

private noncomputable def exchangePasting {A C T A' C' T' : Type*}
    [Category A] [Category C] [Category T] [Category A'] [Category C'] [Category T']
    (J : A ⥤ C) (P : C ⥤ T) (J' : A' ⥤ C') (P' : C' ⥤ T')
    (L : A ⥤ A') (Lc : C ⥤ C') (Lt : T ⥤ T')
    (β : J ⋙ Lc ⟶ L ⋙ J') (e : P ⋙ Lt ⟶ Lc ⋙ P') :
    (J ⋙ P) ⋙ Lt ⟶ L ⋙ (J' ⋙ P') :=
  (Functor.associator J P Lt).hom ≫ Functor.whiskerLeft J e ≫
    (Functor.associator J Lc P').inv ≫ Functor.whiskerRight β P' ≫
    (Functor.associator L J' P').hom

private theorem refinementPasting_exchange {A C₁ C₂ T A' C₁' C₂' T' : Type*}
    [Category A] [Category C₁] [Category C₂] [Category T]
    [Category A'] [Category C₁'] [Category C₂'] [Category T']
    (J₁ : A ⥤ C₁) (J₂ : A ⥤ C₂) (J₁' : A' ⥤ C₁') (J₂' : A' ⥤ C₂')
    (I : A ⥤ A) (I' : A' ⥤ A') (ei : I ≅ 𝟭 A) (ei' : I' ≅ 𝟭 A')
    (Rr : C₁ ⥤ C₂) (Rr' : C₁' ⥤ C₂')
    (P₁ : C₁ ⥤ T) (P₂ : C₂ ⥤ T) (P₁' : C₁' ⥤ T') (P₂' : C₂' ⥤ T')
    (L : A ⥤ A') (L₁ : C₁ ⥤ C₁') (L₂ : C₂ ⥤ C₂') (Lt : T ⥤ T')
    (γ : I ⋙ J₂ ⟶ J₁ ⋙ Rr) (γ' : I' ⋙ J₂' ⟶ J₁' ⋙ Rr')
    (κ : Rr ⋙ P₂ ≅ P₁) (κ' : Rr' ⋙ P₂' ≅ P₁')
    (β₁ : J₁ ⋙ L₁ ⟶ L ⋙ J₁') (β₂ : J₂ ⋙ L₂ ⟶ L ⋙ J₂')
    (er : Rr ⋙ L₂ ⟶ L₁ ⋙ Rr') (ex₀ : I ⋙ L ⟶ L ⋙ I')
    (e₁ : P₁ ⋙ Lt ⟶ L₁ ⋙ P₁') (e₂ : P₂ ⋙ Lt ⟶ L₂ ⋙ P₂')
    (hc : ∀ M, L₂.map (γ.app M) ≫ er.app (J₁.obj M) ≫ Rr'.map (β₁.app M) =
      β₂.app (I.obj M) ≫ J₂'.map (ex₀.app M) ≫ γ'.app (L.obj M))
    (hi : ∀ M, ex₀.app M ≫ ei'.hom.app (L.obj M) = L.map (ei.hom.app M))
    (hκ : ∀ N, Lt.map (κ.hom.app N) ≫ e₁.app N =
      e₂.app (Rr.obj N) ≫ P₂'.map (er.app N) ≫ κ'.hom.app (L₁.obj N)) :
    exchangePasting J₂ P₂ J₂' P₂' L L₂ Lt β₂ e₂ ≫
        Functor.whiskerLeft L (refinementPasting J₁' J₂' I' Rr' P₂' P₁' ei' κ' γ') =
      Functor.whiskerRight (refinementPasting J₁ J₂ I Rr P₂ P₁ ei κ γ) Lt ≫
        exchangePasting J₁ P₁ J₁' P₁' L L₁ Lt β₁ e₁ := by
  let o := (Functor.leftUnitor J₂).inv ≫ Functor.whiskerRight ei.inv J₂ ≫ γ
  let o' := (Functor.leftUnitor J₂').inv ≫ Functor.whiskerRight ei'.inv J₂' ≫ γ'
  have ho : ∀ M, L₂.map (o.app M) ≫ er.app (J₁.obj M) ≫ Rr'.map (β₁.app M) =
      β₂.app M ≫ o'.app (L.obj M) := by
    intro M
    simpa only [o, o', NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.whiskerRight_app, Category.id_comp] using
      normalized_open_exchange J₁ J₂ J₁' J₂' I I' Rr Rr' L L₁ L₂ ei ei'
        γ γ' β₁ β₂ er ex₀ M (hc M) (hi M)
  ext M
  simpa only [exchangePasting, refinementPasting, o, o', NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc] using
    normalized_comparison_exchange J₁ J₂ J₁' J₂' Rr Rr' P₁ P₂ P₁' P₂' L L₁ L₂ Lt
      o o' κ κ' β₁ β₂ er e₁ e₂ ho hκ M

private theorem compositionE_factor {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (c : Compactification f) (c' : Compactification f')
    (a : X' ⟶ X) (b : Y' ⟶ Y) (s : c'.Z ⟶ c.Z)
    (wi : a ≫ c.i = c'.i ≫ s) (wp : s ≫ c.g = c'.g ≫ b)
    (si : IsPullback a c'.i c.i s) :
    compositionE B c c' a b s wi wp si =
      exchangePasting (J B c.i) (R B c.g) (J B c'.i) (R B c'.g)
        (G B a) (G B s) (G B b) (beta B a c'.i c.i s wi si).hom
        (refinementExchange B s c'.g c.g b wp) := by
  rw [refinementExchange_eq]
  rfl

private theorem equation_exchange_transfer {A A' T T' : Type*}
    [Category A] [Category A'] [Category T] [Category T']
    (L : A ⥤ A') (Lt : T ⥤ T')
    {F₁ F₂ : A ⥤ T} {F₁' F₂' : A' ⥤ T'}
    (e₂ e₂' : F₂ ⋙ Lt ⟶ L ⋙ F₂') (e₁ e₁' : F₁ ⋙ Lt ⟶ L ⋙ F₁')
    (c c' : F₂ ⟶ F₁) (cp cp' : F₂' ⟶ F₁')
    (he₂ : e₂ = e₂') (he₁ : e₁ = e₁') (hc : c = c') (hcp : cp = cp')
    (h : e₂' ≫ Functor.whiskerLeft L cp' = Functor.whiskerRight c' Lt ≫ e₁') :
    e₂ ≫ Functor.whiskerLeft L cp = Functor.whiskerRight c Lt ≫ e₁ := by
  rw [he₂, he₁, hc, hcp]
  exact h

private theorem refinementR_exchange {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c₁ c₂ : Compactification f) (c₁' c₂' : Compactification f')
    (r : c₁.Refinement c₂) (r' : c₁'.Refinement c₂')
    (s₁ : c₁'.Z ⟶ c₁.Z) (s₂ : c₂'.Z ⟶ c₂.Z) (g : Y' ⟶ Y)
    (hr : r'.hom ≫ s₂ = s₁ ≫ r.hom)
    (wp₁ : s₁ ≫ c₁.g = c₁'.g ≫ g) (wp₂ : s₂ ≫ c₂.g = c₂'.g ≫ g)
    (N : Derived B c₁.Z) :
    (G B g).map ((refinementR B r).hom.app N) ≫
        (refinementExchange B s₁ c₁'.g c₁.g g wp₁).app N =
      (refinementExchange B s₂ c₂'.g c₂.g g wp₂).app ((R B r.hom).obj N) ≫
        (R B c₂'.g).map ((refinementExchange B s₁ r'.hom r.hom s₂ hr.symm).app N) ≫
        (refinementR B r').hom.app ((G B s₁).obj N) := by
  exact (refinementMatePasting B)
    c₁.Z c₂.Z Y c₁'.Z c₂'.Z Y' r.hom c₂.g c₁.g
    r'.hom c₂'.g c₁'.g s₁ s₂ g r.hom_g r'.hom_g hr.symm wp₂ wp₁ N

private theorem morphism_cube_transfer {D : Type*} [Category D]
    {X₀ X₁ X₂ X₃ X₄ X₅ : D}
    (a a₀ : X₀ ⟶ X₁) (b b₀ : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (d : X₀ ⟶ X₄) (e e₀ : X₄ ⟶ X₅) (f f₀ : X₅ ⟶ X₃)
    (ha : a = a₀) (hb : b = b₀) (he : e = e₀) (hf : f = f₀)
    (h : a₀ ≫ b₀ ≫ c = d ≫ e₀ ≫ f₀) : a ≫ b ≫ c = d ≫ e ≫ f := by
  rw [ha, hb, he, hf]
  exact h

private theorem refinementComparison_exchange {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (g' : X' ⟶ X) (g : Y' ⟶ Y)
    (sf : IsPullback g' f' f g)
    (c₁ c₂ : Compactification f) (c₁' c₂' : Compactification f')
    (s₁ : c₁'.Z ⟶ c₁.Z) (s₂ : c₂'.Z ⟶ c₂.Z)
    (si₁ : IsPullback g' c₁'.i c₁.i s₁) (sp₁ : IsPullback s₁ c₁'.g c₁.g g)
    (si₂ : IsPullback g' c₂'.i c₂.i s₂) (sp₂ : IsPullback s₂ c₂'.g c₂.g g)
    (r : c₁.Refinement c₂) (r' : c₁'.Refinement c₂')
    (hr : r'.hom ≫ s₂ = s₁ ≫ r.hom) (hf : QuasiCompact f) :
    compositionE B c₂ c₂' g' g s₂ si₂.w sp₂.w si₂ ≫
        Functor.whiskerLeft (G B g')
          (refinementComparison B r'
            (MorphismProperty.IsStableUnderBaseChange.of_isPullback sf hf)) =
      Functor.whiskerRight (refinementComparison B r hf) (G B g) ≫
        compositionE B c₁ c₁' g' g s₁ si₁.w sp₁.w si₁ := by
  let hf' : QuasiCompact f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sf hf
  have sr : IsPullback s₁ r'.hom r.hom s₂ := by
    apply IsPullback.of_bot (p := hr.symm) (t := sp₂)
    simpa only [r.hom_g, r'.hom_g] using sp₁
  let : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion hf
  let : QuasiCompact c₂.i := c₂.quasiCompact_openImmersion hf
  let : QuasiCompact c₁'.i := c₁'.quasiCompact_openImmersion hf'
  let : QuasiCompact c₂'.i := c₂'.quasiCompact_openImmersion hf'
  have hid : g' ≫ (𝟙 X) = (𝟙 X') ≫ g' := by simp
  have sid : IsPullback g' (𝟙 X') (𝟙 X) g' := IsPullback.of_vert_isIso ⟨hid⟩
  refine equation_exchange_transfer (G B g') (G B g) _ _ _ _ _ _ _ _
    (compositionE_factor B c₂ c₂' g' g s₂ si₂.w sp₂.w si₂)
    (compositionE_factor B c₁ c₁' g' g s₁ si₁.w sp₁.w si₁)
    (refinementComparison_factor B r hf) (refinementComparison_factor B r' hf') ?_
  apply refinementPasting_exchange
    (J B c₁.i) (J B c₂.i) (J B c₁'.i) (J B c₂'.i)
    (R B (𝟙 X)) (R B (𝟙 X')) (rId B X) (rId B X')
    (R B r.hom) (R B r'.hom)
    (R B c₁.g) (R B c₂.g) (R B c₁'.g) (R B c₂'.g)
    (G B g') (G B s₁) (G B s₂) (G B g)
    _ _ _ _ _ _ (refinementExchange B s₁ r'.hom r.hom s₂ hr.symm)
    (refinementExchange B g' (𝟙 X') (𝟙 X) g' hid)
  · intro M
    refine morphism_cube_transfer _ _ _ _ _ _ _ _ _ _
      (congrArg (fun δ ↦ (G B s₂).map (δ.app M))
        (refinementGamma_eq B c₁.i (𝟙 X) r.hom c₂.i _))
      (congrArg (fun δ ↦ δ.app ((J B c₁.i).obj M))
        (refinementExchange_app_eq B s₁ r'.hom r.hom s₂ hr.symm))
      (congrArg (fun δ ↦ (J B c₂'.i).map (δ.app M))
        (refinementExchange_app_eq B g' (𝟙 X') (𝟙 X) g' hid))
      (congrArg (fun δ ↦ δ.app ((G B g').obj M))
        (refinementGamma_eq B c₁'.i (𝟙 X') r'.hom c₂'.i _)) ?_
    exact (normalizedProperOpenCalculus B).2.2 c₁.i c₂.i (𝟙 X) r.hom
      c₁'.i c₂'.i (𝟙 X') r'.hom s₁ s₂ g' g'
      (r.i_hom.trans (Category.id_comp _).symm)
      (r'.i_hom.trans (Category.id_comp _).symm)
      si₁.w si₂.w hr.symm hid si₁ si₂ sr sid M
  · exact (refinementMateIdentity B) X X' g' hid
  · intro N
    exact refinementR_exchange B c₁ c₂ c₁' c₂' r r' s₁ s₂ g hr sp₁.w sp₂.w N

private theorem refinementComparison_parallel {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] {c d : Compactification f} (r s : d.Refinement c)
    (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M))) :
    (refinementComparison B r).app M = (refinementComparison B s).app M := by
  obtain ⟨e, t, ht⟩ := IsCofilteredOrEmpty.cone_maps (C := Compactification f)
    (r : d ⟶ c) (s : d ⟶ c)
  have ht' : t.comp r = t.comp s := ht
  have hh := congrArg (fun a ↦ (refinementComparison B a).app M) ht'
  rw [refinementComparison_comp, refinementComparison_comp] at hh
  let := refinementComparison_isIso B t M hM
  exact (cancel_mono ((refinementComparison B t).app M)).1 hh

private theorem refinementCommonComparison_refine {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] {c₁ c₂ d e : Compactification f}
    (r₁ : d.Refinement c₁) (r₂ : d.Refinement c₂) (t : e.Refinement d)
    (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M))) :
    refinementCommonComparison B (t.comp r₁) (t.comp r₂) M hM =
      refinementCommonComparison B r₁ r₂ M hM := by
  let := refinementComparison_isIso B r₁ M hM
  let := refinementComparison_isIso B r₂ M hM
  let := refinementComparison_isIso B t M hM
  apply Iso.ext
  simp [refinementCommonComparison, refinementComparison_comp, IsIso.inv_comp,
    Category.assoc]

private theorem refinementCommonComparison_independent {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] {c₁ c₂ d e : Compactification f}
    (r₁ : d.Refinement c₁) (r₂ : d.Refinement c₂)
    (s₁ : e.Refinement c₁) (s₂ : e.Refinement c₂) (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M))) :
    refinementCommonComparison B r₁ r₂ M hM =
      refinementCommonComparison B s₁ s₂ M hM := by
  obtain ⟨a, t, v, -⟩ := IsCofilteredOrEmpty.cone_objs d e
  rw [← refinementCommonComparison_refine B r₁ r₂ t M hM,
    ← refinementCommonComparison_refine B s₁ s₂ v M hM]
  apply Iso.ext
  simp only [refinementCommonComparison, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    asIso_inv]
  simp only [refinementComparison_parallel B (t.comp r₁) (v.comp s₁) M hM,
    refinementComparison_parallel B (t.comp r₂) (v.comp s₂) M hM]

private theorem refinementCommonComparison_cocycle {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] {c₁ c₂ c₃ d₁₂ d₂₃ d₁₃ : Compactification f}
    (u₁ : d₁₂.Refinement c₁) (u₂ : d₁₂.Refinement c₂)
    (v₂ : d₂₃.Refinement c₂) (v₃ : d₂₃.Refinement c₃)
    (w₁ : d₁₃.Refinement c₁) (w₃ : d₁₃.Refinement c₃)
    (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M))) :
    refinementCommonComparison B u₁ u₂ M hM ≪≫
        refinementCommonComparison B v₂ v₃ M hM =
      refinementCommonComparison B w₁ w₃ M hM := by
  obtain ⟨d, t, v, -⟩ := IsCofilteredOrEmpty.cone_objs d₁₂ d₂₃
  rw [← refinementCommonComparison_refine B u₁ u₂ t M hM,
    refinementCommonComparison_independent B v₂ v₃ (t.comp u₂) (v.comp v₃) M hM,
    refinementCommonComparison_independent B w₁ w₃ (t.comp u₁) (v.comp v₃) M hM]
  let := refinementComparison_isIso B (t.comp u₂) M hM
  apply Iso.ext
  simp [refinementCommonComparison]

private theorem refinementCommonComparison_hom {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ d : Compactification f} (u₁ : d.Refinement c₁) (u₂ : d.Refinement c₂)
    (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M)))
    (hf : QuasiCompact f)
    [IsIso ((refinementComparison B u₂ hf).app M)] :
    (refinementCommonComparison B u₁ u₂ M hM hf).hom =
      (refinementComparison B u₁ hf).app M ≫ inv ((refinementComparison B u₂ hf).app M) := by
  rfl

private theorem refinementCommonComparison_relation {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ d : Compactification f} (u₁ : d.Refinement c₁) (u₂ : d.Refinement c₂)
    (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M)))
    (hf : QuasiCompact f) :
    (refinementCommonComparison B u₁ u₂ M hM hf).hom ≫
      (refinementComparison B u₂ hf).app M = (refinementComparison B u₁ hf).app M := by
  let := refinementComparison_isIso B u₂ M hM hf
  rw [refinementCommonComparison_hom B u₁ u₂ M hM hf]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

private theorem ratio_relation_exchange {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A₁ A₂ A : C} {A₁' A₂' A' : D}
    (r₁ : A₁ ⟶ A) (r₂ : A₂ ⟶ A) (r₁' : A₁' ⟶ A') (r₂' : A₂' ⟶ A')
    [IsIso r₂'] (q : A₁ ⟶ A₂) (q' : A₁' ⟶ A₂')
    (hq : q ≫ r₂ = r₁) (hq' : q' ≫ r₂' = r₁')
    (e₁ : F.obj A₁ ⟶ A₁') (e₂ : F.obj A₂ ⟶ A₂') (e : F.obj A ⟶ A')
    (h₁ : e₁ ≫ r₁' = F.map r₁ ≫ e) (h₂ : e₂ ≫ r₂' = F.map r₂ ≫ e) :
    F.map q ≫ e₂ = e₁ ≫ q' := by
  apply (cancel_mono r₂').1
  calc
    (F.map q ≫ e₂) ≫ r₂' = F.map (q ≫ r₂) ≫ e := by
      simp only [Functor.map_comp, Category.assoc]
      rw [h₂]
    _ = F.map r₁ ≫ e := by rw [hq]
    _ = e₁ ≫ r₁' := h₁.symm
    _ = (e₁ ≫ q') ≫ r₂' := by rw [Category.assoc, hq']

private theorem ratio_exchange_nat {A A' T T' : Type*}
    [Category A] [Category A'] [Category T] [Category T']
    (L : A ⥤ A') (Lt : T ⥤ T')
    (F₁ F₂ D : A ⥤ T) (F₁' F₂' D' : A' ⥤ T')
    (r₁ : F₁ ⟶ D) (r₂ : F₂ ⟶ D) (r₁' : F₁' ⟶ D') (r₂' : F₂' ⟶ D')
    (e₁ : F₁ ⋙ Lt ⟶ L ⋙ F₁') (e₂ : F₂ ⋙ Lt ⟶ L ⋙ F₂') (e : D ⋙ Lt ⟶ L ⋙ D')
    (h₁ : e₁ ≫ Functor.whiskerLeft L r₁' = Functor.whiskerRight r₁ Lt ≫ e)
    (h₂ : e₂ ≫ Functor.whiskerLeft L r₂' = Functor.whiskerRight r₂ Lt ≫ e)
    (M : A) [IsIso (r₂'.app (L.obj M))]
    (q : F₁.obj M ⟶ F₂.obj M) (q' : F₁'.obj (L.obj M) ⟶ F₂'.obj (L.obj M))
    (hq : q ≫ r₂.app M = r₁.app M) (hq' : q' ≫ r₂'.app (L.obj M) = r₁'.app (L.obj M)) :
    Lt.map q ≫ e₂.app M = e₁.app M ≫ q' := by
  apply ratio_relation_exchange Lt (r₁.app M) (r₂.app M)
    (r₁'.app (L.obj M)) (r₂'.app (L.obj M)) q q' hq hq'
    (e₁.app M) (e₂.app M) (e.app M)
  · simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] using congrArg (fun t ↦ t.app M) h₁
  · simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] using congrArg (fun t ↦ t.app M) h₂

private theorem refinementCommonComparison_qc_irrel {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ d : Compactification f} (u₁ : d.Refinement c₁) (u₂ : d.Refinement c₂)
    (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M)))
    (hf hg : QuasiCompact f) :
    refinementCommonComparison B u₁ u₂ M hM hf =
      refinementCommonComparison B u₁ u₂ M hM hg := by
  exact congrArg (fun h ↦ refinementCommonComparison B u₁ u₂ M hM h)
    (Subsingleton.elim hf hg)

private theorem refinementCommonComparison_exchange {X Y : Scheme.{u}} {f : X ⟶ Y}
    [hf : QuasiCompact f] (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M)))
    {X' Y' : Scheme.{u}} {f' : X' ⟶ Y'}
      (g' : X' ⟶ X) (g : Y' ⟶ Y) (sf : IsPullback g' f' f g)
      (c₁ c₂ d : Compactification f) (c₁' c₂' d' : Compactification f')
      (s₁ : c₁'.Z ⟶ c₁.Z) (s₂ : c₂'.Z ⟶ c₂.Z) (sd : d'.Z ⟶ d.Z)
      (si₁ : IsPullback g' c₁'.i c₁.i s₁) (sp₁ : IsPullback s₁ c₁'.g c₁.g g)
      (si₂ : IsPullback g' c₂'.i c₂.i s₂) (sp₂ : IsPullback s₂ c₂'.g c₂.g g)
      (sid : IsPullback g' d'.i d.i sd) (spd : IsPullback sd d'.g d.g g)
      (u₁ : d.Refinement c₁) (u₂ : d.Refinement c₂)
      (u₁' : d'.Refinement c₁') (u₂' : d'.Refinement c₂')
      (hu₁ : u₁'.hom ≫ s₁ = sd ≫ u₁.hom)
      (hu₂ : u₂'.hom ≫ s₂ = sd ≫ u₂.hom) :
      (G B g).map (refinementCommonComparison B u₁ u₂ M hM hf).hom ≫
          (compositionE B c₂ c₂' g' g s₂ si₂.w sp₂.w si₂).app M =
        (compositionE B c₁ c₁' g' g s₁ si₁.w sp₁.w si₁).app M ≫
          (refinementCommonComparison B u₁' u₂' ((G B g').obj M)
            (refinementFiniteOrigin_pullback B g' M hM)
            (MorphismProperty.IsStableUnderBaseChange.of_isPullback sf hf)).hom := by
  let : IsIso ((refinementComparison B u₂'
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback sf hf)).app ((G B g').obj M)) :=
    refinementComparison_isIso B u₂' ((G B g').obj M)
      (refinementFiniteOrigin_pullback B g' M hM)
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback sf hf)
  exact ratio_exchange_nat (G B g') (G B g)
    (compositionF B c₁) (compositionF B c₂) (compositionF B d)
    (compositionF B c₁') (compositionF B c₂') (compositionF B d')
    (refinementComparison B u₁ hf) (refinementComparison B u₂ hf)
    (refinementComparison B u₁'
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback sf hf))
    (refinementComparison B u₂'
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback sf hf))
    (compositionE B c₁ c₁' g' g s₁ si₁.w sp₁.w si₁)
    (compositionE B c₂ c₂' g' g s₂ si₂.w sp₂.w si₂)
    (compositionE B d d' g' g sd sid.w spd.w sid)
    (refinementComparison_exchange B g' g sf d c₁ d' c₁'
      sd s₁ sid spd si₁ sp₁ u₁ u₁' hu₁ hf)
    (refinementComparison_exchange B g' g sf d c₂ d' c₂'
      sd s₂ sid spd si₂ sp₂ u₂ u₂' hu₂ hf) M
    (refinementCommonComparison B u₁ u₂ M hM hf).hom
    (refinementCommonComparison B u₁' u₂' ((G B g').obj M)
      (refinementFiniteOrigin_pullback B g' M hM)
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback sf hf)).hom
    (refinementCommonComparison_relation B u₁ u₂ M hM hf)
    (refinementCommonComparison_relation B u₁' u₂' ((G B g').obj M)
      (refinementFiniteOrigin_pullback B g' M hM)
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback sf hf))

-- Preserve the published names of proof binders in the quantified statement.
set_option linter.unusedVariables false in
/-- All refinement and common-refinement coherences, in the derived strict-tower categories.
The first three equations and the refinement/base-change square are equalities of
natural transformations on the whole derived categories. Invertibility and the
common-refinement isomorphisms are on the stated finite scalar etale-origin domain.
Source: Stacks, Tags 0F7B, 0F7C and 0F7F; blueprint, thm-cbc-complete-proetale,
final independence and naturality argument
(blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence).

Proof, following the six node steps:
1. The refinement equations identify its identity-left proper/open square. Whiskering
   its normalized gamma by R of c₂.g, with canonical compositors, is compositionC.
2. gamma_isIso on the finite scalar etale origins makes this map invertible, as in
   refinementComparison_isIso. The origins are preserved by arbitrary pullback, as in
   refinementFiniteOrigin_pullback: exact etale inverse image retains each lower bound.
3. Pull back the refinement square. The calculus cube gives the equality for gamma
   and beta. Whisker by the outer proper direct image. Naturality moves gamma past
   the outer proper mate, and mate pasting identifies the composite proper mates
   with the mate for c₁.g. These are exactly the two displayed exchange paths.
   This is an equality of transformations, not a deduction from evaluation.
4. Identity normalization gives C_id = 1. Vertical pasting gives the refinement
   composition equation, including the canonical R compositors.
5. Equalize any pair of parallel refinement arrows. The composition equation and
   cancellation of the further invertible comparison identify their comparisons.
   For two common-refinement diagrams choose a common domination; the two resulting
   arrows to each cᵢ are parallel, so these equalities identify both legs and hence
   refinementCommonComparison, including different arrows from the same refinement.
6. Dominate three compactifications at once. Independence permits computing all
   comparisons there; cancellation gives the cocycle. After base change the common
   refinement and its arrows pull back, and step 2 supplies invertible primed maps.
   Apply step 3 to both legs and cancel C_{u₂}' to get the final intertwining equation.
   There is no qcqs or Noetherian assumption on Y, no properness assumption on g,
   and no common bound or coefficient ring for the different levels.
-/
theorem refinementExchangeCoherence {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M))) :
    (∀ {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂),
      IsIso ((refinementComparison B r).app M)) ∧
    (∀ c : Compactification f,
      refinementComparison B (Compactification.Refinement.id c) = 𝟙 _) ∧
    (∀ {c₁ c₂ c₃ : Compactification f}
      (r : c₁.Refinement c₂) (s : c₂.Refinement c₃),
      refinementComparison B (r.comp s) =
        refinementComparison B s ≫ refinementComparison B r) ∧
    (∀ {X' Y' : Scheme.{u}} {f' : X' ⟶ Y'}
      (g' : X' ⟶ X) (g : Y' ⟶ Y) (sf : IsPullback g' f' f g)
      (c₁ c₂ : Compactification f) (c₁' c₂' : Compactification f')
      (s₁ : c₁'.Z ⟶ c₁.Z) (s₂ : c₂'.Z ⟶ c₂.Z)
      (si₁ : IsPullback g' c₁'.i c₁.i s₁) (sp₁ : IsPullback s₁ c₁'.g c₁.g g)
      (si₂ : IsPullback g' c₂'.i c₂.i s₂) (sp₂ : IsPullback s₂ c₂'.g c₂.g g)
      (r : c₁.Refinement c₂) (r' : c₁'.Refinement c₂')
      (hr : r'.hom ≫ s₂ = s₁ ≫ r.hom),
      compositionE B c₂ c₂' g' g s₂ si₂.w sp₂.w si₂ ≫
          Functor.whiskerLeft (G B g')
            (refinementComparison B r'
              (MorphismProperty.IsStableUnderBaseChange.of_isPullback sf inferInstance)) =
        Functor.whiskerRight (refinementComparison B r) (G B g) ≫
          compositionE B c₁ c₁' g' g s₁ si₁.w sp₁.w si₁) ∧
    (∀ {c₁ c₂ d e : Compactification f}
      (u₁ : d.Refinement c₁) (u₂ : d.Refinement c₂)
      (v₁ : e.Refinement c₁) (v₂ : e.Refinement c₂),
      refinementCommonComparison B u₁ u₂ M hM =
        refinementCommonComparison B v₁ v₂ M hM) ∧
    (∀ {c₁ c₂ c₃ d₁₂ d₂₃ d₁₃ : Compactification f}
      (u₁ : d₁₂.Refinement c₁) (u₂ : d₁₂.Refinement c₂)
      (v₂ : d₂₃.Refinement c₂) (v₃ : d₂₃.Refinement c₃)
      (w₁ : d₁₃.Refinement c₁) (w₃ : d₁₃.Refinement c₃),
      refinementCommonComparison B u₁ u₂ M hM ≪≫
          refinementCommonComparison B v₂ v₃ M hM =
        refinementCommonComparison B w₁ w₃ M hM) ∧
    (∀ {X' Y' : Scheme.{u}} {f' : X' ⟶ Y'}
      (g' : X' ⟶ X) (g : Y' ⟶ Y) (sf : IsPullback g' f' f g)
      (c₁ c₂ d : Compactification f) (c₁' c₂' d' : Compactification f')
      (s₁ : c₁'.Z ⟶ c₁.Z) (s₂ : c₂'.Z ⟶ c₂.Z) (sd : d'.Z ⟶ d.Z)
      (si₁ : IsPullback g' c₁'.i c₁.i s₁) (sp₁ : IsPullback s₁ c₁'.g c₁.g g)
      (si₂ : IsPullback g' c₂'.i c₂.i s₂) (sp₂ : IsPullback s₂ c₂'.g c₂.g g)
      (sid : IsPullback g' d'.i d.i sd) (spd : IsPullback sd d'.g d.g g)
      (u₁ : d.Refinement c₁) (u₂ : d.Refinement c₂)
      (u₁' : d'.Refinement c₁') (u₂' : d'.Refinement c₂')
      (hu₁ : u₁'.hom ≫ s₁ = sd ≫ u₁.hom)
      (hu₂ : u₂'.hom ≫ s₂ = sd ≫ u₂.hom),
      (G B g).map (refinementCommonComparison B u₁ u₂ M hM).hom ≫
          (compositionE B c₂ c₂' g' g s₂ si₂.w sp₂.w si₂).app M =
        (compositionE B c₁ c₁' g' g s₁ si₁.w sp₁.w si₁).app M ≫
          (refinementCommonComparison B u₁' u₂' ((G B g').obj M)
            (refinementFiniteOrigin_pullback B g' M hM)
            (MorphismProperty.IsStableUnderBaseChange.of_isPullback sf inferInstance)).hom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c₁ c₂ r
    refine @refinementComparison_isIso.{u} B _ X Y f c₁ c₂ r M hM ?_
  · intro c
    exact refinementComparison_id B c inferInstance
  · intro c₁ c₂ c₃ r s
    exact refinementComparison_comp B s r inferInstance
  · intro X' Y' f' g' g sf c₁ c₂ c₁' c₂' s₁ s₂ si₁ sp₁ si₂ sp₂ r r' hr
    exact refinementComparison_exchange B g' g sf c₁ c₂ c₁' c₂'
      s₁ s₂ si₁ sp₁ si₂ sp₂ r r' hr inferInstance
  · intro c₁ c₂ d e u₁ u₂ v₁ v₂
    exact refinementCommonComparison_independent B u₁ u₂ v₁ v₂ M hM
  · intro c₁ c₂ c₃ d₁₂ d₂₃ d₁₃ u₁ u₂ v₂ v₃ w₁ w₃
    exact refinementCommonComparison_cocycle B u₁ u₂ v₂ v₃ w₁ w₃ M hM
  · intro X' Y' f' g' g sf c₁ c₂ d c₁' c₂' d' s₁ s₂ sd
      si₁ sp₁ si₂ sp₂ sid spd u₁ u₂ u₁' u₂' hu₁ hu₂
    have hf : QuasiCompact f := inferInstance
    have hf' : QuasiCompact f' :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback sf hf
    rw [refinementCommonComparison_qc_irrel B u₁ u₂ M hM _ hf]
    rw [refinementCommonComparison_qc_irrel B u₁' u₂' ((G B g').obj M)
      (refinementFiniteOrigin_pullback B g' M hM) _ hf']
    exact refinementCommonComparison_exchange B M hM g' g sf c₁ c₂ d c₁' c₂' d'
      s₁ s₂ sd si₁ sp₁ si₂ sp₂ sid spd u₁ u₂ u₁' u₂' hu₁ hu₂

end AlgebraicGeometry.ProEtale.StrictTower
