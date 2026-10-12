/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackSourceComparison
public import Sheaf.AlgebraicGeometry.TensorPullback

/-! # EtaleGeneratorsPullbackTargetComparison

Source: Stacks Project, Tags 0097 and 040E.
(blueprint: lem-sc-etale-generators-pullback-target-comparison)
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

private theorem compOfEq_assoc {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (ab : A ⟶ C) (bc : B ⟶ D) (t : A ⟶ D)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (ht : ab ≫ c = t) (ht' : a ≫ bc = t) (M : D.Modules) :
    (pullbackCompOfEq a b ab hab ((pullback c).obj M)).hom ≫
      (pullbackCompOfEq ab c t ht M).hom =
    (pullback a).map (pullbackCompOfEq b c bc hbc M).hom ≫
      (pullbackCompOfEq a bc t ht' M).hom := by
  subst ab bc t
  have h := congrArg (fun n ↦ n.app M) (pseudofunctor_associativity a b c)
  dsimp at h
  simp only [Category.id_comp] at h
  have h' := congrArg (fun k ↦
    (pullback a).map ((pullbackComp b c).hom.app M) ≫
      (pullbackComp a (b ≫ c)).hom.app M ≫ k) h
  simpa [pullbackCompOfEq, pullbackCongr, Category.assoc,
    ← Functor.map_comp] using h'

private theorem compOfEq_naturality {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (h : a ≫ b = c)
    {M N : C.Modules} (φ : M ⟶ N) :
    (pullback a).map ((pullback b).map φ) ≫ (pullbackCompOfEq a b c h N).hom =
      (pullbackCompOfEq a b c h M).hom ≫ (pullback c).map φ := by
  subst c
  simpa [pullbackCompOfEq, pullbackCongr] using (pullbackComp a b).hom.naturality φ

private theorem square_comp {A B C D E F : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (d : A ⟶ D) (e : D ⟶ C)
    (c : C ⟶ E) (v : D ⟶ E) (q : B ⟶ F) (r : A ⟶ F) (f : F ⟶ E)
    (hp : a ≫ b = d ≫ e) (hi : e ≫ c = v)
    (hw : b ≫ c = q ≫ f) (hv : d ≫ v = r ≫ f) (hq : a ≫ q = r)
    (M : E.Modules) :
    ((pullbackComp d e).app ((pullback c).obj M)).hom ≫
      (pullbackCompOfEq a b (d ≫ e) hp ((pullback c).obj M)).inv ≫
      (pullback a).map ((pullbackCompOfEq b c (q ≫ f) hw M).hom ≫
        ((pullbackComp q f).app M).inv) ≫
      (pullbackCompOfEq a q r hq ((pullback f).obj M)).hom =
    (pullback d).map (pullbackCompOfEq e c v hi M).hom ≫
      (pullbackCompOfEq d v (r ≫ f) hv M).hom ≫ ((pullbackComp r f).app M).inv := by
  have ht : (d ≫ e) ≫ c = r ≫ f := by rw [Category.assoc, hi, hv]
  have ht' : a ≫ q ≫ f = r ≫ f := by rw [← Category.assoc, hq]
  have h₁ : (pullbackCompOfEq a q r hq ((pullback f).obj M)).hom ≫
      ((pullbackComp r f).app M).hom =
      (pullback a).map ((pullbackComp q f).app M).hom ≫
        (pullbackCompOfEq a (q ≫ f) (r ≫ f) ht' M).hom := by
    simpa [pullbackCompOfEq, pullbackCongr] using
      compOfEq_assoc a q f r (q ≫ f) (r ≫ f) hq rfl rfl ht' M
  have h₂ := compOfEq_assoc a b c (d ≫ e) (q ≫ f) (r ≫ f) hp hw ht ht' M
  have h₃ : ((pullbackComp d e).app ((pullback c).obj M)).hom ≫
      (pullbackCompOfEq (d ≫ e) c (r ≫ f) ht M).hom =
      (pullback d).map (pullbackCompOfEq e c v hi M).hom ≫
        (pullbackCompOfEq d v (r ≫ f) hv M).hom := by
    simpa [pullbackCompOfEq, pullbackCongr] using
      compOfEq_assoc d e c (d ≫ e) v (r ≫ f) rfl hi ht hv M
  rw [← cancel_mono ((pullbackComp r f).hom.app M)]
  dsimp only [Iso.app] at h₁ h₃ ⊢
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [h₁]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← h₂]
  simp only [Iso.inv_hom_id_assoc]
  exact h₃

private theorem square_comp_map {A B C D E F : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (d : A ⟶ D) (e : D ⟶ C)
    (c : C ⟶ E) (v : D ⟶ E) (q : B ⟶ F) (r : A ⟶ F) (f : F ⟶ E)
    (hp : a ≫ b = d ≫ e) (hi : e ≫ c = v)
    (hw : b ≫ c = q ≫ f) (hv : d ≫ v = r ≫ f) (hq : a ≫ q = r)
    (M : E.Modules) {N : F.Modules} (φ : (pullback f).obj M ⟶ N) :
    ((pullbackComp d e).app ((pullback c).obj M)).hom ≫
      (pullbackCompOfEq a b (d ≫ e) hp ((pullback c).obj M)).inv ≫
      (pullback a).map ((pullbackCompOfEq b c (q ≫ f) hw M).hom ≫
        ((pullbackComp q f).app M).inv ≫ (pullback q).map φ) ≫
      (pullbackCompOfEq a q r hq N).hom =
    (pullback d).map (pullbackCompOfEq e c v hi M).hom ≫
      (pullbackCompOfEq d v (r ≫ f) hv M).hom ≫
      ((pullbackComp r f).app M).inv ≫ (pullback r).map φ := by
  simp only [Functor.map_comp, Category.assoc]
  rw [compOfEq_naturality a q r hq φ]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ k ≫ (pullback r).map φ)
      (square_comp a b d e c v q r f hp hi hw hv hq M)

/-- An explicit comparison factor in the generator pullback construction.
Source: Stacks Project, Tag 0097. (blueprint: lem-sc-etale-generators-pullback-target-comparison) -/
noncomputable def etaleGeneratorsPullbackTargetIso {X Y : Scheme.{u}} (f : Y ⟶ X) (W : X.Etale)
    (L : X.Modules) :
    (pullback (Limits.pullback.fst W.hom f)).obj ((pullback W.hom).obj L) ≅
      (pullback (Limits.pullback.snd W.hom f)).obj ((tensorPullback f).obj L) :=
  (pullbackComp (Limits.pullback.fst W.hom f) W.hom).app L ≪≫
    (pullbackCongr Limits.pullback.condition).app L ≪≫
    ((pullbackComp (Limits.pullback.snd W.hom f) f).app L).symm ≪≫
    (pullback (Limits.pullback.snd W.hom f)).mapIso
      (((Classical.choice (nonempty_tensorPullbackAdjunction f)).leftAdjointUniq
        (pullbackPushforwardAdjunction f)).app L).symm

/-- The target comparison commutes with etale restriction.
Source: Stacks Project, Tag 0097, Lemma 6.26.3; Tag 040E, Lemma 21.6.1.
(blueprint: lem-sc-etale-generators-pullback-target-comparison)

Proof: Write B_U(M) as the comparison p_U*U*M to q_U*f*M, followed by q_U* of the inverse
tensor/abstract pullback comparison. Naturality of c(j,q_W;q_V) with respect to this last
inverse moves that factor to q_V*. The remaining comparison identity is the associativity
coherence of the module pullback pseudofunctor: both composites identify j*p_W*W*M with q_V*f*M
through the same morphism to X. Use j followed by p_W equals p_V followed by i, i followed by W
equals V, and j followed by q_W equals q_V. Apply the three-fold composition coherence on each
path and cancel the common comparison for the total morphism. This gives K(M).inv followed by
j*B_W(M) and the q comparison equal to p_V* of c(i,W;V).hom followed by B_V(M). The argument is
natural for every module M, including the zero module, and does not use any section or
invertibility.
-/
theorem etaleGeneratorsPullbackTarget_naturality {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    {V W : X.Etale} (i : V ⟶ W) :
    (etaleGeneratorsPullbackSquareIso f i ((pullback W.hom).obj L)).inv ≫
      (pullback ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left).map
        (etaleGeneratorsPullbackTargetIso f W L).hom ≫ (pullbackCompOfEq
        ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left
      (Limits.pullback.snd W.hom f) (Limits.pullback.snd V.hom f)
      ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).w ((tensorPullback f).obj L)).hom =
      (pullback (Limits.pullback.fst V.hom f)).map (pullbackCompOfEq i.left W.hom V.hom i.w
        (L)).hom ≫
        (etaleGeneratorsPullbackTargetIso f V L).hom := by
  have hp : ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left ≫
      Limits.pullback.fst W.hom f = Limits.pullback.fst V.hom f ≫ i.left := by
    simp [MorphismProperty.Over.pullback_map_left]
  have h := square_comp_map ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left
    (Limits.pullback.fst W.hom f) (Limits.pullback.fst V.hom f) i.left W.hom V.hom
    (Limits.pullback.snd W.hom f) (Limits.pullback.snd V.hom f) f
    (N := (tensorPullback f).obj L)
    hp i.w Limits.pullback.condition Limits.pullback.condition
    ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).w L
    (((Classical.choice (nonempty_tensorPullbackAdjunction f)).leftAdjointUniq
      (pullbackPushforwardAdjunction f)).inv.app L)
  simp only [etaleGeneratorsPullbackSquareIso, etaleGeneratorsPullbackTargetIso,
    pullbackCompOfEq, Iso.app_hom, Iso.app_inv, NatIso.trans_app, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Category.assoc] at h ⊢
  exact h

end AlgebraicGeometry.Scheme.Modules
