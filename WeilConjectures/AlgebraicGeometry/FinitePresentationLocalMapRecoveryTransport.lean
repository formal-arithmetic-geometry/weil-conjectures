/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.AlgebraicGeometry.LocalMapPullbackFamily
public import WeilConjectures.AlgebraicGeometry.LocalMapRecovery
import WeilConjectures.AlgebraicGeometry.LocalMapRecoveryComposition
import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionAssociativity

/-! # Transport of local recovery equations

## References

* Stacks Project, Tags 01ZR, 0095 and 0096
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.pullback Scheme.Modules.tensorPullback
  Scheme.Modules.openCoverTensorPullbackComparison

private theorem comparison_conjugate
    {C D E : Type*} [Category C] [Category D] [Category E]
    (R : C ⥤ D) (S : D ⥤ E) (T : C ⥤ E) (t : R ⋙ S ≅ T)
    {F G F' G' : C} (κ : F' ⟶ F) (ρ : G ⟶ G')
    (r : R.obj F ⟶ R.obj G) :
    t.inv.app F' ≫ S.map (R.map κ ≫ r ≫ R.map ρ) ≫ t.hom.app G' =
      T.map κ ≫ (t.inv.app F ≫ S.map r ≫ t.hom.app G) ≫ T.map ρ := by
  simp only [Functor.map_comp, Category.assoc]
  have hk := t.inv.naturality κ
  have hρ := t.hom.naturality ρ
  dsimp only [Functor.comp_map] at hk hρ
  rw [← reassoc_of% hk]
  rw [hρ]

private theorem recovery_conjugate
    {X Y : Scheme.{u}} (p : Y ⟶ X) (U : X.OpenCover.{u})
    {F G F' G' : X.Modules} (κ : F' ⟶ F) (ρ : G ⟶ G')
    (δ : (Scheme.Modules.tensorPullback p).obj F ⟶
      (Scheme.Modules.tensorPullback p).obj G)
    (r : ∀ α, (Scheme.Modules.pullback (U.f α)).obj F ⟶
      (Scheme.Modules.pullback (U.f α)).obj G)
    (hr : localMapRecovery p U F G δ r) :
    localMapRecovery p U F' G'
      ((Scheme.Modules.tensorPullback p).map κ ≫ δ ≫
        (Scheme.Modules.tensorPullback p).map ρ)
      (fun α ↦ (Scheme.Modules.pullback (U.f α)).map κ ≫ r α ≫
        (Scheme.Modules.pullback (U.f α)).map ρ) := by
  intro α
  dsimp only at *
  rw [comparison_conjugate]
  rw [hr α]
  simp only [Functor.comp_map, Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
/-- Recovery of a global map survives a further factorization of the limit map.
The three supplied comparisons are required to be the canonical ones.
(Stacks, Tag 01ZR, Tag 0095, Tag 0096) -/
theorem finitePresentation_local_maps_recovery_transport
    {X₀ X₁ X₂ Z : Scheme.{u}}
    (h : X₁ ⟶ X₀) (q : X₂ ⟶ X₁) (p : Z ⟶ X₂)
    (b : Z ⟶ X₁) (a : Z ⟶ X₀) (d : X₂ ⟶ X₀)
    (wpq : p ≫ q = b) (wqh : q ≫ h = d)
    (wbh : b ≫ h = a) (wpd : p ≫ d = a)
    (A₀ : X₀.Modules ⥤ X₁.Modules) (hA₀ : A₀ = Scheme.Modules.tensorPullback h)
    (A : X₀.Modules ⥤ X₂.Modules) (hA : A = Scheme.Modules.tensorPullback d)
    (B : X₀.Modules ⥤ Z.Modules) (hB : B = Scheme.Modules.tensorPullback a)
    (F G : X₀.Modules)
    (φ : B.obj F ⟶ B.obj G)
    (e₀ : B ≅ A₀ ⋙ Scheme.Modules.tensorPullback b)
    (he₀ : HEq e₀ (Scheme.Modules.tensorPullbackCompositionIso b h a wbh))
    (e : B ≅
      A ⋙ Scheme.Modules.tensorPullback p)
    (he : HEq e (Scheme.Modules.tensorPullbackCompositionIso p d a wpd))
    (z : A ≅ A₀ ⋙ Scheme.Modules.tensorPullback q)
    (hz : HEq z (Scheme.Modules.tensorPullbackCompositionIso q h d wqh))
    (U₀ : X₁.OpenCover.{u}) :
    let Q₀ := modulesPseudofunctor.toDescentData U₀.f
    ∀ (r₀ : ∀ α, (Q₀.obj (A₀.obj F)).obj α ⟶
      (Q₀.obj (A₀.obj G)).obj α),
    localMapRecovery b U₀ (A₀.obj F) (A₀.obj G)
      (e₀.inv.app F ≫ φ ≫ e₀.hom.app G) r₀ →
    let U : X₂.OpenCover.{u} := U₀.pullback₁ q
    let V : Z.OpenCover.{u} := U.pullback₁ p
    let Q := modulesPseudofunctor.toDescentData U.f
    let r : ∀ α, (Q.obj (A.obj F)).obj α ⟶ (Q.obj (A.obj G)).obj α :=
      localMapPullbackFamily q U₀ (A₀.obj F) (A₀.obj G) (A.obj F) (A.obj G)
        (z.hom.app F) (z.inv.app G) r₀
    localMapRecovery p U (A.obj F) (A.obj G)
      (e.inv.app F ≫ φ ≫ e.hom.app G) r := by
  dsimp
  subst A₀
  subst A
  subst B
  have he₀' := eq_of_heq he₀
  have he' := eq_of_heq he
  have hz' := eq_of_heq hz
  subst e₀
  subst e
  subst z
  intro r₀ hr₀
  let e₀ := Scheme.Modules.tensorPullbackCompositionIso b h a wbh
  let e := Scheme.Modules.tensorPullbackCompositionIso p d a wpd
  let z := Scheme.Modules.tensorPullbackCompositionIso q h d wqh
  let c := Scheme.Modules.tensorPullbackCompositionIso p q b wpq
  have hr := localMapRecovery_composition q p b wpq U₀
    ((Scheme.Modules.tensorPullback h).obj F)
    ((Scheme.Modules.tensorPullback h).obj G)
    (e₀.inv.app F ≫ φ ≫ e₀.hom.app G) r₀ hr₀
  have hr' := recovery_conjugate p (U₀.pullback₁ q)
    (z.hom.app F) (z.inv.app G) _ _ hr
  have hc (M : X₀.Modules) :
      e.hom.app M ≫ (Scheme.Modules.tensorPullback p).map (z.hom.app M) =
        e₀.hom.app M ≫ c.hom.app ((Scheme.Modules.tensorPullback h).obj M) :=
    Scheme.Modules.tensorPullbackCompositionIso_associativity h q p b a d
      wpq wqh wbh wpd M
  have hl : (Scheme.Modules.tensorPullback p).map (z.hom.app F) ≫
      c.inv.app ((Scheme.Modules.tensorPullback h).obj F) ≫ e₀.inv.app F =
        e.inv.app F := by
    rw [← cancel_epi (e.hom.app F)]
    simp only [← Category.assoc, hc F]
    simp
  have hh : e₀.hom.app G ≫ c.hom.app ((Scheme.Modules.tensorPullback h).obj G) ≫
      (Scheme.Modules.tensorPullback p).map (z.inv.app G) = e.hom.app G := by
    rw [← Category.assoc, ← hc G, Category.assoc, ← Functor.map_comp]
    simp
  have hδ : (Scheme.Modules.tensorPullback p).map (z.hom.app F) ≫
      (c.inv.app ((Scheme.Modules.tensorPullback h).obj F) ≫
        (e₀.inv.app F ≫ φ ≫ e₀.hom.app G) ≫
        c.hom.app ((Scheme.Modules.tensorPullback h).obj G)) ≫
      (Scheme.Modules.tensorPullback p).map (z.inv.app G) =
        e.inv.app F ≫ φ ≫ e.hom.app G := by
    simp only [Category.assoc] at hl hh ⊢
    rw [reassoc_of% hl, hh]
  rw [hδ] at hr'
  intro α
  change U₀.I₀ at α
  have hrα := hr' α
  dsimp only [e, z] at hrα
  unfold localMapPullbackFamily at hrα ⊢
  dsimp only at hrα ⊢
  have hid (M : X₀.Modules) :
      (Scheme.Modules.pullback ((U₀.pullback₁ q).f α)).map
        (𝟙 ((Scheme.Modules.tensorPullback q).obj ((Scheme.Modules.tensorPullback h).obj M))) =
      𝟙 _ := (Scheme.Modules.pullback ((U₀.pullback₁ q).f α)).map_id _
  rw [hid F, hid G] at hrα
  erw [Category.id_comp, Category.comp_id] at hrα
  exact hrα

end AlgebraicGeometry
