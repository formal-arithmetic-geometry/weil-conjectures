/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerPairOpenRestriction

/-! # Counit-preserving isomorphism on a binary overlap

Source: latest smooth-purity blueprint, Local pairs, Gluing and Uniformity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

private theorem representing_pair_counit_unique
    {A B : Type*} [Category A] [Category B]
    (P : ObjectProperty A) (F : A ⥤ B) (K : B)
    (H J : P.FullSubcategory) (epsH : F.obj H.obj ⟶ K) (epsJ : F.obj J.obj ⟶ K)
    (repH : ∀ M : P.FullSubcategory,
      Function.Bijective (fun a : M.obj ⟶ H.obj ↦ F.map a ≫ epsH))
    (repJ : ∀ M : P.FullSubcategory,
      Function.Bijective (fun a : M.obj ⟶ J.obj ↦ F.map a ≫ epsJ)) :
    ∃! e : H.obj ≅ J.obj, F.map e.hom ≫ epsJ = epsH := by
  obtain ⟨a, ha⟩ := (repJ H).2 epsH
  obtain ⟨b, hb⟩ := (repH J).2 epsJ
  dsimp only at ha hb
  have hab : a ≫ b = 𝟙 H.obj := by
    apply (repH H).1
    change F.map (a ≫ b) ≫ epsH = F.map (𝟙 H.obj) ≫ epsH
    rw [F.map_comp, Category.assoc, hb, ha, F.map_id, Category.id_comp]
  have hba : b ≫ a = 𝟙 J.obj := by
    apply (repJ J).1
    change F.map (b ≫ a) ≫ epsJ = F.map (𝟙 J.obj) ≫ epsJ
    rw [F.map_comp, Category.assoc, ha, hb, F.map_id, Category.id_comp]
  refine ⟨⟨a, b, hab, hba⟩, ha, ?_⟩
  intro e he
  apply Iso.ext
  exact (repJ H).1 (he.trans ha.symm)

private theorem transport_pair
    {A B : Type*} [Category A] [Category B]
    (F G : A ⥤ B) (e : F ≅ G) (H M : A) (K : B) (eps : G.obj H ⟶ K)
    (rep : Function.Bijective (fun a : M ⟶ H ↦ G.map a ≫ eps)) :
    Function.Bijective (fun a : M ⟶ H ↦ F.map a ≫ e.hom.app H ≫ eps) := by
  have heq : (fun a : M ⟶ H ↦ F.map a ≫ e.hom.app H ≫ eps) =
      fun a ↦ e.hom.app M ≫ (G.map a ≫ eps) := by
    funext a
    rw [e.hom.naturality_assoc]
  rw [heq]
  constructor
  · intro a b hab
    exact rep.1 ((cancel_epi (e.hom.app M)).1 hab)
  · intro g
    obtain ⟨a, ha⟩ := rep.2 (e.inv.app M ≫ g)
    refine ⟨a, ?_⟩
    change e.hom.app M ≫ (G.map a ≫ eps) = g
    dsimp only at ha
    rw [ha, Iso.hom_inv_id_app_assoc]

set_option maxHeartbeats 1200000 in
-- The actual derived-tower functor types exceed the default kernel reduction budget.
/-- The two local counits determine a counit-preserving overlap isomorphism.
Source: latest smooth-purity blueprint, Gluing, uniqueness on overlaps
(blueprint: lem-sp-tower-binary-overlap-pair).

Proof. Give the two opens and their pullback the inherited field structures. Restrict
both pairs by the open-morphism restriction theorem; its preservation clause puts the
two restricted objects in C_W. The equality of the two composites into X identifies
their compact-support functors with F_(c.precomp jW), using the proved precomposition
comparison. Transport their counits through these actual functor equalities. Each then
represents the same Hom functor on C_W. Transpose each counit under the other bijection;
injectivity makes the transposes inverse and gives the stated counit equation. All
morphisms and equalities are in the ordinary derived category of actual towers. -/
theorem tower_binary_overlap_pair
    (k : Type u) [Field k]
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h) :
  ∀ (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (K : SpTowerCalculus.C l E b q Y.left)
    (U V : X.left.Opens)
    (HU : SpTowerCalculus.C l E b q U.toScheme)
    (HV : SpTowerCalculus.C l E b q V.toScheme)
    (epsU : (SpTowerCalculus.F l E b o q (c.precomp U.ι)).obj HU.obj ⟶ K.obj)
    (epsV : (SpTowerCalculus.F l E b o q (c.precomp V.ι)).obj HV.obj ⟶ K.obj),
    (∀ M : SpTowerCalculus.C l E b q U.toScheme,
      Function.Bijective (fun a : M.obj ⟶ HU.obj ↦
        (SpTowerCalculus.F l E b o q (c.precomp U.ι)).map a ≫ epsU)) →
    (∀ M : SpTowerCalculus.C l E b q V.toScheme,
      Function.Bijective (fun a : M.obj ⟶ HV.obj ↦
        (SpTowerCalculus.F l E b o q (c.precomp V.ι)).map a ≫ epsV)) →
    let wU := Limits.pullback.fst U.ι V.ι
    let wV := Limits.pullback.snd U.ι V.ι
    let jW := wU ≫ U.ι
    ∃ e : (SpTowerCalculus.etalePullback l E b o q wU).obj HU.obj ≅
        (SpTowerCalculus.etalePullback l E b o q wV).obj HV.obj,
      (SpTowerCalculus.F l E b o q (c.precomp jW)).map e.hom ≫
        normalizedOpenCounit l E b o q c V.ι wV jW
          (Limits.pullback.condition.symm) HV.obj K.obj epsV =
        normalizedOpenCounit l E b o q c U.ι wU jW rfl HU.obj K.obj epsU := by
  intro X Y _ _ _ _ _ _ f c K U V HU HV epsU epsV hU hV
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  let W := Limits.pullback U.ι V.ι
  let wU : W ⟶ U.toScheme := Limits.pullback.fst U.ι V.ι
  let wV : W ⟶ V.toScheme := Limits.pullback.snd U.ι V.ι
  let jW : W ⟶ X.left := wU ≫ U.ι
  let XU : Over (Spec (.of k)) := Over.mk (U.ι ≫ X.hom)
  let XV : Over (Spec (.of k)) := Over.mk (V.ι ≫ X.hom)
  let XW : Over (Spec (.of k)) := Over.mk (jW ≫ X.hom)
  have : IsSeparated XU.hom := by dsimp [XU]; infer_instance
  have : LocallyOfFiniteType XU.hom := by dsimp [XU]; infer_instance
  have : QuasiCompact XU.hom := by dsimp [XU]; infer_instance
  have : IsSeparated XV.hom := by dsimp [XV]; infer_instance
  have : LocallyOfFiniteType XV.hom := by dsimp [XV]; infer_instance
  have : QuasiCompact XV.hom := by dsimp [XV]; infer_instance
  have : IsSeparated XW.hom := by dsimp [XW]; infer_instance
  have : LocallyOfFiniteType XW.hom := by dsimp [XW]; infer_instance
  have : QuasiCompact XW.hom := by dsimp [XW]; infer_instance
  let u : XW ⟶ XU := Over.homMk wU (by simp [XU, XW, jW, Category.assoc])
  let v : XW ⟶ XV := Over.homMk wV (by
    change wV ≫ (V.ι ≫ X.hom) = jW ≫ X.hom
    rw [← Category.assoc, ← Limits.pullback.condition])
  let fU : XU ⟶ Y := Over.homMk (U.ι ≫ f.left) (by simp [XU, Category.assoc])
  let fV : XV ⟶ Y := Over.homMk (V.ι ≫ f.left) (by simp [XV, Category.assoc])
  let cU : Compactification fU.left := c.precomp U.ι
  let cV : Compactification fV.left := c.precomp V.ι
  have : IsOpenImmersion u.left := by
    change IsOpenImmersion (Limits.pullback.fst U.ι V.ι)
    infer_instance
  have : IsOpenImmersion v.left := by
    change IsOpenImmersion (Limits.pullback.snd U.ι V.ι)
    infer_instance
  obtain ⟨hWU, repWU⟩ := tower_pair_open_morphism_restriction l E b o q k z h cal
    XW XU Y u fU cU HU K epsU hU
  obtain ⟨hWV, repWV⟩ := tower_pair_open_morphism_restriction l E b o q k z h cal
    XW XV Y v fV cV HV K epsV hV
  let HUW : SpTowerCalculus.C l E b q W :=
    ⟨(SpTowerCalculus.etalePullback l E b o q wU).obj HU.obj, hWU⟩
  let HVW : SpTowerCalculus.C l E b q W :=
    ⟨(SpTowerCalculus.etalePullback l E b o q wV).obj HV.obj, hWV⟩
  let G := SpTowerCalculus.F l E b o q (c.precomp jW)
  let etaU := normalizedOpenCounit l E b o q c U.ι wU jW rfl HU.obj K.obj epsU
  let etaV := normalizedOpenCounit l E b o q c V.ι wV jW
    (Limits.pullback.condition.symm) HV.obj K.obj epsV
  have repU (M : SpTowerCalculus.C l E b q W) :
      Function.Bijective (fun a : M.obj ⟶ HUW.obj ↦ G.map a ≫ etaU) := by
    exact transport_pair _ _
      (eqToIso (compact_support_precomp_comp l E b o q c U.ι wU jW rfl)).symm
      _ _ _ _ (repWU M)
  have repV (M : SpTowerCalculus.C l E b q W) :
      Function.Bijective (fun a : M.obj ⟶ HVW.obj ↦ G.map a ≫ etaV) := by
    exact transport_pair _ _
      (eqToIso (compact_support_precomp_comp l E b o q c V.ι wV jW
        Limits.pullback.condition.symm)).symm _ _ _ _ (repWV M)
  obtain ⟨e, he, _⟩ := representing_pair_counit_unique _ G K.obj HUW HVW
    etaU etaV repU repV
  exact ⟨e, he⟩

end AlgebraicGeometry.ProEtale.SpTowerGluing
