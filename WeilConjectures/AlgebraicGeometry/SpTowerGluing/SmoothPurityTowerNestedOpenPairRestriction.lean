/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerPairOpenRestriction

/-! # Restriction through a nested source open

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

private theorem open_hom_bijective
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (L : A ⥤ B) (R : B ⥤ A) (adj : L ⊣ R)
    (F : B ⥤ D) (G : A ⥤ D) (e : L ⋙ F ≅ G)
    (H : B) (K : D) (eps : F.obj H ⟶ K) (M : A)
    (hlocal : Function.Bijective (fun z : M ⟶ R.obj H ↦
      G.map z ≫ e.inv.app (R.obj H) ≫ F.map (adj.counit.app H) ≫ eps)) :
    Function.Bijective (fun z : L.obj M ⟶ H ↦ F.map z ≫ eps) := by
  let h := (adj.homEquiv M H).trans (Equiv.ofBijective _ hlocal)
  let e' := Iso.homCongr (e.app M) (Iso.refl K)
  have heq : (fun z : L.obj M ⟶ H ↦ F.map z ≫ eps) =
      fun z ↦ e'.symm (h z) := by
    funext z
    dsimp [e', h, Iso.homCongr]
    simp only [Category.comp_id]
    rw [← e.hom.naturality_assoc]
    simp only [Iso.hom_inv_id_app_assoc, Functor.comp_map, ← F.map_comp_assoc,
      ← adj.homEquiv_counit, Equiv.symm_apply_apply]
  rw [heq]
  exact e'.symm.bijective.comp h.bijective

private theorem restrict_test
    {A B D : Type*} [Category A] [Category B] [Category D]
    (L : A ⥤ B) (R : B ⥤ A) (adj : L ⊣ R)
    (F : B ⥤ D) (G : A ⥤ D) (e : L ⋙ F ≅ G)
    (H : B) (K : D) (eps : F.obj H ⟶ K)
    (M : A)
    (rep : Function.Bijective (fun a : L.obj M ⟶ H ↦ F.map a ≫ eps)) :
    Function.Bijective (fun a : M ⟶ R.obj H ↦
      G.map a ≫ e.inv.app (R.obj H) ≫ F.map (adj.counit.app H) ≫ eps) := by
  let t := (adj.homEquiv M H).symm.trans
    (Equiv.ofBijective _ rep)
  let v := (Iso.homCongr (e.app M) (Iso.refl K)).symm
  have hv : (fun a : M ⟶ R.obj H ↦
      G.map a ≫ e.inv.app (R.obj H) ≫ F.map (adj.counit.app H) ≫ eps) =
      fun a ↦ v.symm (t a) := by
    funext a
    dsimp [v, t, Iso.homCongr]
    simp only [Category.comp_id, Adjunction.homEquiv_counit, Functor.map_comp,
      Category.assoc]
    rw [e.inv.naturality_assoc]
    rfl
  rw [hv]
  exact v.symm.bijective.comp t.bijective


/-- A canonical representing restriction remains representing on a smaller open.
Source: latest smooth-purity blueprint, Gluing, restriction of local representing pairs
(blueprint: lem-sp-tower-nested-open-pair-restriction).

Proof. Extend a test on W by zero to U. Open preservation puts this extension
in C_U. Transpose the assumed canonical bijection on U across its open adjunction;
this gives the global Hom map on the further extension from U to X. The canonical
composition isomorphism of open extensions identifies this doubly extended test
with extension directly from W to X. Naturality of F and eps transports the global
Hom bijection across this isomorphism. Finally transpose back across the direct
open adjunction for W, using openComposition to identify the compact-support
source. This yields exactly the displayed once-restricted counit word. This route
requires no equality between twice-restricted and once-restricted counit words.
No binary descent, choice of a global counit, or finite-cover induction occurs. -/
theorem tower_nested_open_pair_restriction
    (k : Type u) [Field k]
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (H : SpTowerCalculus.C l E b q X.left)
    (K : SpTowerCalculus.C l E b q Y.left)
    (eps : (SpTowerCalculus.F l E b o q c).obj H.obj ⟶ K.obj)
    (U W : X.left.Opens) (hWU : W ≤ U)
    (repU : ∀ M : SpTowerCalculus.C l E b q U.toScheme,
      Function.Bijective (fun a : M.obj ⟶
          (SpTowerCalculus.etalePullback l E b o q U.ι).obj H.obj ↦
        (SpTowerCalculus.F l E b o q (c.precomp U.ι)).map a ≫
          openMorphismCounit l E b o q c H.obj K.obj eps U.ι)) :
    ∀ M : SpTowerCalculus.C l E b q W.toScheme,
      Function.Bijective (fun a : M.obj ⟶
          (SpTowerCalculus.etalePullback l E b o q W.ι).obj H.obj ↦
        (SpTowerCalculus.F l E b o q (c.precomp W.ι)).map a ≫
          openMorphismCounit l E b o q c H.obj K.obj eps W.ι) := by
  intro M
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  let XU : Over (Spec (.of k)) := Over.mk (U.ι ≫ X.hom)
  let XW : Over (Spec (.of k)) := Over.mk (W.ι ≫ X.hom)
  have : IsSeparated XU.hom := by dsimp [XU]; infer_instance
  have : LocallyOfFiniteType XU.hom := by dsimp [XU]; infer_instance
  have : QuasiCompact XU.hom := by dsimp [XU]; infer_instance
  have : IsSeparated XW.hom := by dsimp [XW]; infer_instance
  have : LocallyOfFiniteType XW.hom := by dsimp [XW]; infer_instance
  have : QuasiCompact XW.hom := by dsimp [XW]; infer_instance
  let j : XW ⟶ XU := Over.homMk (X.left.homOfLE hWU) (by
    change X.left.homOfLE hWU ≫ (U.ι ≫ X.hom) = W.ι ≫ X.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])
  have : IsOpenImmersion j.left := by
    change IsOpenImmersion (X.left.homOfLE hWU)
    infer_instance
  let N : SpTowerCalculus.C l E b q U.toScheme :=
    ⟨(SpTowerCalculus.openExtension l E b o q j.left).obj M.obj,
      tower_open_morphism_extension_preserves l E b o q k z h cal XW XU j M⟩
  have hN : Function.Bijective (fun a :
      (SpTowerCalculus.openExtension l E b o q U.ι).obj N.obj ⟶ H.obj ↦
      (SpTowerCalculus.F l E b o q c).map a ≫ eps) :=
    open_hom_bijective _ _ (openAdjunction l E b o q U.ι) _ _
      (SpTowerCalculus.openComposition l E b o q U.ι c) H.obj K.obj eps N.obj (repU N)
  let RW := SpTowerCalculus.realization l E b W.toScheme (q.abelian W.toScheme)
  let RU := SpTowerCalculus.realization l E b U.toScheme (q.abelian U.toScheme)
  let RX := SpTowerCalculus.realization l E b X.left (q.abelian X.left)
  let L := SpTowerShriek.openD l E b (o.openOp j.left)
  let LU := SpTowerShriek.openD l E b (o.openOp U.ι)
  let openFunctor (a : {a : W.toScheme ⟶ X.left // IsOpenImmersion a}) :=
    letI := a.property
    SpTowerShriek.openD l E b (o.openOp a.val)
  have hj : (⟨j.left ≫ U.ι, inferInstance⟩ :
      {a : W.toScheme ⟶ X.left // IsOpenImmersion a}) = ⟨W.ι, inferInstance⟩ :=
    Subtype.ext (Scheme.homOfLE_ι X.left hWU)
  let e : L ⋙ LU ≅ SpTowerShriek.openD l E b (o.openOp W.ι) :=
    SpTowerCalculus.sequenceOpenComposition l E b o j.left U.ι ≪≫
      eqToIso (congrArg openFunctor hj)
  let t : (SpTowerCalculus.openExtension l E b o q U.ι).obj N.obj ≅
      (SpTowerCalculus.openExtension l E b o q W.ι).obj M.obj :=
    RX.inverse.mapIso
      (LU.mapIso (RU.counitIso.app (L.obj (RW.functor.obj M.obj))) ≪≫
        e.app (RW.functor.obj M.obj))
  have hW : Function.Bijective (fun a :
      (SpTowerCalculus.openExtension l E b o q W.ι).obj M.obj ⟶ H.obj ↦
      (SpTowerCalculus.F l E b o q c).map a ≫ eps) := by
    let v := Iso.homCongr t (Iso.refl H.obj)
    let w := Iso.homCongr ((SpTowerCalculus.F l E b o q c).mapIso t) (Iso.refl K.obj)
    have heq : (fun a :
        (SpTowerCalculus.openExtension l E b o q W.ι).obj M.obj ⟶ H.obj ↦
        (SpTowerCalculus.F l E b o q c).map a ≫ eps) =
        fun a ↦ w ((Equiv.ofBijective _ hN) (v.symm a)) := by
      funext a
      simp only [v, w, Iso.homCongr, Equiv.coe_ofBijective,
        Iso.refl_inv, Iso.refl_hom, Category.comp_id, Functor.mapIso_inv,
        Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
      simpa only [Functor.map_comp, Category.assoc] using
        (congrArg (fun a ↦ (SpTowerCalculus.F l E b o q c).map a ≫ eps)
          (t.inv_hom_id_assoc a)).symm
    rw [heq]
    exact w.bijective.comp (hN.comp v.symm.bijective)
  exact restrict_test _ _ (openAdjunction l E b o q W.ι) _ _
    (SpTowerCalculus.openComposition l E b o q W.ι c) H.obj K.obj eps M.obj hW

end AlgebraicGeometry.ProEtale.SpTowerGluing
