/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.SpaceLineModuleProjInput
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.Modules.GeneratesFibre
import Mathlib.CategoryTheory.Sites.Subsheaf

/-! # The open generation subspace of a cartesian graded line map -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

private theorem generationSet_isOpen {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S} {f : F ⟶ yoneda.obj T}
    {A : T.left.GradedAlgebraData} {L : TestLineFamily F}
    (ψ : GradedLineMap f A L) (W : SchemeTests F) : IsOpen (ψ.generationSet W) := by
  apply isOpen_iff_forall_mem_open.mpr
  rintro x ⟨B, j, hj, y, rfl, V, h, n, hn, a, ha⟩
  have := hj
  refine ⟨Set.range j.left.left, ?_, j.left.left.isOpenMap.isOpen_range, ⟨y, rfl⟩⟩
  rintro z ⟨b, rfl⟩
  exact ⟨B, j, hj, b, rfl, V, h, n, hn, a, ha⟩

private theorem powerMap_free {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (L : TestLineFamily F) {W V : SchemeTests F} (j : W ⟶ V) (n : ℕ)
    (s : Γ((L.module V).tensorPow n, ⊤)) (hs : Scheme.Modules.IsFreeGenerator s) :
    Scheme.Modules.IsFreeGenerator (L.powerMap j n s) := by
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j.left.left)
  let e := Scheme.Modules.boundaryPullbackComparison j.left.left
  have hη := Adjunction.unit_leftAdjointUniq_hom_app adj
    (Scheme.Modules.pullbackPushforwardAdjunction j.left.left) ((L.module V).tensorPow n)
  have ht := hs.pullback_unit_app_top j.left.left
  have hx := ht.app_hom (e.app ((L.module V).tensorPow n)).symm
  have heq : (e.app ((L.module V).tensorPow n)).hom.app (j.left.left ⁻¹ᵁ ⊤)
      ((adj.unit.app ((L.module V).tensorPow n)).app ⊤ s) =
      ((Scheme.Modules.pullbackPushforwardAdjunction j.left.left).unit.app
        ((L.module V).tensorPow n)).app ⊤ s := by
    exact congrArg (fun q ↦ q.app ⊤ s) hη
  have hsec : (e.app ((L.module V).tensorPow n)).inv.app (j.left.left ⁻¹ᵁ ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction j.left.left).unit.app
        ((L.module V).tensorPow n)).app ⊤ s) =
      (adj.unit.app ((L.module V).tensorPow n)).app ⊤ s := by
    rw [← heq]
    exact congrArg (fun q ↦ q.app _ ((adj.unit.app _).app ⊤ s))
      (e.app ((L.module V).tensorPow n)).hom_inv_id
  change Scheme.Modules.IsFreeGenerator
    ((e.app ((L.module V).tensorPow n)).inv.app (j.left.left ⁻¹ᵁ ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction j.left.left).unit.app
        ((L.module V).tensorPow n)).app ⊤ s)) at hx
  rw [hsec] at hx
  have htop : j.left.left ⁻¹ᵁ (⊤ : V.left.left.Opens) = ⊤ :=
    Scheme.Hom.preimage_top _
  have ht' : Scheme.Modules.IsFreeGenerator
      (M := (Scheme.Modules.tensorPullback j.left.left).obj ((L.module V).tensorPow n))
      (U := ⊤) ((adj.unit.app ((L.module V).tensorPow n)).app ⊤ s) := by
    simpa only [htop] using hx
  exact ht'.app_hom (Scheme.Modules.boundaryPullbackPowIso j.left.left (L.module V) n ≪≫
    Scheme.Modules.boundaryTensorPowIso (L.pullbackIso j) n)

private theorem powerMap_free_on {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (L : TestLineFamily F) {W V : SchemeTests F} (j : W ⟶ V) (n : ℕ)
    (s : Γ((L.module V).tensorPow n, ⊤)) (O : V.left.left.Opens)
    (hO : (⊤ : W.left.left.Opens) ≤ j.left.left ⁻¹ᵁ O)
    (hs : Scheme.Modules.IsFreeGenerator
      (((L.module V).tensorPow n).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op s)) :
    Scheme.Modules.IsFreeGenerator (L.powerMap j n s) := by
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j.left.left)
  let e := Scheme.Modules.boundaryPullbackComparison j.left.left
  have hη := Adjunction.unit_leftAdjointUniq_hom_app adj
    (Scheme.Modules.pullbackPushforwardAdjunction j.left.left) ((L.module V).tensorPow n)
  have ht := (hs.pullback_unit_app j.left.left).map hO
  change Scheme.Modules.IsFreeGenerator
    (((Scheme.Modules.pullback j.left.left).obj ((L.module V).tensorPow n)).presheaf.map
      (homOfLE hO).op (Scheme.Modules.pullbackSection j.left.left
        (((L.module V).tensorPow n).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op s))) at ht
  rw [Scheme.Modules.pullbackSection_map] at ht
  rw [Scheme.Modules.presheaf_map_homOfLE_map_homOfLE] at ht
  have ht0 := Scheme.Modules.IsFreeGenerator.of_presheaf_map
    (M := (Scheme.Modules.pullback j.left.left).obj ((L.module V).tensorPow n))
    (U := j.left.left ⁻¹ᵁ ⊤) (V := ⊤)
    (Scheme.Hom.preimage_top j.left.left).ge le_top ht
  clear ht
  have hx := ht0.app_hom (e.app ((L.module V).tensorPow n)).symm
  have heq : (e.app ((L.module V).tensorPow n)).hom.app (j.left.left ⁻¹ᵁ ⊤)
      ((adj.unit.app ((L.module V).tensorPow n)).app ⊤ s) =
      ((Scheme.Modules.pullbackPushforwardAdjunction j.left.left).unit.app
        ((L.module V).tensorPow n)).app ⊤ s := by
    exact congrArg (fun q ↦ q.app ⊤ s) hη
  have hsec : (e.app ((L.module V).tensorPow n)).inv.app (j.left.left ⁻¹ᵁ ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction j.left.left).unit.app
        ((L.module V).tensorPow n)).app ⊤ s) =
      (adj.unit.app ((L.module V).tensorPow n)).app ⊤ s := by
    rw [← heq]
    exact congrArg (fun q ↦ q.app _ ((adj.unit.app _).app ⊤ s))
      (e.app ((L.module V).tensorPow n)).hom_inv_id
  change Scheme.Modules.IsFreeGenerator
    ((e.app ((L.module V).tensorPow n)).inv.app (j.left.left ⁻¹ᵁ ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction j.left.left).unit.app
        ((L.module V).tensorPow n)).app ⊤ s)) at hx
  rw [hsec] at hx
  have htop : j.left.left ⁻¹ᵁ (⊤ : V.left.left.Opens) = ⊤ :=
    Scheme.Hom.preimage_top _
  have ht' : Scheme.Modules.IsFreeGenerator
      (M := (Scheme.Modules.tensorPullback j.left.left).obj ((L.module V).tensorPow n))
      (U := ⊤) ((adj.unit.app ((L.module V).tensorPow n)).app ⊤ s) := by
    simpa only [htop] using hx
  exact ht'.app_hom (Scheme.Modules.boundaryPullbackPowIso j.left.left (L.module V) n ≪≫
    Scheme.Modules.boundaryTensorPowIso (L.pullbackIso j) n)

private theorem powerMap_generatesAt {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} (L : TestLineFamily F)
    {W V : SchemeTests F} (j : W ⟶ V) (n : ℕ)
    (s : Γ((L.module V).tensorPow n, ⊤))
    (hs : Scheme.Modules.IsFreeGenerator (L.powerMap j n s)) (x : W.left.left) :
    Scheme.Modules.GeneratesAt s (j.left.left x) := by
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j.left.left)
  let e := Scheme.Modules.boundaryPullbackComparison j.left.left
  let q := Scheme.Modules.boundaryPullbackPowIso j.left.left (L.module V) n ≪≫
    Scheme.Modules.boundaryTensorPowIso (L.pullbackIso j) n
  have ht := hs.app_hom q.symm
  have hsec : q.inv.app ⊤ (L.powerMap j n s) =
      (adj.unit.app ((L.module V).tensorPow n)).app ⊤ s := by
    exact congrArg (fun a ↦ a.app ⊤ ((adj.unit.app _).app ⊤ s)) q.hom_inv_id
  change Scheme.Modules.IsFreeGenerator (q.inv.app ⊤ (L.powerMap j n s)) at ht
  rw [hsec] at ht
  have ht' : Scheme.Modules.IsFreeGenerator
      (M := (Scheme.Modules.tensorPullback j.left.left).obj ((L.module V).tensorPow n))
      (U := j.left.left ⁻¹ᵁ ⊤) ((adj.unit.app ((L.module V).tensorPow n)).app ⊤ s) := by
    simpa only [Scheme.Hom.preimage_top] using ht
  have hp := ht'.app_hom (e.app ((L.module V).tensorPow n))
  have hη := Adjunction.unit_leftAdjointUniq_hom_app adj
    (Scheme.Modules.pullbackPushforwardAdjunction j.left.left) ((L.module V).tensorPow n)
  have heq := congrArg (fun q ↦ q.app ⊤ s) hη
  change (e.app ((L.module V).tensorPow n)).hom.app (j.left.left ⁻¹ᵁ ⊤)
      ((adj.unit.app ((L.module V).tensorPow n)).app ⊤ s) = _ at heq
  rw [heq] at hp
  apply Scheme.Modules.generatesAt_of_isFreeGenerator_pullbackSection j.left.left
    ((L.module V).tensorPow n) s (W := j.left.left ⁻¹ᵁ ⊤) (by trivial)
  change Scheme.Modules.IsFreeGenerator
    (((Scheme.Modules.pullback j.left.left).obj ((L.module V).tensorPow n)).presheaf.map
      (homOfLE (le_refl (j.left.left ⁻¹ᵁ ⊤))).op
      (((Scheme.Modules.pullbackPushforwardAdjunction j.left.left).unit.app
        ((L.module V).tensorPow n)).app ⊤ s))
  have hid : (homOfLE (le_refl (j.left.left ⁻¹ᵁ ⊤))).op =
      𝟙 (op (j.left.left ⁻¹ᵁ ⊤)) := rfl
  rw [hid, CategoryTheory.Functor.map_id]
  exact hp

private theorem testToBase_comp {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S} (f : F ⟶ yoneda.obj T)
    {W V : SchemeTests F} (j : W ⟶ V) :
    j.left ≫ testToBase f V = testToBase f W := by
  apply yoneda.map_injective
  simp only [Functor.map_comp, testToBase, Functor.map_preimage, ← Category.assoc]
  rw [CostructuredArrow.w j]

private theorem generationSet_preimage_le {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S} {f : F ⟶ yoneda.obj T}
    {A : T.left.GradedAlgebraData} {L : TestLineFamily F}
    (ψ : GradedLineMap f A L) {W V : SchemeTests F} (j : W ⟶ V) :
    j.left.left ⁻¹' ψ.generationSet V ⊆ ψ.generationSet W := by
  intro x hx
  obtain ⟨B, l, hl, y, hy, C, h, n, hn, a, ha⟩ := hx
  have := hl
  let p : Over.mk (Limits.pullback.fst j.left.left l.left.left ≫ W.left.hom) ⟶
      W.left := Over.homMk (Limits.pullback.fst _ _)
  let q : Over.mk (Limits.pullback.fst j.left.left l.left.left ≫ W.left.hom) ⟶
      B.left := Over.homMk (Limits.pullback.snd _ _) (by
        change _ = Limits.pullback.fst j.left.left l.left.left ≫ W.left.hom
        rw [← j.left.w, ← Category.assoc, Limits.pullback.condition,
          Category.assoc, l.left.w])
  have hpq : p ≫ j.left = q ≫ l.left := by
    apply Over.OverMorphism.ext
    exact Limits.pullback.condition
  let B' : SchemeTests F := CostructuredArrow.mk (yoneda.map p ≫ W.hom)
  let m : B' ⟶ W := CostructuredArrow.homMk p rfl
  let v : B' ⟶ B := CostructuredArrow.homMk q (by
    change yoneda.map q ≫ B.hom = yoneda.map p ≫ W.hom
    rw [← CostructuredArrow.w j, ← CostructuredArrow.w l, ← Category.assoc, ← Category.assoc,
      ← Functor.map_comp, ← Functor.map_comp, hpq])
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := j.left.left) (g := l.left.left) x y hy.symm
  have h' : (⊤ : B'.left.left.Opens) ≤ (testToBase f B').left ⁻¹ᵁ C.1 := by
    have he := congrArg Over.Hom.left (testToBase_comp f v)
    rw [← he]
    intro z hz
    exact h (by trivial)
  refine ⟨B', m, ?_, z, hz, C, h', n, hn, a, ?_⟩
  · change IsOpenImmersion (Limits.pullback.fst j.left.left l.left.left)
    infer_instance
  · rw [ψ.naturality v C h' h n a]
    exact powerMap_free L v n _ ha

private theorem generationSet_image_le {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S} {f : F ⟶ yoneda.obj T}
    {A : T.left.GradedAlgebraData} {L : TestLineFamily F}
    (ψ : GradedLineMap f A L) {W V : SchemeTests F} (j : W ⟶ V)
    {x : W.left.left} (hx : x ∈ ψ.generationSet W) :
    j.left.left x ∈ ψ.generationSet V := by
  obtain ⟨B, l, hl, y, hy, C, h, n, hn, a, ha⟩ := hx
  let O : V.left.left.Opens := (testToBase f V).left ⁻¹ᵁ C.1
  let i : Over.mk (O.ι ≫ V.left.hom) ⟶ V.left := Over.homMk O.ι
  let D : SchemeTests F := CostructuredArrow.mk (yoneda.map i ≫ V.hom)
  let v : D ⟶ V := CostructuredArrow.homMk i rfl
  have himg : Set.range (l.left.left ≫ j.left.left) ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    rintro z ⟨b, rfl⟩
    have he := congrArg Over.Hom.left (testToBase_comp f (l ≫ j))
    change (testToBase f V).left ((l.left.left ≫ j.left.left) b) ∈ C.1
    change ((l ≫ j).left ≫ testToBase f V).left b ∈ C.1
    rw [he]
    exact h (by trivial)
  let bmap := IsOpenImmersion.lift O.ι (l.left.left ≫ j.left.left) himg
  have hbmap := IsOpenImmersion.lift_fac O.ι (l.left.left ≫ j.left.left) himg
  let b : B.left ⟶ D.left := Over.homMk bmap (by
    change bmap ≫ O.ι ≫ V.left.hom = B.left.hom
    rw [← Category.assoc, hbmap, Category.assoc, j.left.w, l.left.w])
  have hb : b ≫ i = l.left ≫ j.left := by
    apply Over.OverMorphism.ext
    exact hbmap
  let q : B ⟶ D := CostructuredArrow.homMk b (by
    change yoneda.map b ≫ yoneda.map i ≫ V.hom = B.hom
    rw [← Functor.map_comp_assoc, hb, Functor.map_comp, Category.assoc,
      CostructuredArrow.w j, CostructuredArrow.w l])
  have hD : (⊤ : D.left.left.Opens) ≤ (testToBase f D).left ⁻¹ᵁ C.1 := by
    have he := congrArg Over.Hom.left (testToBase_comp f v)
    rw [← he]
    intro z hz
    exact z.property
  have hs : Scheme.Modules.IsFreeGenerator
      (L.powerMap q n (ψ.component D C hD n a)) := by
    rw [← ψ.naturality q C h hD n a]
    exact ha
  obtain ⟨E, hyE, hE⟩ := powerMap_generatesAt L q n _ hs y
  let e : Over.mk (E.ι ≫ D.left.hom) ⟶ D.left := Over.homMk E.ι
  let B' : SchemeTests F := CostructuredArrow.mk (yoneda.map e ≫ D.hom)
  let k : B' ⟶ D := CostructuredArrow.homMk e rfl
  have hB' : (⊤ : B'.left.left.Opens) ≤ (testToBase f B').left ⁻¹ᵁ C.1 := by
    rw [← congrArg Over.Hom.left (testToBase_comp f k)]
    intro z hz
    exact hD (by trivial)
  refine ⟨B', k ≫ v, ?_, ⟨q.left.left y, hyE⟩, ?_, C, hB', n, hn, a, ?_⟩
  · change IsOpenImmersion (E.ι ≫ O.ι)
    infer_instance
  · change (E.ι ≫ O.ι) ⟨q.left.left y, hyE⟩ = j.left.left x
    rw [Scheme.Hom.comp_apply]
    change (bmap ≫ O.ι) y = j.left.left x
    rw [hbmap, Scheme.Hom.comp_apply, hy]
  · rw [ψ.naturality k C hB' hD n a]
    exact powerMap_free_on L k n _ E (by
      change (⊤ : E.toScheme.Opens) ≤ E.ι ⁻¹ᵁ E
      rw [E.ι_preimage_self]) hE

private theorem generationSet_preimage {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S} {f : F ⟶ yoneda.obj T}
    {A : T.left.GradedAlgebraData} {L : TestLineFamily F}
    (ψ : GradedLineMap f A L) {W V : SchemeTests F} (j : W ⟶ V) :
    ψ.generationSet W = j.left.left ⁻¹' ψ.generationSet V := by
  apply Set.Subset.antisymm
  · intro x hx
    exact generationSet_image_le ψ j hx
  · exact generationSet_preimage_le ψ j

private def generationSubfunctor {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S} {f : F ⟶ yoneda.obj T}
    {A : T.left.GradedAlgebraData} {L : TestLineFamily F}
    (ψ : GradedLineMap f A L) : Subfunctor F where
  obj W := {a | ψ.generationSet (CostructuredArrow.mk (yonedaEquiv.symm a)) = Set.univ}
  map {W V} i a ha := by
    let j : CostructuredArrow.mk (yonedaEquiv.symm (F.map i a)) ⟶
        CostructuredArrow.mk (yonedaEquiv.symm a) :=
      CostructuredArrow.homMk i.unop (by
        exact yonedaEquiv_symm_naturality_left i.unop F a)
    change ψ.generationSet (CostructuredArrow.mk (yonedaEquiv.symm (F.map i a))) = Set.univ
    rw [generationSet_preimage ψ j, ha]
    exact Set.preimage_univ

private theorem generationSubfunctor_spec {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S} {f : F ⟶ yoneda.obj T}
    {A : T.left.GradedAlgebraData} {L : TestLineFamily F}
    (ψ : GradedLineMap f A L) : ψ.IsGenerationOpen (generationSubfunctor ψ) := by
  intro W a
  rfl

private theorem generationSubfunctor_isSheaf {S : Scheme.{u}}
    (X : AlgebraicSpace S) {T : Over S} {f : X.obj.obj ⟶ yoneda.obj T}
    {A : T.left.GradedAlgebraData} {L : TestLineFamily X.obj.obj}
    (ψ : GradedLineMap f A L) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (generationSubfunctor ψ).toFunctor := by
  apply (isSheaf_iff_isSheaf_of_type _ _).2
  apply (Subfunctor.isSheaf_iff _
    ((isSheaf_iff_isSheaf_of_type _ _).1 X.obj.property)).2
  intro W a ha
  rw [GrothendieckTopology.mem_over_iff] at ha
  have hle : Scheme.fppfTopology ≤ Scheme.jointlySurjectiveTopology := by
    rw [Scheme.jointlySurjectiveTopology_eq_toGrothendieck_jointlySurjectivePretopology]
    change Scheme.fppfPrecoverage.toGrothendieck ≤
      Scheme.jointlySurjectivePrecoverage.toPretopology.toGrothendieck
    rw [Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
    apply Precoverage.toGrothendieck_mono
    intro Y R hR
    exact hR.1
  have hsur := hle _ ha
  change _ ∈ Scheme.jointlySurjectivePretopology W.unop.left at hsur
  change _ ∈ Scheme.jointlySurjectivePrecoverage W.unop.left at hsur
  rw [Scheme.jointlySurjectivePrecoverage,
    Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hsur
  change ψ.generationSet (CostructuredArrow.mk (yonedaEquiv.symm a)) = Set.univ
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨B, b, hb, y, hy⟩ := hsur x
  have hb' := (Sieve.overEquiv_iff _ b).1 hb
  let b' : Over.mk (b ≫ W.unop.hom) ⟶ W.unop := Over.homMk b
  let j : CostructuredArrow.mk (yonedaEquiv.symm (X.obj.obj.map b'.op a)) ⟶
      CostructuredArrow.mk (yonedaEquiv.symm a) :=
    CostructuredArrow.homMk b' (yonedaEquiv_symm_naturality_left b' X.obj.obj a)
  have hgen : ψ.generationSet
      (CostructuredArrow.mk (yonedaEquiv.symm (X.obj.obj.map b'.op a))) = Set.univ := hb'
  have hmem := generationSet_image_le ψ j (x := y) (hgen.ge (Set.mem_univ y))
  exact hy ▸ hmem

private theorem generationSubfunctor_section {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S} {f : F ⟶ yoneda.obj T}
    {A : T.left.GradedAlgebraData} {L : TestLineFamily F}
    (ψ : GradedLineMap f A L) (W : SchemeTests F) (B : Over S) (b : B ⟶ W.left) :
    (W.hom.app (op B) b) ∈ (generationSubfunctor ψ).obj (op B) ↔
      Set.range b.left ⊆ ψ.generationSet W := by
  let j : CostructuredArrow.mk (yonedaEquiv.symm (W.hom.app (op B) b)) ⟶ W :=
    CostructuredArrow.homMk b (by
      apply yonedaEquiv.injective
      simp [yonedaEquiv])
  change ψ.generationSet (CostructuredArrow.mk
    (yonedaEquiv.symm (W.hom.app (op B) b))) = Set.univ ↔ _
  rw [generationSet_preimage ψ j]
  exact ⟨fun h x ⟨y, hy⟩ ↦ hy ▸ h.ge (Set.mem_univ y),
    fun h ↦ Set.eq_univ_of_forall (fun y ↦ h ⟨y, rfl⟩)⟩

private theorem generationSubfunctor_open {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S} {f : F ⟶ yoneda.obj T}
    {A : T.left.GradedAlgebraData} {L : TestLineFamily F}
    (ψ : GradedLineMap f A L) :
    IsRepresentableWith (fun _ _ j ↦ IsOpenImmersion j.left)
      (generationSubfunctor ψ).ι := by
  intro W a
  let V : SchemeTests F := CostructuredArrow.mk a
  let O : W.left.Opens := ⟨ψ.generationSet V, generationSet_isOpen ψ V⟩
  let i : Over.mk (O.ι ≫ W.hom) ⟶ W := Over.homMk O.ι
  have hi : Subfunctor.range (yoneda.map i ≫ a) ≤ generationSubfunctor ψ := by
    intro B x hx
    obtain ⟨b, rfl⟩ := hx
    change a.app B (b ≫ i) ∈ _
    apply (generationSubfunctor_section ψ V B.unop (b ≫ i)).2
    rintro z ⟨y, rfl⟩
    exact (b.left y).property
  let q := Subfunctor.lift (yoneda.map i ≫ a) hi
  refine ⟨Over.mk (O.ι ≫ W.hom), i, q, ?_, ?_⟩
  · apply IsPullback.of_forall_isPullback_app
    intro B
    apply (Types.isPullback_iff _ _ _ _).2
    refine ⟨?_, ?_, ?_⟩
    · rfl
    · intro b c h
      apply (cancel_mono i).1
      exact h.2
    · intro x b hb
      have hmem : a.app B b ∈ (generationSubfunctor ψ).obj B := hb ▸ x.property
      have hO := (generationSubfunctor_section ψ V B.unop b).1 hmem
      have hO' : Set.range b.left ⊆ Set.range O.ι := by
        rw [Scheme.Opens.range_ι]
        exact hO
      let c : B.unop ⟶ Over.mk (O.ι ≫ W.hom) :=
        Over.homMk (IsOpenImmersion.lift O.ι b.left hO') (by
          change IsOpenImmersion.lift O.ι b.left hO' ≫ O.ι ≫ W.hom = B.unop.hom
          rw [← Category.assoc, IsOpenImmersion.lift_fac, b.w])
      have hc : c ≫ i = b := by
        apply Over.OverMorphism.ext
        exact IsOpenImmersion.lift_fac O.ι b.left hO'
      refine ⟨c, ?_, hc⟩
      apply Subtype.ext
      change a.app B (c ≫ i) = x.val
      rw [hc]
      exact hb.symm
  · change IsOpenImmersion O.ι
    infer_instance

private theorem representableWith_pullback {S : Scheme.{u}}
    {F G H K : (Over S)ᵒᵖ ⥤ Type u}
    {q : H ⟶ F} {v : H ⟶ G} {i : F ⟶ K} {p : G ⟶ K}
    (sq : IsPullback q v i p) (P : MorphismProperty (Over S))
    (hp : IsRepresentableWith P p) : IsRepresentableWith P q := by
  intro T a
  obtain ⟨R, r, b, hb, hr⟩ := hp T (a ≫ i)
  let e := sq.lift (yoneda.map r ≫ a) b (by
    rw [Category.assoc]
    exact hb.w.symm)
  refine ⟨R, r, e, ?_, hr⟩
  apply IsPullback.of_right (t := sq.flip)
    (p := sq.lift_fst _ _ _)
  simpa only [sq.lift_snd] using hb

private theorem subfunctor_diagonal {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : Subfunctor X.obj.obj) :
    IsRepresentable (prod.lift (𝟙 U.toFunctor) (𝟙 U.toFunctor)) := by
  have sq : IsPullback (prod.lift (𝟙 U.toFunctor) (𝟙 U.toFunctor)) U.ι
      (prod.map U.ι U.ι) (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)) := by
    apply IsPullback.of_isLimit' ⟨by
      apply prod.hom_ext <;> simp⟩
    refine PullbackCone.IsLimit.mk _
      (fun s ↦ s.fst ≫ prod.fst) ?_ ?_ ?_
    · intro s
      apply prod.hom_ext
      · simp
      · apply (cancel_mono U.ι).1
        have h1 := congrArg (fun a ↦ a ≫ prod.fst) s.condition
        have h2 := congrArg (fun a ↦ a ≫ prod.snd) s.condition
        simp only [Category.assoc, prod.map_fst, prod.map_snd, prod.lift_fst,
          prod.lift_snd, Category.comp_id] at h1 h2
        simpa using h1.trans h2.symm
    · intro s
      have h1 := congrArg (fun a ↦ a ≫ prod.fst) s.condition
      simpa using h1
    · intro s m hm hn
      have h1 := congrArg (fun a ↦ a ≫ prod.fst) hm
      simpa using h1
  exact representableWith_pullback sq ⊤ X.property.1

/-- The positive-degree generator condition on scheme tests is represented by an open
algebraic subspace.

Source: Stacks Project, Divisors on Spaces, Tag 0D2Z, opening definition of U(psi);
Constructions, Tag 01O9, description of U(psi) by generator opens
(blueprint: lem-trf-space-line-generation-open).

Proof: A generator witness on an open test gives the entire image of that open,
so the generation set is open. Pulling back a witness along an arbitrary scheme map
preserves free generators by the tensor-pullback adjunction and the specified power
isomorphism. Conversely, factor its composite test through the inverse image of its
affine base open. Naturality identifies the witness with a pulled-back section.
A free generator after pullback generates near the image point: express the section
in a local frame and use that a local ring map reflects units. Restrict to such a
neighbourhood to recover a witness on the original test. Thus generation sets pull
back exactly under all test maps; coherence is not needed for this argument.
Define U(W) to consist of sections whose generation set is all of W. The pullback
identity proves it is a subfunctor. It is an fppf subsheaf because fppf covering
sieves are jointly surjective on points. On each test its pullback is represented
by the open generation set, using unique factorization through an open immersion.
The diagonal of any subfunctor of X is the pullback of the diagonal of X along the
product of its inclusions, so is representable. Pulling an etale surjective atlas
of X back to U gives its etale surjective atlas, whose source is the open just
constructed. All constructions allow empty schemes and arbitrary unions. No
flatness of the test maps or finite generation of the algebra is used. -/
theorem exists_space_line_generation_open {S : Scheme.{u}} (T : Over S)
    (X : AlgebraicSpace S) (f : X.obj.obj ⟶ yoneda.obj T)
    (A : T.left.GradedAlgebraData) (L : TestLineFamily X.obj.obj)
    (ψ : GradedLineMap f A L) :
    ∃ (U : Subfunctor X.obj.obj)
      (hU : Presheaf.IsSheaf (Scheme.fppfTopology.over S) U.toFunctor),
      IsAlgebraicSpace ⟨U.toFunctor, hU⟩ ∧
      IsRepresentableWith (fun _ _ j ↦ IsOpenImmersion j.left) U.ι ∧
      ψ.IsGenerationOpen U := by
  let U := generationSubfunctor ψ
  have hsheaf := generationSubfunctor_isSheaf X ψ
  have hopen := generationSubfunctor_open ψ
  refine ⟨U, hsheaf, ⟨subfunctor_diagonal X U, ?_⟩, hopen,
    generationSubfunctor_spec ψ⟩
  obtain ⟨V, p, hp, hs⟩ := X.property.2
  obtain ⟨R, r, q, sq, hr⟩ := hopen V p
  exact ⟨R, q,
    representableWith_pullback sq (fun _ _ p ↦ Etale p.left) hp,
    representableWith_pullback sq (fun _ _ p ↦ Surjective p.left) hs⟩


end AlgebraicGeometry.AlgebraicSpace
