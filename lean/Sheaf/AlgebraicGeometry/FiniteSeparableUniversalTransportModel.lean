/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.IntermediateField.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.PointwisePullbackLimit
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Spreading a descent datum on an existing finite model

Source: Stacks Project, Tag 01ZM (2), (3); Tag 023V.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

private theorem transport_left_congr
    {X S T : Scheme.{u}} {f : X ⟶ S} {V : Over X} (D : Over.DescentDatum f V)
    {a b a' b' : T ⟶ X} {hab : a ≫ f = b ≫ f} {hab' : a' ≫ f = b' ≫ f}
    (x : Over.mk a ⟶ V) (y : Over.mk a' ⟶ V)
    (ha : a = a') (hb : b = b') (hxy : x.left = y.left) :
    (D.transport a b hab x).left = (D.transport a' b' hab' y).left := by
  subst a' b'
  have h : x = y := by ext; exact hxy
  subst y
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The universal transport of a descent datum is a single morphism over the double base
 product. It descends to a finite separable enlargement of a given finite model.

Proof: write `ks` as the filtered colimit of its finitely generated `k`-subalgebras,
 all of which are finite separable fields. Restrict the inverse system of their spectra to
 fields containing `K`. Its base change along `JK → Spec K` has limit `Js`. Take fibre
 products over `Spec k` with the original system. The pointwise pullback limit theorem
 identifies the new limit with `Js ×_k Spec ks`; the transition maps are affine and the
 terms are quasi-compact and quasi-separated. Compose the universal transport of `E` with
 `q:Js → JK`. This is a morphism over `Spec K`, using the second base factor. The
 finite-presentation morphism-factorization theorem descends it to a stage `L`. Pair this
 morphism with the second projection to construct `t:JL ×_k Spec L → JL`. Its being over
 the second base factor gives the structure-map equation. The factorization equality and
 naturality of `E` give pointwise compatibility, by factoring each pair of points through
 the universal double product. Pullback pasting gives `r`, `qL`, the cartesian squares and
 their composite. No identity or cocycle equation is required at this step; those equations
 are proved by faithfully flat testing in the consuming theorem.

Source: Stacks Project, Tag 01ZM (2), and Tag 023V.
(blueprint: lem-pd-finite-separable-universal-transport-model) -/
theorem exists_finiteSeparable_universalTransportModel
    {k ks : Type u} [Field k] [Field ks] [Algebra k ks] [IsSepClosure k ks]
    (K : IntermediateField k ks) [FiniteDimensional k K] [Algebra.IsSeparable k K]
    (JK : Over (Spec (.of K))) [LocallyOfFinitePresentation JK.hom]
    [QuasiCompact JK.hom] [QuasiSeparated JK.hom]
    (Js : Over (Spec (.of ks))) (q : Js.left ⟶ JK.left)
    (hq : IsPullback q Js.hom JK.hom (Spec.map (CommRingCat.ofHom (algebraMap K ks))))
    (E : Over.DescentDatum (Spec.map (CommRingCat.ofHom (algebraMap k ks))) Js) :
    ∃ (L : IntermediateField k ks), FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
      ∃ (hKL : K ≤ L) (JL : Over (Spec (.of L))) (r : JL.left ⟶ JK.left),
        IsPullback r JL.hom JK.hom
          (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hKL).toRingHom)) ∧
        ∃ (qL : Js.left ⟶ JL.left)
          (hqL : IsPullback qL Js.hom JL.hom
            (Spec.map (CommRingCat.ofHom (algebraMap L ks))))
          (t : pullback
            (JL.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶ JL.left),
          qL ≫ r = q ∧
          t ≫ JL.hom = pullback.snd
            (JL.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (Spec.map (CommRingCat.ofHom (algebraMap k L))) ∧
          ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Spec (.of ks))
            (h : f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap k ks)) =
              f₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap k ks)))
            (a : Over.mk f₁ ⟶ Js),
            pullback.lift (a.left ≫ qL)
              (f₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap L ks))) (by
                calc
                  (a.left ≫ qL) ≫ (JL.hom ≫
                      Spec.map (CommRingCat.ofHom (algebraMap k L))) =
                      (a.left ≫ Js.hom) ≫
                        (Spec.map (CommRingCat.ofHom (algebraMap L ks)) ≫
                          Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
                    rw [Category.assoc, ← Category.assoc qL, hqL.w]
                    simp only [Category.assoc]
                  _ = f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap k ks)) := by
                    rw [Over.w a, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                      ← IsScalarTower.algebraMap_eq]
                    rfl
                  _ = (f₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap L ks))) ≫
                      Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
                    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                      ← IsScalarTower.algebraMap_eq, h]) ≫ t =
              (E.transport f₁ f₂ h a).left ≫ qL := by
  classical
  have : Algebra.IsAlgebraic k ks := Algebra.IsSeparable.isAlgebraic k ks
  let I := {A : Subalgebra k ks // A.FG}
  have : Nonempty I := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩
  have : IsDirectedOrder I := ⟨fun A B ↦ ⟨⟨A.1 ⊔ B.1, A.2.sup B.2⟩,
    show A.1 ≤ A.1 ⊔ B.1 from le_sup_left, show B.1 ≤ A.1 ⊔ B.1 from le_sup_right⟩⟩
  let D : Iᵒᵖ ⥤ Scheme.{u} := (CommRingCat.fgSubalgebraDiagramOf k ks).op ⋙ Scheme.Spec
  let c : Cone D := Scheme.Spec.mapCone (CommRingCat.fgSubalgebraCoconeOf k ks).op
  have hc : IsLimit c :=
    isLimitOfPreserves Scheme.Spec (CommRingCat.isColimitFGSubalgebraCocone k ks).op
  have hfgK : K.toSubalgebra.FG := (Subalgebra.fg_iff_finiteType _).mpr inferInstance
  let i : Iᵒᵖ := Opposite.op ⟨K.toSubalgebra, hfgK⟩
  let p₀ : JK.left ⟶ D.obj i := JK.hom
  let D₂ := Over.forget i ⋙ D
  let c₂ := c.whisker (Over.forget i)
  have hc₂ : IsLimit c₂ := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  let D₁ := baseChangeDiagram D (i := i) p₀
  let c₁ := baseChangeCone D c (i := i) p₀
  have hc₁ : IsLimit c₁ := isLimitBaseChangeCone D c (i := i) p₀ hc
  let t₀ : D ⟶ (Functor.const _).obj (Spec (.of k)) :=
    { app a := Spec.map (CommRingCat.ofHom (algebraMap k a.unop.1))
      naturality a b g := by
        change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ 𝟙 _
        rw [Category.comp_id, ← Spec.map_comp]
        congr 1 }
  let t₂ := Functor.whiskerLeft (Over.forget i) t₀
  let t₁ : D₁ ⟶ (Functor.const _).obj (Spec (.of k)) :=
    baseChangeDiagramπ D (i := i) p₀ ≫ t₂
  let pk : c₂.pt ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k ks))
  let f₁ : c₁.pt ⟶ Spec (.of k) := pullback.snd p₀ (c.π.app i) ≫ pk
  have hf₂ (a : Over i) : c₂.π.app a ≫ t₂.app a = pk := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
  have hf₁ (a : Over i) : c₁.π.app a ≫ t₁.app a = f₁ := by
    change (baseChangeCone D c (i := i) p₀).π.app a ≫
      pullback.snd p₀ (D.map a.hom) ≫ t₂.app a = f₁
    rw [baseChangeCone_π_app_snd_assoc]
    change pullback.snd p₀ (c.π.app i) ≫ c₂.π.app a ≫ t₂.app a = f₁
    rw [hf₂]
  let R : Over i ⥤ Scheme.{u} :=
    { obj a := pullback (t₁.app a) (t₂.app a)
      map {a b} g := pullback.map _ _ _ _ (D₁.map g) (D₂.map g) (𝟙 (Spec (.of k)))
        (by simp [t₁.naturality])
        (by simp)
      map_id a := by apply pullback.hom_ext <;> simp [D₂]
      map_comp g h := by apply pullback.hom_ext <;> simp [Category.assoc] }
  let cr : Cone R :=
    { pt := pullback f₁ pk
      π :=
        { app a := pullback.map _ _ _ _ (c₁.π.app a) (c₂.π.app a) (𝟙 _)
            (by simp [hf₁]) (by simp [hf₂])
          naturality a b g := by
            apply pullback.hom_ext
            · have hh : c₁.π.app a ≫ D₁.map g = c₁.π.app b := c₁.w g
              simp [R, Category.assoc, hh]
            · have hh : c₂.π.app a ≫ D₂.map g = c₂.π.app b := c₂.w g
              simp [R, Category.assoc, hh] } }
  have hcr : IsLimit cr :=
    isLimit_pointwisePullback D₁ D₂ t₁ t₂ c₁ c₂ hc₁ hc₂ f₁ pk hf₁ hf₂
  have hD {a b : Iᵒᵖ} (g : a ⟶ b) : IsAffineHom (D.map g) :=
    inferInstanceAs (IsAffineHom (Spec.map _))
  have hD₂ {a b : Over i} (g : a ⟶ b) : IsAffineHom (D₂.map g) := hD g.left
  have hD₁ {a b : Over i} (g : a ⟶ b) : IsAffineHom (D₁.map g) := inferInstance
  have hR {a b : Over i} (g : a ⟶ b) : IsAffineHom (R.map g) :=
    MorphismProperty.pullbackMap (P := @IsAffineHom) (hD₁ g) (hD₂ g)
      (by simp) (by simp)
  have hDc (a : Iᵒᵖ) : CompactSpace (D.obj a) :=
    inferInstanceAs (CompactSpace (Spec _))
  have hDq (a : Iᵒᵖ) : QuasiSeparatedSpace (D.obj a) :=
    inferInstanceAs (QuasiSeparatedSpace (Spec _))
  have hDc₂ (a : Over i) : CompactSpace (D₂.obj a) := hDc a.left
  have hDq₂ (a : Over i) : QuasiSeparatedSpace (D₂.obj a) := hDq a.left
  have : QuasiCompact p₀ := inferInstanceAs (QuasiCompact JK.hom)
  have : QuasiSeparated p₀ := inferInstanceAs (QuasiSeparated JK.hom)
  have : LocallyOfFinitePresentation p₀ :=
    inferInstanceAs (LocallyOfFinitePresentation JK.hom)
  have h₁qc (a : Over i) : QuasiCompact (t₁.app a) := by
    change QuasiCompact (pullback.snd p₀ (D.map a.hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k a.left.unop.1)))
    infer_instance
  have h₁qs (a : Over i) : QuasiSeparated (t₁.app a) := by
    change QuasiSeparated (pullback.snd p₀ (D.map a.hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k a.left.unop.1)))
    infer_instance
  have hRc (a : Over i) : CompactSpace (R.obj a) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (t₁.app a) (t₂.app a))
  have hRq (a : Over i) : QuasiSeparatedSpace (R.obj a) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd (t₁.app a) (t₂.app a))
  let sR : R ⟶ (Functor.const _).obj (D.obj i) :=
    { app a := pullback.snd (t₁.app a) (t₂.app a) ≫ D.map a.hom
      naturality a b g := by simp [R, D₂, ← D.map_comp, Over.w g] }
  have hq₀ : IsPullback q Js.hom p₀ (c.π.app i) := hq
  let e := hq₀.isoPullback
  let a : Over.mk (pullback.fst f₁ pk ≫ pullback.snd p₀ (c.π.app i)) ⟶ Js :=
    Over.homMk (pullback.fst f₁ pk ≫ e.inv) (by rw [Category.assoc, hq₀.isoPullback_inv_snd]; rfl)
  let u := (E.transport (pullback.fst f₁ pk ≫ pullback.snd p₀ (c.π.app i))
    (pullback.snd f₁ pk) (by
      change (pullback.fst f₁ pk ≫ pullback.snd p₀ (c.π.app i)) ≫ pk =
        pullback.snd f₁ pk ≫ pk
      rw [Category.assoc]
      exact pullback.condition) a).left ≫ q
  have hu : u ≫ p₀ = pullback.snd f₁ pk ≫ c.π.app i := by
    dsimp only [u]
    rw [Category.assoc, hq₀.w, ← Category.assoc, Over.w]
    rfl
  have hus : cr.π ≫ sR = (Functor.const _).map (u ≫ p₀) := by
    ext a
    have hw : c₂.π.app a ≫ D.map a.hom = c.π.app i := c.w a.hom
    simp [cr, sR, hu, hw]
  obtain ⟨j, v, hv, hvS⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation R sR p₀ cr hcr u hus
  have : Algebra.IsIntegral k j.left.unop.1 :=
    Algebra.IsIntegral.of_injective j.left.unop.1.val Subtype.val_injective
  let L : IntermediateField k ks := Algebra.IsAlgebraic.toIntermediateField j.left.unop.1
  have hL : FiniteDimensional k L := by
    have : Algebra.FiniteType k j.left.unop.1 :=
      (Subalgebra.fg_iff_finiteType _).mp j.left.unop.2
    exact Algebra.IsIntegral.finite (R := k) (A := j.left.unop.1)
  have hLs : Algebra.IsSeparable k L := inferInstance
  have hKL : K ≤ L := leOfHom j.hom.unop
  let JL : Over (Spec (.of L)) := Over.mk (pullback.snd p₀ (D.map j.hom))
  let r : JL.left ⟶ JK.left := pullback.fst p₀ (D.map j.hom)
  have hr : IsPullback r JL.hom JK.hom
      (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hKL).toRingHom)) :=
    IsPullback.of_hasPullback p₀ (D.map j.hom)
  let qL : Js.left ⟶ JL.left := e.hom ≫ c₁.π.app j
  have hqL : IsPullback qL Js.hom JL.hom
      (Spec.map (CommRingCat.ofHom (algebraMap L ks))) :=
    (isPullback_baseChangeCone_π D c p₀ j).of_iso e.symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp [qL, c₁]) (by simp [e]) (by simp [JL]) (by simp; rfl)
  let t : pullback (JL.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶ JL.left :=
    pullback.lift v (pullback.snd (t₁.app j) (t₂.app j)) hvS
  refine ⟨L, hL, hLs, hKL, JL, r, hr, qL, hqL, t, ?_, ?_, ?_⟩
  · simp [qL, r, c₁, e]
  · exact pullback.lift_snd _ _ _
  · intro T f₁' f₂' h a'
    let z : T ⟶ cr.pt := pullback.lift (a'.left ≫ e.hom) f₂' (by
      change (a'.left ≫ e.hom) ≫ (pullback.snd p₀ (c.π.app i) ≫ pk) = f₂' ≫ pk
      rw [← Category.assoc, Category.assoc a'.left, hq₀.isoPullback_hom_snd, Over.w a']
      exact h)
    have hz₁ : z ≫ pullback.fst f₁ pk = a'.left ≫ e.hom := pullback.lift_fst _ _ _
    have hz₂ : z ≫ pullback.snd f₁ pk = f₂' := pullback.lift_snd _ _ _
    have hz₁s : z ≫ (pullback.fst f₁ pk ≫ pullback.snd p₀ (c.π.app i)) = f₁' := by
      rw [← Category.assoc, hz₁, Category.assoc, hq₀.isoPullback_hom_snd]
      exact Over.w a'
    have hza : z ≫ a.left = a'.left := by
      calc
        z ≫ a.left = (a'.left ≫ e.hom) ≫ e.inv := by
          simp only [a, Over.homMk_left, ← Category.assoc, hz₁]
        _ = a'.left := by simp [Category.assoc]
    have hn := E.transport_homMk_comp z
      (pullback.fst f₁ pk ≫ pullback.snd p₀ (c.π.app i)) (pullback.snd f₁ pk)
      (by change _ ≫ pk = _ ≫ pk; rw [Category.assoc]; exact pullback.condition) a
    have hn' := congrArg (fun m ↦ m.left ≫ q) hn
    let b : T ⟶ R.obj j := pullback.lift (a'.left ≫ qL)
      (f₂' ≫ Spec.map (CommRingCat.ofHom (algebraMap L ks))) (by
        calc
          (a'.left ≫ qL) ≫ (JL.hom ≫
              Spec.map (CommRingCat.ofHom (algebraMap k L))) =
              (a'.left ≫ Js.hom) ≫
                (Spec.map (CommRingCat.ofHom (algebraMap L ks)) ≫
                  Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
            rw [Category.assoc, ← Category.assoc qL, hqL.w]
            simp only [Category.assoc]
          _ = f₁' ≫ Spec.map (CommRingCat.ofHom (algebraMap k ks)) := by
            rw [Over.w a', ← Spec.map_comp, ← CommRingCat.ofHom_comp,
              ← IsScalarTower.algebraMap_eq]
            rfl
          _ = (f₂' ≫ Spec.map (CommRingCat.ofHom (algebraMap L ks))) ≫
              Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
            rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
              ← IsScalarTower.algebraMap_eq, h])
    have heq : b = z ≫ cr.π.app j := by
      apply pullback.hom_ext
      · simp only [b, cr, Category.assoc, pullback.lift_fst, pullback.map]
        simpa only [Category.assoc] using
          congrArg (fun m ↦ m ≫ c₁.π.app j) hz₁.symm
      · simp only [b, cr, Category.assoc, pullback.lift_snd, pullback.map]
        rw [← Category.assoc, hz₂]
        rfl
    have heqv := congrArg (fun m ↦ z ≫ m) hv
    have hc := transport_left_congr E (hab' := h)
      (hab := by rw [hz₁s, hz₂]; exact h)
      ((Over.homMk z :
        Over.mk (z ≫ (pullback.fst f₁ pk ≫ pullback.snd p₀ (c.π.app i))) ⟶
          Over.mk (pullback.fst f₁ pk ≫ pullback.snd p₀ (c.π.app i))) ≫ a)
      a' hz₁s hz₂ (by
        simpa only [Over.comp_left, Over.homMk_left] using hza)
    have hfinal : z ≫ u = (E.transport f₁' f₂' h a').left ≫ q := by
      calc
        z ≫ u = _ := by simpa only [u, Over.comp_left, Over.homMk_left,
          Category.assoc] using hn'.symm
        _ = _ := congrArg (fun m ↦ m ≫ q) hc
    apply hr.hom_ext
    · change (pullback.lift (a'.left ≫ qL)
          (f₂' ≫ Spec.map (CommRingCat.ofHom (algebraMap L ks))) _ ≫ t) ≫ r =
        ((E.transport f₁' f₂' h a').left ≫ qL) ≫ r
      change (b ≫ t) ≫ r = ((E.transport f₁' f₂' h a').left ≫ qL) ≫ r
      rw [Category.assoc]
      have htr : t ≫ r = v := pullback.lift_fst _ _ _
      have hqr : qL ≫ r = q := by simp [qL, r, c₁, e]
      rw [htr, heq, Category.assoc, hv, Category.assoc, hqr]
      exact hfinal
    · have hqLw := hqL.w
      have htw : t ≫ JL.hom = pullback.snd (t₁.app j) (t₂.app j) :=
        pullback.lift_snd _ _ _
      change (b ≫ t) ≫ JL.hom = ((E.transport f₁' f₂' h a').left ≫ qL) ≫ JL.hom
      rw [Category.assoc, htw, pullback.lift_snd, Category.assoc, hqLw,
        ← Category.assoc, Over.w]
      rfl


end AlgebraicGeometry
