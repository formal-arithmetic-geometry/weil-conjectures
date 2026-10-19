/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Over
public import Sheaf.AlgebraicGeometry.InvertibleTorsionOrders
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.FieldTheory.SeparableExtension
import Sheaf.FieldTheory.SeparableSmoothColimit
import Sheaf.AlgebraicGeometry.SmoothBaseChangeLimit
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Separable field-extension exchange

Source: Stacks Project, Tags 0F1C and 0F09.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem over_pullback_square {X Y : Scheme.{u}} (a : X ⟶ Y)
    {T S : Over Y} (g : T ⟶ S) :
    IsPullback (pullback.fst T.hom a) ((Over.pullback a).map g).left g.left
      (pullback.fst S.hom a) := by
  have outer : IsPullback (((Over.pullback a).map g).left ≫ pullback.snd S.hom a)
      (pullback.fst T.hom a) a (g.left ≫ S.hom) := by
    simpa only [Over.pullback_map_left, pullback.lift_snd, Over.w] using
      (IsPullback.of_hasPullback T.hom a).flip
  exact (outer.of_right (by simp [Over.pullback_map_left])
    (IsPullback.of_hasPullback S.hom a).flip).flip

/-- The separable case of field-extension exchange.
Source: Stacks Project, Tag 0F1C, separable case (blueprint: lem-kun-separable-exchange).

Proof: Express L as the filtered colimit of its smooth finitely generated K-subalgebras
by Tag 07BV. Base change their spectra to S. The resulting diagram has smooth affine
structure maps and affine transitions, with limit S_L because pullback preserves limits.
Apply smoothBaseChange_of_inverseLimit to g. For each stalk element, hE supplies a
positive annihilator nonzero in K; its image in the global functions of S is a unit.
This is the required elementwise coefficient condition. -/
theorem isIso_derivedBaseChangeMapPlus_separableFieldExtension
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (hsep : Algebra.IsSeparableExtension K L)
    (T S : Over (Spec (.of K))) (g : T ⟶ S)
    [QuasiCompact g.left] [QuasiSeparated g.left]
    (E : _root_.DerivedCategory.Plus
      (Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hE : HasTorsionCohomologyOfInvertibleOrder K T E.obj) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      (⟨by simp [Over.pullback_map_left]⟩ : CommSq
        (pullback.fst T.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))))
        (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map g).left)
        g.left (pullback.fst S.hom
          (Spec.map (CommRingCat.ofHom (algebraMap K L)))))).app E)  := by
  classical
  obtain ⟨hne, hdir, _, _, ⟨hc₀⟩, _, _⟩ :=
    FieldTheory.separable_extension_is_filtered_colimit_smooth hsep
  let A := {A : Subalgebra K L // Algebra.Smooth K A ∧ A.FG}
  let : Nonempty A := hne
  let : IsDirectedOrder A := ⟨hdir⟩
  have : IsCofiltered Aᵒᵖ := inferInstance
  have : IsConnected Aᵒᵖ := IsCofiltered.isConnected _
  let D₀ := (FieldTheory.smoothSubalgebraDiagram K L).op ⋙ Scheme.Spec
  let η₀ : D₀ ⟶ (Functor.const Aᵒᵖ).obj (Spec (.of K)) :=
    { app i := Spec.map (CommRingCat.ofHom (algebraMap K i.unop.1))
      naturality := by
        intro i j h
        dsimp [D₀, FieldTheory.smoothSubalgebraDiagram]
        rw [← Spec.map_comp]
        rfl }
  let r := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let c₀ := Scheme.Spec.mapCone (FieldTheory.smoothSubalgebraCocone K L).op
  have hp₀ (i : Aᵒᵖ) : c₀.π.app i ≫ η₀.app i = r := by
    dsimp [c₀, η₀, FieldTheory.smoothSubalgebraCocone]
    rw [← Spec.map_comp]
    rfl
  let D₁ := Over.lift D₀ η₀
  let c₁ := Over.liftCone D₀ η₀ c₀ r hp₀
  have hc₁ : IsLimit c₁ := Over.isLimitLiftCone D₀ η₀ c₀ r hp₀ hc₀
  let B := Over.pullback S.hom
  let D₂ := D₁ ⋙ B
  let c₂ := B.mapCone c₁
  let D := D₂ ⋙ Over.forget S.left
  let c₃ := (Over.forget S.left).mapCone c₂
  let c := c₃.extend (pullbackSymmetry S.hom r).hom
  have hc : IsLimit c :=
    (isLimitOfPreserves (Over.forget S.left) (isLimitOfPreserves B hc₁)).extendIso _
  let η : D ⟶ (Functor.const Aᵒᵖ).obj S.left :=
    { app i := (D₂.obj i).hom
      naturality := by intro i j h; exact (D₂.map h).w }
  have hη (i : Aᵒᵖ) : c.π.app i ≫ η.app i = pullback.fst S.hom r := by
    simp [c, c₃, c₂, c₁, B, D₂, D₁, η, Over.liftCone]
  have hsm (i : Aᵒᵖ) : Smooth (η.app i) := by
    let : Algebra.Smooth K i.unop.1 := i.unop.2.1
    have : Smooth (η₀.app i) := by
      apply (HasRingHomProperty.Spec_iff (P := @Smooth)).2
      change (algebraMap K i.unop.1).Smooth
      exact RingHom.smooth_algebraMap.mpr inferInstance
    change Smooth (pullback.snd (η₀.app i) S.hom)
    infer_instance
  have hqc (i : Aᵒᵖ) : QuasiCompact (η.app i) := by
    have : QuasiCompact (η₀.app i) := by
      change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap K i.unop.1)))
      infer_instance
    change QuasiCompact (pullback.snd (η₀.app i) S.hom)
    infer_instance
  have hqs (i : Aᵒᵖ) : QuasiSeparated (η.app i) := by
    change QuasiSeparated (pullback.snd (η₀.app i) S.hom)
    infer_instance
  have htrans (i j : Aᵒᵖ) (f : i ⟶ j) : IsAffineHom (D.map f) := by
    have sq := over_pullback_square S.hom (D₁.map f)
    have : IsAffineHom (D₁.map f).left := by
      change IsAffineHom (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion (leOfHom f.unop)).toRingHom))
      infer_instance
    exact MorphismProperty.of_isPullback (P := @IsAffineHom) sq inferInstance
  let gL := (Over.pullback r).map g
  have sq : IsPullback (pullback.fst T.hom r) gL.left g.left
      (pullback.fst S.hom r) := by
    have outer : IsPullback (gL.left ≫ pullback.snd S.hom r)
        (pullback.fst T.hom r) r (g.left ≫ S.hom) := by
      simpa only [gL, Over.pullback_map_left, pullback.lift_snd, Over.w] using
        (IsPullback.of_hasPullback T.hom r).flip
    exact (outer.of_right (by simp [gL, Over.pullback_map_left])
      (IsPullback.of_hasPullback S.hom r).flip).flip
  let chosen : ChosenCartesianSquare (pullback.fst T.hom r) gL.left g.left
      (pullback.fst S.hom r) :=
    { toCommSq := sq.toCommSq
      isoPullback := sq.isoPullback
      hom_fst := by simp
      hom_snd := by simp }
  apply smoothBaseChange_of_inverseLimit S.left D η htrans c hc
    (pullback.fst S.hom r) hη hsm hqc hqs g.left chosen E
  intro q Ω _ _ t x
  obtain ⟨n, ⟨hn, hnK⟩, hx⟩ := hE q Ω t x
  refine ⟨n, hn, hx, ?_⟩
  let φ := (Scheme.ΓSpecIso (.of K)).inv ≫ Scheme.Γ.map S.hom.op
  simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hnK).map φ.hom


end AlgebraicGeometry.Etale
