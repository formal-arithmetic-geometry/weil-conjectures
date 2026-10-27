/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-!
# Units and ordinary descent maps from étale line frames

Source: Stacks Project, Descent, Tag 03DX (2), overlap isomorphisms in the proof;
Sheaves, Tag 0095, tensor pullback (blueprint: lem-trf-etale-line-frame-transition-units).

The module sheaf is given by the two fields of the recorded `SheafOfModules`
definition: its underlying module presheaf and its sheaf condition. Frames on the localized
site are module-presheaf isomorphisms; because both objects are sheaves, these are
exactly module-sheaf isomorphisms. Products in `X.Etale` are fibre products over X.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A frame on a localized small étale site, using Mathlib precomposition.
Source: Stacks, Tag 03DX (2) (blueprint: lem-trf-etale-line-frame-transition-units). -/
abbrev TrfEtaleFrame {X : Scheme.{u}}
    (G : _root_.PresheafOfModules.{u}
      (X.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (U : X.Etale) :=
  PresheafOfModules.unit ((Over.forget U).op ⋙
      (X.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})) ≅
    (PresheafOfModules.pushforward₀ (Over.forget U)
      (X.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})).obj G

/-- The change of frames evaluated on a test object mapping to the overlap.
Source: Stacks, Tag 03DX (2) (blueprint: lem-trf-etale-line-frame-transition-units). -/
noncomputable def trfEtaleFrameChange {X : Scheme.{u}}
    {G : _root_.PresheafOfModules.{u}
      (X.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    {A B W : X.Etale} (a : TrfEtaleFrame G A) (b : TrfEtaleFrame G B)
    (f : W ⟶ A) (g : W ⟶ B) (s : Γ(W.left, ⊤)) : Γ(W.left, ⊤) :=
  a.inv.app (op (Over.mk f)) (b.hom.app (op (Over.mk g)) s)

/-- The canonical tensor-unit identification, using the existing adjoint structure map.
Source: Stacks, Tags 0095 and 0096
(blueprint: lem-trf-etale-line-frame-transition-units). -/
noncomputable def trfFrameTensorUnit {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (Modules.tensorPullback f).obj (SheafOfModules.unit Z.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf := by
  letI : IsIso (Modules.tensorPullbackObjUnitToUnit f) :=
    (Modules.tensorPullbackObjUnitToUnit_isIso f).1
  exact asIso (Modules.tensorPullbackObjUnitToUnit f)

/-- Pull an automorphism of the ordinary structure module back, in unit coordinates.
Source: Stacks, Tag 0095 (blueprint: lem-trf-etale-line-frame-transition-units). -/
noncomputable def trfFramePullUnit {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (e : SheafOfModules.unit Z.ringCatSheaf ≅ SheafOfModules.unit Z.ringCatSheaf) :
    SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf :=
  (trfFrameTensorUnit f).symm ≪≫ (Modules.tensorPullback f).mapIso e ≪≫
    trfFrameTensorUnit f

/-- Express a b-to-a ordinary overlap isomorphism in tensor-unit coordinates.
Source: Stacks, Tag 03DX (2); Sheaves, Tag 0095
(blueprint: lem-trf-etale-line-frame-transition-units). -/
noncomputable def trfFrameOverlapCoordinates {X : Scheme.{u}} {A B : X.Etale}
    (φ : (Modules.tensorPullback (Limits.prod.snd : Limits.prod A B ⟶ B).left).obj
        (SheafOfModules.unit B.left.ringCatSheaf) ≅
      (Modules.tensorPullback (Limits.prod.fst : Limits.prod A B ⟶ A).left).obj
        (SheafOfModules.unit A.left.ringCatSheaf)) :
    SheafOfModules.unit (Limits.prod A B).left.ringCatSheaf ≅
      SheafOfModules.unit (Limits.prod A B).left.ringCatSheaf :=
  (trfFrameTensorUnit (Limits.prod.snd : Limits.prod A B ⟶ B).left).symm ≪≫ φ ≪≫
    trfFrameTensorUnit (Limits.prod.fst : Limits.prod A B ⟶ A).left

private lemma frame_hom_inv {X : Scheme.{u}}
    {G : _root_.PresheafOfModules.{u}
      (X.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    {A W : X.Etale} (a : TrfEtaleFrame G A) (f : W ⟶ A) (s : Γ(W.left, ⊤)) :
    a.inv.app (op (Over.mk f)) (a.hom.app (op (Over.mk f)) s) = s := by
  exact ConcreteCategory.congr_hom (C := ModuleCat (Γ(W.left, ⊤)))
    (congrArg (fun k ↦ k.app (op (Over.mk f))) a.hom_inv_id) s

private lemma frame_inv_hom {X : Scheme.{u}}
    {G : _root_.PresheafOfModules.{u}
      (X.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    {A W : X.Etale} (a : TrfEtaleFrame G A) (f : W ⟶ A) (s : G.obj (op W)) :
    a.hom.app (op (Over.mk f)) (a.inv.app (op (Over.mk f)) s) = s := by
  exact ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.app (op (Over.mk f))) a.inv_hom_id) s

private lemma frame_change_mul {X : Scheme.{u}}
    {G : _root_.PresheafOfModules.{u}
      (X.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    {A B W : X.Etale} (a : TrfEtaleFrame G A) (b : TrfEtaleFrame G B)
    (f : W ⟶ A) (g : W ⟶ B) (s : Γ(W.left, ⊤)) :
    trfEtaleFrameChange a b f g s = s * trfEtaleFrameChange a b f g 1 := by
  unfold trfEtaleFrameChange
  have h := (a.inv.app (op (Over.mk f))).hom.map_smul s
    (b.hom.app (op (Over.mk g)) (1 : Γ(W.left, ⊤)))
  rw [← (b.hom.app (op (Over.mk g))).hom.map_smul] at h
  simpa only [smul_eq_mul, mul_one] using h

private lemma frame_change_naturality {X : Scheme.{u}}
    {G : _root_.PresheafOfModules.{u}
      (X.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    {A B W V : X.Etale} (a : TrfEtaleFrame G A) (b : TrfEtaleFrame G B)
    (f : W ⟶ A) (g : W ⟶ B) (q : V ⟶ W) (s : Γ(W.left, ⊤)) :
    trfEtaleFrameChange a b (q ≫ f) (q ≫ g) (q.left.appTop s) =
      q.left.appTop (trfEtaleFrameChange a b f g s) := by
  let qa : Over.mk (q ≫ f) ⟶ Over.mk f := Over.homMk q
  let qb : Over.mk (q ≫ g) ⟶ Over.mk g := Over.homMk q
  have ha := PresheafOfModules.naturality_apply a.inv qa.op
    (b.hom.app (op (Over.mk g)) s)
  have hb := PresheafOfModules.naturality_apply b.hom qb.op s
  change b.hom.app (op (Over.mk (q ≫ g))) (q.left.appTop s) =
    G.map q.op (b.hom.app (op (Over.mk g)) s) at hb
  change a.inv.app (op (Over.mk (q ≫ f)))
      (G.map q.op (b.hom.app (op (Over.mk g)) s)) =
    q.left.appTop (trfEtaleFrameChange a b f g s) at ha
  exact (congrArg (fun z ↦ a.inv.app (op (Over.mk (q ≫ f))) z) hb).trans ha

private lemma frame_change_cancel {X : Scheme.{u}}
    {G : _root_.PresheafOfModules.{u}
      (X.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    {A B C W : X.Etale} (a : TrfEtaleFrame G A) (b : TrfEtaleFrame G B)
    (c : TrfEtaleFrame G C) (f : W ⟶ A) (g : W ⟶ B) (h : W ⟶ C)
    (s : Γ(W.left, ⊤)) :
    trfEtaleFrameChange a b f g (trfEtaleFrameChange b c g h s) =
      trfEtaleFrameChange a c f h s := by
  unfold trfEtaleFrameChange
  rw [frame_inv_hom]

private noncomputable def frame_scalar_iso (Y : Scheme.{u}) (g : (Γ(Y, ⊤))ˣ) :
    SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf where
  hom := Modules.smulHom _ (g : Γ(Y, ⊤))
  inv := Modules.smulHom _ ((g⁻¹ : (Γ(Y, ⊤))ˣ) : Γ(Y, ⊤))
  hom_inv_id := by rw [← Modules.smulHom_mul]; simp
  inv_hom_id := by rw [← Modules.smulHom_mul]; simp

private lemma frame_scalar_apply (Y : Scheme.{u}) (g : (Γ(Y, ⊤))ˣ)
    (V : Y.Opens) (s : Γ(Y, V)) :
    (frame_scalar_iso Y g).hom.val.app (op V) s =
      s * Y.presheaf.map (homOfLE le_top).op (g : Γ(Y, ⊤)) := by
  change Y.presheaf.map (homOfLE le_top).op (g : Γ(Y, ⊤)) * s = _
  exact mul_comm _ _

private lemma frame_tensor_smul {Y Z : Scheme.{u}} (f : Y ⟶ Z) (c : Γ(Z, ⊤)) :
    (Modules.tensorPullback f).map (Modules.smulHom (SheafOfModules.unit Z.ringCatSheaf) c) ≫
        (trfFrameTensorUnit f).hom =
      (trfFrameTensorUnit f).hom ≫
        Modules.smulHom (SheafOfModules.unit Y.ringCatSheaf) (f.appTop c) := by
  let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction f)
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  have h : adj.homEquiv _ _ (trfFrameTensorUnit f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    (adj.homEquiv _ _).apply_symm_apply _
  rw [h, Modules.pushforward_map_smulHom]
  exact Modules.smulHom_naturality _ _

private lemma frame_pull_scalar {Y Z : Scheme.{u}} (f : Y ⟶ Z) (g : (Γ(Z, ⊤))ˣ) :
    trfFramePullUnit f (frame_scalar_iso Z g) =
      frame_scalar_iso Y (Units.map f.appTop.hom.toMonoidHom g) := by
  apply Iso.ext
  change (trfFrameTensorUnit f).inv ≫
    (Modules.tensorPullback f).map (Modules.smulHom _ (g : Γ(Z, ⊤))) ≫
      (trfFrameTensorUnit f).hom = _
  rw [frame_tensor_smul, Iso.inv_hom_id_assoc]
  rfl

private lemma frame_scalar_mul (Y : Scheme.{u}) (g h : (Γ(Y, ⊤))ˣ) :
    frame_scalar_iso Y h ≪≫ frame_scalar_iso Y g = frame_scalar_iso Y (g * h) := by
  apply Iso.ext
  exact (Modules.smulHom_mul _ _ _).symm

private lemma frame_scalar_one (Y : Scheme.{u}) :
    frame_scalar_iso Y 1 = Iso.refl (SheafOfModules.unit Y.ringCatSheaf) := by
  apply Iso.ext
  exact Modules.smulHom_one _

/-- Étale line frames determine unique units and ordinary descent isomorphisms.

Source: Stacks, Tag 03DX (2), overlap paragraph of the proof; Sheaves, Tag 0095
(blueprint: lem-trf-etale-line-frame-transition-units).

Proof:
1. Restrict each frame by precomposition. For a test object over an overlap both
   targets are the same module of sections of G. The two changes of frames are inverse.
   This uses `def-weil-pbc-etale-site` and `def-weil-sheaf-of-modules-category`.
2. Naturality at a test map q identifies the value at 1 with the pullback of the value
   at the identity of the overlap. Componentwise linearity gives f_q(b)=b q♯(f_id(1)).
   The same computation applies to the inverse change of frames.
3. Evaluate the two inverse identities at 1. Their values multiply to 1 in both
   orders, hence define a unit with the asserted inverse. Evaluation at identity and
   1 proves uniqueness of the unit, and therefore of the whole family.
4. On triple overlaps cancellation of the middle frame gives the cocycle; commute
   the two scalar factors. For the diagonal use naturality of the frame along the
   two maps id_U to the projections in the localized site over U. Both restrictions
   of G agree; injectivity of the frame gives diagonal pullback equal to 1. This
   does not assert g_aa=1 on the whole overlap.
5. The tensor formula of `def-pc-module-pullback` gives the unit map
   a tensor b ↦ a p♯(b), inverse a ↦ a tensor 1. Multiplication by the unit and its
   inverse gives an ordinary structure-module automorphism, and conjugation gives
   ordinary overlap maps with the required b-to-a orientation.
6. Pulling multiplication back along v sends a tensor b to a tensor (b g), hence,
   in unit coordinates, multiplies by v♯(g). The unit identifications respect
   composition, since both iterated tensor identifications multiply the same
   three factors. Thus the unit cocycle and diagonal equality give exactly the
   ordinary descent cocycle and normalization in these coordinates.
-/
theorem etale_line_frame_transition_units (X : Scheme.{u})
    (G : _root_.PresheafOfModules.{u}
      (X.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (_hG : Presheaf.IsSheaf X.smallEtaleTopology G.presheaf)
    (I : Type w) (U : I → X.Etale) (_hU : X.smallEtaleTopology.CoversTop U)
    (t : ∀ a, TrfEtaleFrame G (U a)) :
    ∃! g : ∀ a b, (Γ((Limits.prod (U a) (U b)).left, ⊤))ˣ,
      (∀ (a b : I) (W : X.Etale) (q : W ⟶ Limits.prod (U a) (U b))
        (s : Γ(W.left, ⊤)),
        trfEtaleFrameChange (t a) (t b) (q ≫ Limits.prod.fst) (q ≫ Limits.prod.snd) s =
          s * q.left.appTop (g a b : Γ((Limits.prod (U a) (U b)).left, ⊤))) ∧
      (∀ a b,
        (g a b : Γ((Limits.prod (U a) (U b)).left, ⊤)) =
          trfEtaleFrameChange (t a) (t b) Limits.prod.fst Limits.prod.snd 1 ∧
        ((g a b)⁻¹).val =
          trfEtaleFrameChange (t b) (t a) Limits.prod.snd Limits.prod.fst 1) ∧
      (∀ a b c,
        Units.map (Limits.prod.fst :
            Limits.prod (Limits.prod (U a) (U b)) (U c) ⟶ _).left.appTop.hom.toMonoidHom (g a b) *
          Units.map (Limits.prod.lift (Limits.prod.fst ≫ Limits.prod.snd) Limits.prod.snd :
            Limits.prod (Limits.prod (U a) (U b)) (U c) ⟶
              Limits.prod (U b) (U c)).left.appTop.hom.toMonoidHom (g b c) =
          Units.map (Limits.prod.lift (Limits.prod.fst ≫ Limits.prod.fst) Limits.prod.snd :
            Limits.prod (Limits.prod (U a) (U b)) (U c) ⟶
              Limits.prod (U a) (U c)).left.appTop.hom.toMonoidHom (g a c)) ∧
      (∀ a, Units.map
        (Limits.prod.lift (𝟙 (U a)) (𝟙 (U a))).left.appTop.hom.toMonoidHom (g a a) = 1) ∧
      ∃ φ : ∀ a b,
          (Modules.tensorPullback (Limits.prod.snd : Limits.prod (U a) (U b) ⟶ U b).left).obj
              (SheafOfModules.unit (U b).left.ringCatSheaf) ≅
            (Modules.tensorPullback (Limits.prod.fst : Limits.prod (U a) (U b) ⟶ U a).left).obj
              (SheafOfModules.unit (U a).left.ringCatSheaf),
        (∀ (a b : I) (V : (Limits.prod (U a) (U b)).left.Opens)
          (s : Γ((Limits.prod (U a) (U b)).left, V)),
          (trfFrameOverlapCoordinates (φ a b)).hom.val.app (op V) s = s *
            (Limits.prod (U a) (U b)).left.presheaf.map (homOfLE le_top).op
              (g a b : Γ((Limits.prod (U a) (U b)).left, ⊤))) ∧
        (∀ a b c,
          trfFramePullUnit (Limits.prod.lift
              (Limits.prod.fst ≫ Limits.prod.snd) Limits.prod.snd :
              Limits.prod (Limits.prod (U a) (U b)) (U c) ⟶
                Limits.prod (U b) (U c)).left (trfFrameOverlapCoordinates (φ b c)) ≪≫
            trfFramePullUnit (Limits.prod.fst :
              Limits.prod (Limits.prod (U a) (U b)) (U c) ⟶ _).left
                (trfFrameOverlapCoordinates (φ a b)) =
            trfFramePullUnit (Limits.prod.lift
              (Limits.prod.fst ≫ Limits.prod.fst) Limits.prod.snd :
              Limits.prod (Limits.prod (U a) (U b)) (U c) ⟶
                Limits.prod (U a) (U c)).left (trfFrameOverlapCoordinates (φ a c))) ∧
        (∀ a, trfFramePullUnit (Limits.prod.lift (𝟙 (U a)) (𝟙 (U a))).left
            (trfFrameOverlapCoordinates (φ a a)) =
          Iso.refl (SheafOfModules.unit (U a).left.ringCatSheaf)) := by
  let v (a b : I) : Γ((Limits.prod (U a) (U b)).left, ⊤) :=
    trfEtaleFrameChange (t a) (t b) Limits.prod.fst Limits.prod.snd 1
  let r (a b : I) : Γ((Limits.prod (U a) (U b)).left, ⊤) :=
    trfEtaleFrameChange (t b) (t a) Limits.prod.snd Limits.prod.fst 1
  have hv (a b : I) : r a b * v a b = 1 := by
    rw [← frame_change_mul]
    exact (frame_change_cancel (t a) (t b) (t a) _ _ _ 1).trans
      (frame_hom_inv (t a) _ 1)
  have hr (a b : I) : v a b * r a b = 1 := by
    rw [mul_comm]
    exact hv a b
  let g : ∀ a b, (Γ((Limits.prod (U a) (U b)).left, ⊤))ˣ :=
    fun a b ↦ ⟨v a b, r a b, hr a b, hv a b⟩
  have action (a b : I) (W : X.Etale) (q : W ⟶ Limits.prod (U a) (U b))
      (s : Γ(W.left, ⊤)) :
      trfEtaleFrameChange (t a) (t b) (q ≫ Limits.prod.fst) (q ≫ Limits.prod.snd) s =
        s * q.left.appTop (g a b : Γ((Limits.prod (U a) (U b)).left, ⊤)) := by
    rw [frame_change_mul]
    congr 1
    simpa only [map_one] using
      frame_change_naturality (t a) (t b) Limits.prod.fst Limits.prod.snd q 1
  have cocycle (a b c : I) :
      Units.map (Limits.prod.fst :
          Limits.prod (Limits.prod (U a) (U b)) (U c) ⟶ _).left.appTop.hom.toMonoidHom (g a b) *
        Units.map (Limits.prod.lift (Limits.prod.fst ≫ Limits.prod.snd) Limits.prod.snd :
          Limits.prod (Limits.prod (U a) (U b)) (U c) ⟶
            Limits.prod (U b) (U c)).left.appTop.hom.toMonoidHom (g b c) =
        Units.map (Limits.prod.lift (Limits.prod.fst ≫ Limits.prod.fst) Limits.prod.snd :
          Limits.prod (Limits.prod (U a) (U b)) (U c) ⟶
            Limits.prod (U a) (U c)).left.appTop.hom.toMonoidHom (g a c) := by
    apply Units.ext
    have hab := action a b (Limits.prod (Limits.prod (U a) (U b)) (U c)) Limits.prod.fst
    have hbc := action b c (Limits.prod (Limits.prod (U a) (U b)) (U c))
      (Limits.prod.lift (Limits.prod.fst ≫ Limits.prod.snd) Limits.prod.snd) 1
    have hac := action a c (Limits.prod (Limits.prod (U a) (U b)) (U c))
      (Limits.prod.lift (Limits.prod.fst ≫ Limits.prod.fst) Limits.prod.snd) 1
    simp only [Limits.prod.lift_fst, Limits.prod.lift_snd, one_mul] at hbc hac
    have hcomp := frame_change_cancel (t a) (t b) (t c)
      (Limits.prod.fst ≫ Limits.prod.fst) (Limits.prod.fst ≫ Limits.prod.snd)
      (Limits.prod.snd : Limits.prod (Limits.prod (U a) (U b)) (U c) ⟶ U c) 1
    rw [hab, hbc, hac] at hcomp
    exact (mul_comm _ _).trans hcomp
  have diagonal (a : I) : Units.map
      (Limits.prod.lift (𝟙 (U a)) (𝟙 (U a))).left.appTop.hom.toMonoidHom (g a a) = 1 := by
    apply Units.ext
    have h := action a a (U a) (Limits.prod.lift (𝟙 _) (𝟙 _)) 1
    simp only [Limits.prod.lift_fst, Limits.prod.lift_snd, one_mul] at h
    exact h.symm.trans (frame_hom_inv (t a) (𝟙 _) 1)
  refine ⟨g, ⟨action, (fun _ _ ↦ ⟨rfl, rfl⟩), cocycle, diagonal, ?_⟩, ?_⟩
  · let φ (a b : I) :=
      trfFrameTensorUnit (Limits.prod.snd : Limits.prod (U a) (U b) ⟶ U b).left ≪≫
        frame_scalar_iso _ (g a b) ≪≫
          (trfFrameTensorUnit (Limits.prod.fst : Limits.prod (U a) (U b) ⟶ U a).left).symm
    have coordinates (a b : I) :
        trfFrameOverlapCoordinates (φ a b) = frame_scalar_iso _ (g a b) := by
      ext : 1
      simp [φ, trfFrameOverlapCoordinates]
    refine ⟨φ, ?_, ?_, ?_⟩
    · intro a b V s
      rw [coordinates]
      exact frame_scalar_apply _ _ V s
    · intro a b c
      simp only [coordinates, frame_pull_scalar, frame_scalar_mul]
      rw [cocycle]
    · intro a
      rw [coordinates, frame_pull_scalar, diagonal, frame_scalar_one]
  · intro g' hg'
    funext a b
    apply Units.ext
    exact (hg'.2.1 a b).1

end AlgebraicGeometry.Scheme
