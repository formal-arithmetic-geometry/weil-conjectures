/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q38, R2
-/
module

public import Sheaf.SixFunctors.TraceFormula.SchemeEtaleLineDefinitions
import Sheaf.AlgebraicGeometry.EtaleLineFrameTransitionUnits
import Sheaf.AlgebraicGeometry.EtaleFramedLineEffectiveGluing

/-! Auxiliary comparison for the canonical étale line-section functor. -/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme


private noncomputable def liftLinearIso {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R}
    (e : (SheafOfModules.toSheaf R).obj M ≅ (SheafOfModules.toSheaf R).obj N)
    (h : ∀ (U : Cᵒᵖ) (r : R.obj.obj U) (s : M.val.obj U),
      e.hom.hom.app U (r • s) = r • (@id (N.val.obj U) (e.hom.hom.app U s))) : M ≅ N := by
  apply (SheafOfModules.fullyFaithfulForget R).preimageIso
  refine PresheafOfModules.isoMk (fun U ↦ ModuleCat.isoMk
    (((sheafToPresheaf J AddCommGrpCat).mapIso e).app U) ?_) ?_
  · intro r
    ext s
    exact (h U r s).symm
  · intro U V f
    ext s
    exact ConcreteCategory.congr_hom (e.hom.hom.naturality f) s

/-- Essential surjectivity of a line-section functor with canonical scalar coordinates.
Source: Stacks Project, Descent, Tags 03DX (2), 023T and 05VG, rank one.
(blueprint: lem-trf-etale-line-sections-essentially-surjective).

Proof: for a line module G choose its covering family and invert its local
trivializations to obtain frames. Apply `lem-trf-etale-line-frame-transition-units`
to get overlap units. Linearity says that the second frame equals the first
multiplied by that unit; naturality pulls the triple-product and diagonal identities
to any test object. `lem-trf-etale-framed-line-effective-gluing` then gives an
ordinary invertible L and a scalar-linear additive-sheaf isomorphism from its tensor
sections to G. Compose this isomorphism with alpha for L. The scalar formula makes
the composite linear on every object, and naturality makes it a module-sheaf map.
Its inverse is linear by the inverse equation. Lift the resulting isomorphism to
the full subcategory of line modules. Empty schemes and arbitrary covers are included. -/
theorem etale_line_sections_essSurj {X : Scheme.{u}}
    (A : TrfInvertibleModules X ⥤ TrfEtaleLineModules X)
    (α : ∀ L : TrfInvertibleModules X,
      trfLineSections (A.obj L) ≅ trfInvertibleSections L)
    (hscalar : ∀ (L : TrfInvertibleModules X) (U : X.Etale)
      (r : Γ(U.left, ⊤)) (s : (A.obj L).obj.val.obj (op U)),
      (α L).hom.hom.app (op U) (r • s) =
        (((Modules.tensorPullback U.hom).obj L.obj).smul r).hom
          ((α L).hom.hom.app (op U) s)) :
    A.EssSurj := by
  classical
  refine ⟨fun G ↦ ?_⟩
  obtain ⟨I, U, hU, ht⟩ := G.property
  let t (a : I) : SheafOfModules.unit ((trfEtaleStructureRing X).over (U a)) ≅
      G.obj.over (U a) := (Classical.choice (ht a)).symm
  let tp (a : I) : TrfEtaleFrame G.obj.val (U a) :=
    (SheafOfModules.forget _).mapIso (t a)
  obtain ⟨g, ⟨hg, _, _, _, _⟩, _⟩ :=
    etale_line_frame_transition_units X G.obj.val G.obj.isSheaf I U hU tp
  have hcover : ∀ x : X, ∃ (a : I) (y : (U a).left), (U a).hom y = x := by
    intro x
    obtain ⟨V, f, ⟨a, ⟨k⟩⟩, y, hy⟩ :=
      (mem_smallEtaleTopology_iff _).mp (hU (Scheme.Etale.mk (𝟙 X))) x
    refine ⟨a, k.left y, ?_⟩
    have hf : f.left = V.hom := by
      exact (Category.comp_id (show V.left ⟶ X from f.left)).symm.trans f.w
    have hk := congrArg (fun q : V.left ⟶ X ↦ q y) k.w
    change (U a).hom (k.left y) = V.hom y at hk
    exact hk.trans ((congrArg (fun q : V.left ⟶ X ↦ q y) hf).symm.trans hy)
  have hchange (a b : I) (W : X.Etale) (f : W ⟶ U a) (h : W ⟶ U b)
      (r : Γ(W.left, ⊤)) :
      (t a).inv.val.app (op (Over.mk f)) ((t b).hom.val.app (op (Over.mk h)) r) =
        r * trfOverlapValue f h (g a b) := by
    have hx := hg a b W (Limits.prod.lift f h) r
    change (t a).inv.val.app (op (Over.mk (Limits.prod.lift f h ≫ Limits.prod.fst)))
      ((t b).hom.val.app (op (Over.mk (Limits.prod.lift f h ≫ Limits.prod.snd))) r) =
        r * trfOverlapValue f h (g a b) at hx
    erw [Limits.prod.lift_fst f h, Limits.prod.lift_snd f h] at hx
    exact hx
  have hinv (a : I) (W : X.Etale) (f : W ⟶ U a) (r : Γ(W.left, ⊤)) :
      (t a).inv.val.app (op (Over.mk f)) ((t a).hom.val.app (op (Over.mk f)) r) = r :=
    Iso.hom_inv_id_apply ((SheafOfModules.evaluation _ (op (Over.mk f))).mapIso (t a)) r
  have hframes (a b : I) (W : X.Etale) (f : W ⟶ U a) (h : W ⟶ U b)
      (r : Γ(W.left, ⊤)) :
      (t b).hom.val.app (op (Over.mk h)) r =
        (t a).hom.val.app (op (Over.mk f)) (trfOverlapValue f h (g a b) * r) := by
    apply (((SheafOfModules.evaluation _ (op (Over.mk f))).mapIso (t a)).symm
      |>.toLinearEquiv).injective
    change (t a).inv.val.app (op (Over.mk f)) _ =
      (t a).inv.val.app (op (Over.mk f)) _
    rw [hinv, hchange, mul_comm]
  have hcocycle (a b c : I) (W : X.Etale)
      (f : W ⟶ U a) (h : W ⟶ U b) (k : W ⟶ U c) :
      trfOverlapValue f h (g a b) * trfOverlapValue h k (g b c) =
        trfOverlapValue f k (g a c) := by
    apply (((SheafOfModules.evaluation _ (op (Over.mk f))).mapIso (t a))
      |>.toLinearEquiv).injective
    change (t a).hom.val.app (op (Over.mk f))
        (trfOverlapValue f h (g a b) * trfOverlapValue h k (g b c)) =
      (t a).hom.val.app (op (Over.mk f)) (trfOverlapValue f k (g a c))
    calc
      _ = (t b).hom.val.app (op (Over.mk h)) (trfOverlapValue h k (g b c)) :=
        (hframes a b W f h _).symm
      _ = (t c).hom.val.app (op (Over.mk k)) (1 : Γ(W.left, ⊤)) := by
        simpa only [mul_one] using (hframes b c W h k 1).symm
      _ = _ := by simpa only [mul_one] using hframes a c W f k 1
  have hdiag (a : I) : trfOverlapValue (𝟙 (U a)) (𝟙 (U a)) (g a a) = 1 := by
    have h := hchange a a (U a) (𝟙 _) (𝟙 _) 1
    rw [hinv, one_mul] at h
    exact h.symm
  obtain ⟨L, hL, lam, _, e, ⟨he, _⟩, _⟩ :=
    etale_framed_line_effective_gluing X G.obj U hcover t g hframes hcocycle hdiag
  let L' : TrfInvertibleModules X := ⟨L, hL⟩
  refine ⟨L', ⟨ObjectProperty.isoMk _ ?_⟩⟩
  apply liftLinearIso (α L' ≪≫ e)
  intro W r s
  change e.hom.hom.app W ((α L').hom.hom.app W (r • s)) =
    r • (@id (G.obj.val.obj W) (e.hom.hom.app W ((α L').hom.hom.app W s)))
  rw [hscalar L' W.unop]
  exact he W.unop r _

end AlgebraicGeometry.Scheme
