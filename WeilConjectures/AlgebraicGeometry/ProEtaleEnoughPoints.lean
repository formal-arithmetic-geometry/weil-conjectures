/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineSubsiteEquivalence
import WeilConjectures.CategoryTheory.Sites.FinitarySliceEnoughPoints

/-!
# Enough points of the small pro-étale topos

## References

* Stacks Project, Pro-étale Cohomology, Tag 0992.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

-- Use the direct sheaf colimits instead of searching through full-subcategory closure.
attribute [local instance 2000] Sheaf.instHasColimitsOfShape

set_option autoImplicit false

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem affine_closed_pullbacks (X : Scheme.{u}) :
    (Scheme.ProEt.affineSource X).IsClosedUnderLimitsOfShape WalkingCospan where
  limitsOfShape_le := by
    rintro P ⟨h⟩
    let F := h.diag
    let c : Cone F := ⟨P, h.π⟩
    let c' := (Cone.postcompose (diagramIsoCospan F).hom).obj c
    have hc' : IsLimit c' := (IsLimit.postcomposeHomEquiv _ c).symm h.isLimit
    have hp := (IsPullback.of_isLimit hc').map (Scheme.ProEt.forget X ⋙ Over.forget X)
    let G := Scheme.ProEt.forget X ⋙ Over.forget X
    have : IsAffine (G.obj (F.obj WalkingCospan.left)) := h.prop_diag_obj _
    have : IsAffine (G.obj (F.obj WalkingCospan.right)) := h.prop_diag_obj _
    have : IsAffine (G.obj (F.obj WalkingCospan.one)) := h.prop_diag_obj _
    exact IsAffine.of_isIso hp.isoPullback.hom

set_option backward.isDefEq.respectTransparency false in
private theorem affine_site (X : Scheme.{u})
    [HasPullbacks (Scheme.ProEt.AffineWeaklyEtale X)]
    [PreservesLimitsOfShape WalkingCospan (Scheme.ProEt.affineWeaklyEtaleInclusion X)] :
    (Scheme.ProEt.affineWeaklyEtalePrecoverage X).IsSiteForCoverings := by
  let F := Scheme.ProEt.affineWeaklyEtaleInclusion X
  have : (Scheme.ProEt.precoverage X).HasIsos := by
    dsimp [Scheme.ProEt.precoverage]; infer_instance
  have : (Scheme.ProEt.precoverage X).IsStableUnderComposition := by
    dsimp [Scheme.ProEt.precoverage]; infer_instance
  have : (Scheme.ProEt.precoverage X).IsStableUnderBaseChange := by
    dsimp [Scheme.ProEt.precoverage]; infer_instance
  let K := Pretopology.finite (Scheme.ProEt.AffineWeaklyEtale X) ⊓
    ((Scheme.ProEt.precoverage X).comap F).toPretopology
  have hK : K.toPrecoverage = Scheme.ProEt.affineWeaklyEtalePrecoverage X := rfl
  rw [← hK]
  refine ⟨⟨fun f _ ↦ K.has_isos f⟩, ?_, ?_⟩
  · intro T R S hR hS
    exact K.transitive R (fun _ f hf ↦ S f hf) hR (fun _ f hf ↦ hS _ f hf)
  · intro I T U a ha V b
    refine ⟨fun i ↦ pullback (a i) b, fun i ↦ pullback.snd _ _,
      fun i ↦ pullback.fst _ _, fun i ↦ (IsPullback.of_hasPullback _ _).flip, ?_⟩
    simpa only [Presieve.ofArrows_pullback] using K.pullbacks b _ ha

set_option backward.isDefEq.respectTransparency false in
private theorem affine_slice_finite (X : Scheme.{u})
    (T : Scheme.ProEt.AffineWeaklyEtale X)
    (Y : Over T) (A : Type (u + 1)) (V : A → Over T) (f : ∀ a, V a ⟶ Y)
    (hf : Presieve.ofArrows V f ∈
      ((Scheme.ProEt.affineWeaklyEtalePrecoverage X).comap (Over.forget T)) Y) :
    ∃ (K : Type (u + 1)) (_ : Finite K) (W : K → Over T)
      (g : ∀ k, W k ⟶ Y) (r : K → A),
      Presieve.ofArrows W g ∈
        ((Scheme.ProEt.affineWeaklyEtalePrecoverage X).comap (Over.forget T)) Y ∧
        ∀ k, ∃ (q : W k ⟶ V (r k)), q ≫ f (r k) = g k := by
  classical
  let R := Presieve.ofArrows (fun a ↦ (V a).left) (fun a ↦ (f a).left)
  have hR : R ∈ Scheme.ProEt.affineWeaklyEtalePrecoverage X Y.left := by
    simpa only [Precoverage.mem_comap_iff, Presieve.map_ofArrows,
      Over.forget_obj, Over.forget_map] using hf
  have hfin : R.uncurry.Finite := hR.1
  let K := R.uncurry
  have : Finite K := hfin.to_subtype
  let r : K → A := fun k ↦ k.2.idx
  let W : K → Over T := fun k ↦ V (r k)
  let g : ∀ k, W k ⟶ Y := fun k ↦ f (r k)
  refine ⟨K, inferInstance, W, g, r, ?_, fun k ↦ ⟨𝟙 _, by simp [g]⟩⟩
  simp only [Precoverage.mem_comap_iff, Presieve.map_ofArrows,
    Over.forget_obj, Over.forget_map]
  change Presieve.ofArrows _ (fun k : R.uncurry ↦ (f k.2.idx).left) ∈ _
  rwa [← Presieve.ofArrows_eq_ofArrows_uncurry]

set_option backward.isDefEq.respectTransparency false in
private theorem representables_cover
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    Epi (terminal.from (C := Sheaf J (Type (max (u + 1) v)))
      (∐ fun i : ULift.{max (u + 1) v} C ↦
        (presheafToSheaf J (Type (max (u + 1) v))).obj
          (uliftYoneda.{max (u + 1) v}.obj i.down))) := by
  constructor
  intro F a b hab
  apply (sheafToPresheaf J _).map_injective
  ext U x
  let R := uliftYoneda.{max (u + 1) v}.obj U.unop
  let H := (presheafToSheaf J (Type (max (u + 1) v))).obj R
  let adj := sheafificationAdjunction J (Type (max (u + 1) v))
  let k : H ⟶ ⊤_ (Sheaf J (Type (max (u + 1) v))) :=
    (adj.homEquiv R _).symm (uliftYonedaEquiv.symm x)
  have hk : k ≫ a = k ≫ b := by
    have h := congrArg (fun t ↦ Sigma.ι (fun i : ULift.{max (u + 1) v} C ↦
      (presheafToSheaf J (Type (max (u + 1) v))).obj
        (uliftYoneda.{max (u + 1) v}.obj i.down)) ⟨U.unop⟩ ≫ t) hab
    rw [show k = terminal.from H from terminalIsTerminal.hom_ext _ _]
    simpa only [← Category.assoc, terminal.comp_from] using h
  have h := congrArg (adj.homEquiv R F) hk
  have hka := adj.homEquiv_naturality_right k a
  have hkb := adj.homEquiv_naturality_right k b
  have hkk : adj.homEquiv R _ k = uliftYonedaEquiv.symm x :=
    Equiv.apply_symm_apply _ _
  rw [hka, hkb, hkk] at h
  have h' := congrArg uliftYonedaEquiv h
  simpa [uliftYonedaEquiv] using h'


/-- The small pro-étale topos of any scheme has a set-indexed conservative family
of points (Stacks, Tag 0992).

The site has objects in universe `u + 1` and morphisms in universe `u`; sheaves
and points take values in `Type (max (u + 1) v)`, allowing any compatible larger
universe. Points here are geometric morphisms, not ordinary geometric points
of the scheme. -/
theorem proEtale_enoughPoints (X : Scheme.{u}) :
    ∃ (ι : Type (max (u + 1) v))
      (p : ι → GeometricMorphism (Type (max (u + 1) v))
        (Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v)))),
      ∀ {F G : Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v))} (a : F ⟶ G),
        (∀ i, Function.Bijective ((p i).inverse.map a)) → IsIso a := by
  let := affine_closed_pullbacks X
  have : HasPullbacks (Scheme.ProEt.AffineWeaklyEtale X) := inferInstance
  have : PreservesLimitsOfShape WalkingCospan
      (Scheme.ProEt.affineWeaklyEtaleInclusion X) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (Scheme.ProEt.affineSource X).ι)
  let J := Scheme.ProEt.affineWeaklyEtalePrecoverage X
  let I := ULift.{max (u + 1) v} (Scheme.ProEt.AffineWeaklyEtale X)
  have hlimits (i : I) : HasFiniteLimits (Over i.down) := by
    have : HasTerminal (Over i.down) := Over.over_hasTerminal i.down
    exact hasFiniteLimits_of_hasTerminal_and_pullbacks
  obtain ⟨ι, p, hp⟩ := finitarySlice_enoughPoints.{u + 1, u, v}
    J (affine_site X) I (fun i ↦ i.down) (representables_cover J.toGrothendieck)
    hlimits (fun i ↦ affine_slice_finite X i.down)
  obtain ⟨e, _⟩ := Scheme.ProEt.affineWeaklyEtale_sheafEquivalence.{u, v} X
  let q : GeometricMorphism
      (Sheaf J.toGrothendieck (Type (max (u + 1) v)))
      (Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v))) :=
    { inverse := e.functor
      direct := e.inverse
      adj := e.toAdjunction
      leftExact := inferInstance }
  refine ⟨ι, fun i ↦ (p i).comp q, ?_⟩
  intro F G a ha
  have : IsIso (e.functor.map a) := hp (e.functor.map a) ha
  exact isIso_of_reflects_iso a e.functor

end AlgebraicGeometry
