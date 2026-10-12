/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.ConstructibleSheaf.TorsorAssociatedModule
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# Gluing equivariant module sections

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-equivariant-module-is-sheaf)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.GaloisCover

private noncomputable abbrev functionPresheaf
    {V : Scheme.{u}} {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
    (M : Type (u + 1)) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] :
    V.Etaleᵒᵖ ⥤ Type (u + 1) :=
  (MorphismProperty.Over.pullback @Etale ⊤ c.π).op ⋙
    (Scheme.Etale.continuousMapSheaf c.P M).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}

private noncomputable def equivarianceSubfunctor
    {V : Scheme.{u}} (ℓ : ℕ) {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) (N : Rep.{u + 1} (ZMod ℓ) P)
    [TopologicalSpace N.V] [IsTopologicalAddGroup N.V] :
    Subfunctor (functionPresheaf c N.V) where
  obj W := {s : C(c.sectionSpace W.unop, N.V) | ∀ (g : P) (x : c.sectionSpace W.unop),
    s (c.sectionAction W.unop g x) = N.ρ g (s x)}
  map {W W'} f := by
    intro s₀ hs
    let s : C(c.sectionSpace W.unop, N.V) := s₀
    intro g x
    change s (c.sectionRestriction f.unop (c.sectionAction W'.unop g x)) =
      N.ρ g (s (c.sectionRestriction f.unop x))
    have h : c.sectionAction W'.unop g ≫ c.sectionRestriction f.unop =
        c.sectionRestriction f.unop ≫ c.sectionAction W.unop g := by
      apply pullback.hom_ext <;>
        simp [Scheme.GaloisCover.sectionAction, Scheme.GaloisCover.sectionRestriction]
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
    exact hs g _

/-- Equivariant locally constant module sections satisfy etale descent.
Source: Stacks Project, sites.tex Tags 04TR and 04TS; etale-cohomology.tex Tag 0DV5 (3).
(blueprint: lem-weil-pbc-torsor-equivariant-module-is-sheaf)

Proof: Let a matching family of equivariant sections be given on an etale cover
of an etale object W. Base change this cover along the torsor to obtain an etale
surjective cover of W times_V c.P. Etale maps are open, so matching locally
constant functions on this cover glue uniquely to a locally constant function:
define its value at a point using any lift, with independence given by matching
on the fibre products. Surjectivity of the maps from the fibre products to the
corresponding products of geometric fibres gives independence for arbitrary
scheme points too. Openness gives local constancy of the glued function.
Apply the same uniqueness to the pullback by each group action and the function
obtained by applying the representation action. They agree on the cover by
local equivariance, hence agree globally. Gluing is linear since addition and
scalar multiplication are pointwise. Thus every matching family in the module
presheaf has a unique amalgamation, proving the module-valued sheaf condition. -/
theorem equivariantModulePresheaf_isSheaf
    {V : Scheme.{u}} (ℓ : ℕ) {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
    (N : Rep.{u + 1} (ZMod ℓ) P) :
    Presheaf.IsSheaf V.smallEtaleTopology (c.equivariantModulePresheaf ℓ N) := by
  let : TopologicalSpace N.V := ⊥
  let : DiscreteTopology N.V := ⟨rfl⟩
  let Q := c.equivariantModulePresheaf ℓ N
  let G := equivarianceSubfunctor ℓ c N
  let e : Q ⋙ CategoryTheory.forget (ModuleCat.{u + 1} (ZMod ℓ)) ≅ G.toFunctor :=
    NatIso.ofComponents (fun W ↦ equivEquivIso
      { toFun := fun s ↦ ⟨s.val.toContinuousMap, s.property⟩
        invFun := fun t ↦
          let t₀ : C(c.sectionSpace W.unop, N.V) := t.val
          ⟨⟨t₀, (IsLocallyConstant.iff_continuous _).2 t₀.continuous⟩, t.property⟩
        left_inv := fun s ↦ by apply Subtype.ext; rfl
        right_inv := fun t ↦ by apply Subtype.ext; rfl }) (by
      intro W W' f
      ext s
      apply Subtype.ext
      apply ContinuousMap.ext
      intro y
      change s.val (c.sectionRestriction f.unop y) =
        s.val (((MorphismProperty.Over.pullback @Etale ⊤ c.π).map f.unop).left y)
      have hmap : c.sectionRestriction f.unop =
          ((MorphismProperty.Over.pullback @Etale ⊤ c.π).map f.unop).left := by
        apply pullback.hom_ext <;>
          simp [Scheme.GaloisCover.sectionRestriction, MorphismProperty.Over.pullback]
      rw [hmap]
      rfl)
  let : PreservesLimitsOfSize.{u, u + 1}
      (CategoryTheory.forget (ModuleCat.{u + 1} (ZMod ℓ))) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  let : HasLimitsOfSize.{u, u + 1}
      (ModuleCat.{u + 1} (ZMod ℓ)) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, 0}
  let : ReflectsLimitsOfSize.{u, u + 1}
      (CategoryTheory.forget (ModuleCat.{u + 1} (ZMod ℓ))) :=
    reflectsLimits_of_reflectsIsomorphisms
  apply Presheaf.isSheaf_of_isSheaf_comp _ Q
    (CategoryTheory.forget (ModuleCat.{u + 1} (ZMod ℓ)))
  rw [Presheaf.isSheaf_of_iso_iff e, isSheaf_iff_isSheaf_of_type]
  have hG : Presieve.IsSheaf V.smallEtaleTopology (equivarianceSubfunctor ℓ c N).toFunctor := by
    let H := functionPresheaf c N.V
    have hact : ∀ {W W' : V.Etale} (f : W ⟶ W') (g : P),
        c.sectionAction W g ≫ c.sectionRestriction f =
          c.sectionRestriction f ≫ c.sectionAction W' g := by
      intro W W' f g
      apply pullback.hom_ext <;>
        simp [Scheme.GaloisCover.sectionAction, Scheme.GaloisCover.sectionRestriction]
    have hH : Presieve.IsSheaf V.smallEtaleTopology H := by
      let : (MorphismProperty.Over.pullback @Etale ⊤ c.π).IsContinuous
          V.smallEtaleTopology c.P.smallEtaleTopology :=
        Etale.isContinuous_overPullback c.π
      rw [← isSheaf_iff_isSheaf_of_type]
      apply (MorphismProperty.Over.pullback @Etale ⊤ c.π).op_comp_isSheaf_of_isSheaf
        V.smallEtaleTopology c.P.smallEtaleTopology
      exact ((sheafCompose c.P.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        (Scheme.Etale.continuousMapSheaf c.P N.V)).property
    apply (Subfunctor.isSheaf_iff (equivarianceSubfunctor ℓ c N) hH).2
    intro W s₀ hs
    let s : C(c.sectionSpace W.unop, N.V) := s₀
    intro g x
    let a : H.obj W := s.comp ⟨c.sectionAction W.unop g,
      (c.sectionAction W.unop g).continuous⟩
    let b : H.obj W := ⟨fun y ↦ N.ρ g (s y),
      (continuous_of_discreteTopology).comp s.continuous⟩
    have hab : a = b := (hH.isSeparated _ hs).ext fun T f hf ↦ by
      apply ContinuousMap.ext
      intro y
      change s (c.sectionAction W.unop g (c.sectionRestriction f y)) =
        N.ρ g (s (c.sectionRestriction f y))
      rw [← Scheme.Hom.comp_apply, ← hact f g, Scheme.Hom.comp_apply]
      exact hf g y
    exact ContinuousMap.congr_fun hab x
  exact hG

end AlgebraicGeometry.Scheme.GaloisCover
