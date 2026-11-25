/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModule

/-!
# Equivariant locally constant sections are a sheaf

The presheaf of equivariant locally constant functions on a finite Galois torsor satisfies the
étale sheaf condition, without sheafification.

## Implementation details

The argument stays at the level of type-valued presheaves: equivariant sections form a
subfunctor of the sheaf of continuous (discrete-valued) functions on the pulled-back torsor,
and equivariance is checked locally. This avoids descent and connectedness assumptions.

## References

* [Stacks Project, Tags 04TR, 04TS and 0DV5 (3)]
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

private theorem restriction_action
    {V : Scheme.{u}} {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
    {W W' : V.Etale} (f : W ⟶ W') (g : P) :
    c.sectionAction W g ≫ c.sectionRestriction f =
      c.sectionRestriction f ≫ c.sectionAction W' g := by
  apply pullback.hom_ext <;> simp [Scheme.GaloisCover.sectionAction,
    Scheme.GaloisCover.sectionRestriction]

private noncomputable abbrev functionPresheaf
    {V : Scheme.{u}} {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
    (M : Type (u + 1)) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] :
    V.Etaleᵒᵖ ⥤ Type (u + 1) :=
  (MorphismProperty.Over.pullback @Etale ⊤ c.π).op ⋙
    (Scheme.Etale.continuousMapSheaf c.P M).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}

private theorem functionPresheaf_isSheaf
    {V : Scheme.{u}} {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
    (M : Type (u + 1)) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] :
    Presieve.IsSheaf V.smallEtaleTopology (functionPresheaf c M) := by
  let : (MorphismProperty.Over.pullback @Etale ⊤ c.π).IsContinuous
      V.smallEtaleTopology c.P.smallEtaleTopology :=
    Etale.isContinuous_overPullback c.π
  rw [← isSheaf_iff_isSheaf_of_type]
  apply (MorphismProperty.Over.pullback @Etale ⊤ c.π).op_comp_isSheaf_of_isSheaf
    V.smallEtaleTopology c.P.smallEtaleTopology
  exact ((sheafCompose c.P.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
    (Scheme.Etale.continuousMapSheaf c.P M)).property

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
    rw [← Scheme.Hom.comp_apply, restriction_action c,
      Scheme.Hom.comp_apply]
    exact hs g (c.sectionRestriction f.unop x)

private theorem equivarianceSubfunctor_isSheaf
    {V : Scheme.{u}} (ℓ : ℕ) {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) (N : Rep.{u + 1} (ZMod ℓ) P)
    [TopologicalSpace N.V] [DiscreteTopology N.V] :
    Presieve.IsSheaf V.smallEtaleTopology (equivarianceSubfunctor ℓ c N).toFunctor := by
  let H := functionPresheaf c N.V
  have hH : Presieve.IsSheaf V.smallEtaleTopology H :=
    functionPresheaf_isSheaf c N.V
  apply (Subfunctor.isSheaf_iff (equivarianceSubfunctor ℓ c N) hH).2
  intro W s₀ hs
  let s : C(c.sectionSpace W.unop, N.V) := s₀
  intro g x
  let a : H.obj W := s.comp ⟨c.sectionAction W.unop g,
    (c.sectionAction W.unop g).continuous⟩
  let b : H.obj W := ⟨fun y ↦ N.ρ g (s y), (continuous_of_discreteTopology).comp s.continuous⟩
  have hab : a = b := (hH.isSeparated _ hs).ext fun T f hf ↦ by
    apply ContinuousMap.ext
    intro y
    change s (c.sectionAction W.unop g (c.sectionRestriction f y)) =
      N.ρ g (s (c.sectionRestriction f y))
    rw [← Scheme.Hom.comp_apply, ← restriction_action c, Scheme.Hom.comp_apply]
    exact hf g y
  exact congrArg (fun t : C(c.sectionSpace W.unop, N.V) ↦ t x) hab

/-- Equivariant locally constant functions on a finite Galois torsor form an étale sheaf of
modules, after restricting scalars along `ULift.ringEquiv`. -/
theorem Scheme.GaloisCover.equivariantModulePresheaf_isSheaf
    {V : Scheme.{u}} (ℓ : ℕ) (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) (N : Rep.{u + 1} (ZMod ℓ) P) :
    Presheaf.IsSheaf V.smallEtaleTopology
      (c.equivariantModulePresheaf ℓ N ⋙ ModuleCat.restrictScalars
        (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ)) := by
  let : TopologicalSpace N.V := ⊥
  let : DiscreteTopology N.V := ⟨rfl⟩
  let Q := c.equivariantModulePresheaf ℓ N ⋙ ModuleCat.restrictScalars
    (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ)
  let G : Subfunctor (functionPresheaf c N.V) := equivarianceSubfunctor ℓ c N
  let e : Q ⋙ CategoryTheory.forget (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) ≅ G.toFunctor :=
    NatIso.ofComponents (fun W ↦ equivEquivIso
      { toFun := fun s ↦ ⟨s.val.toContinuousMap, s.property⟩
        invFun := fun t ↦
          let t₀ : C(c.sectionSpace W.unop, N.V) := t.val
          ⟨⟨t₀, (IsLocallyConstant.iff_continuous _).2 t₀.continuous⟩, t.property⟩
        left_inv := fun _ ↦ Subtype.ext rfl
        right_inv := fun _ ↦ Subtype.ext rfl }) (fun {_ _} _ ↦ rfl)
  let : HasLimitsOfSize.{u, u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
  let : ReflectsLimitsOfSize.{u, u + 1}
      (CategoryTheory.forget (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :=
    reflectsLimits_of_reflectsIsomorphisms
  apply Presheaf.isSheaf_of_isSheaf_comp _ Q
    (CategoryTheory.forget (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
  rw [Presheaf.isSheaf_of_iso_iff e, isSheaf_iff_isSheaf_of_type]
  exact equivarianceSubfunctor_isSheaf ℓ c N

end AlgebraicGeometry
