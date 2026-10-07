/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Dimension under quasi-finite morphisms

## Main statements

- `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_eq_of_surjective`: a universally closed,
  locally quasi-finite, surjective morphism of schemes (for instance a finite surjective one)
  preserves the dimension.
- `AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton_of_isFinite_morphismRestrict`: a
  morphism that is finite over an open `U` has finite fibres over the points of `U`.
- `AlgebraicGeometry.LocallyQuasiFinite.of_isPullback_of_surjective`: local quasi-finiteness of
  a quasi-compact morphism locally of finite type descends along surjective base changes.
- `AlgebraicGeometry.locallyQuasiFinite_of_etale`: an étale morphism is locally quasi-finite.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- An étale morphism is locally quasi-finite: on affine opens it is given by étale, hence
unramified and of finite type, ring maps, which are quasi-finite. -/
instance (priority := low) locallyQuasiFinite_of_etale (f : X ⟶ Y) [Etale f] :
    LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h := HasRingHomProperty.appLE @Etale f ‹_› U V e
  algebraize [(f.appLE U V e).hom]
  have : Algebra.Etale Γ(Y, U) Γ(X, V) := h
  change Algebra.QuasiFinite Γ(Y, U) Γ(X, V)
  infer_instance

/-- A locally quasi-finite morphism identifies no two distinct points `x ⤳ x'`: its fibres are
discrete. -/
lemma Scheme.Hom.eq_of_specializes_of_apply_eq (f : X ⟶ Y) [LocallyQuasiFinite f] {x x' : X}
    (h : x ⤳ x') (hx : f x = f x') : x = x' := by
  have : DiscreteTopology (f ⁻¹' {f x'}) := (f.isDiscrete_preimage_singleton (f x')).to_subtype
  have h' : (⟨x, hx⟩ : f ⁻¹' {f x'}) ⤳ ⟨x', rfl⟩ := IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val h'.eq

/-- **A universally closed, locally quasi-finite, surjective morphism preserves the dimension.**
Such a morphism `f : X ⟶ Y`, for instance a finite surjective one, satisfies `dim X = dim Y`:
chains of specializations in `Y` lift to `X` since `f` is closed (going up), and their images in
`Y` stay strict since the fibres of `f` are discrete (incomparability). -/
theorem Scheme.Hom.topologicalKrullDim_eq_of_surjective (f : X ⟶ Y) [UniversallyClosed f]
    [LocallyQuasiFinite f] [Surjective f] : topologicalKrullDim X = topologicalKrullDim Y :=
  le_antisymm
    (topologicalKrullDim_le_of_continuous f.continuous fun _ _ ↦ f.eq_of_specializes_of_apply_eq)
    (topologicalKrullDim_le_of_specializingMap f.isClosedMap.specializingMap f.surjective)

/-- If the restriction of `f` over an open `U` is finite, then the fibre of `f` over any point
of `U` is finite. -/
lemma Scheme.Hom.finite_preimage_singleton_of_isFinite_morphismRestrict (f : X ⟶ Y)
    {U : Y.Opens} [IsFinite (f ∣_ U)] {y : Y} (hy : y ∈ U) : (f ⁻¹' {y}).Finite := by
  refine (((f ∣_ U).finite_preimage_singleton ⟨y, hy⟩).image (f ⁻¹ᵁ U).ι).subset ?_
  intro x hx
  refine ⟨⟨x, by simp_all⟩, Subtype.ext ?_, rfl⟩
  simpa [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base] using hx

/-- **Quasi-finiteness descends along surjective base changes.** Let `f : X ⟶ Z` be quasi-compact
and locally of finite type, and let `snd : P ⟶ Y` be its base change along a surjective
`g : Y ⟶ Z`. If `snd` is locally quasi-finite, so is `f`: every fibre of `f` is the image of a
fibre of `snd`, which is finite. The hypothesis `QuasiCompact f` is only a convenience, used to
get finite fibres of `snd`; the statement also holds without it. -/
lemma LocallyQuasiFinite.of_isPullback_of_surjective {P Z : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) [Surjective g]
    [LocallyQuasiFinite snd] [QuasiCompact f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  have : QuasiCompact snd := MorphismProperty.of_isPullback h ‹_›
  refine .of_finite_preimage_singleton f fun z ↦ ?_
  obtain ⟨y, rfl⟩ := g.surjective z
  refine ((snd.finite_preimage_singleton y).image fst).subset fun x hx ↦ ?_
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y hx
  refine ⟨h.isoPullback.inv w, ?_, ?_⟩
  · simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, hw₂]
  · simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, hw₁]

end AlgebraicGeometry
