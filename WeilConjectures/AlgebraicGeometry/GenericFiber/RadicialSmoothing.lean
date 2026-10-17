/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import WeilConjectures.AlgebraicGeometry.GenericFiber.GenericSmoothness
public import WeilConjectures.AlgebraicGeometry.GenericFiber.PurelyInseparableModel
public import WeilConjectures.AlgebraicGeometry.GenericFiber.SpreadSmooth
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.ConstructibleSheaf.Pullback

/-!
# A smooth dense open after a finite radicial base change

Let `S` be integral of finite type over a field and `f : X ⟶ S` of finite type. After shrinking
`S` to a nonempty open `U` and making a finite, surjective, radicial base change `S' ⟶ U`, the
reduction of `X_{S'}` has a dense open `V` which is smooth over `S'`, and on which a given
constructible sheaf on `X` becomes finite locally constant. In characteristic zero no base
change is needed (generic smoothness); in characteristic `p` one passes to a finite purely
inseparable extension of the function field of `S`. This is the third step of Deligne's
generic constructibility theorem (`thm-fin-deligne-generic-open`).

## Main statements

- `AlgebraicGeometry.exists_isFinite_universallyInjective_smooth_dense`
  (`lem-fin-generic-radicial-smoothing`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

/-- The image of the restriction `f ∣_ V` is the preimage of the image of `f`. -/
lemma range_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) :
    Set.range (f ∣_ V) = V.ι ⁻¹' Set.range f := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(f ⁻¹ᵁ V).ι x, by rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι,
      Scheme.Hom.comp_apply]⟩
  · rintro ⟨x, hx⟩
    have hxV : x ∈ f ⁻¹ᵁ V := by
      change f x ∈ V
      rw [hx]
      exact y.2
    refine ⟨⟨x, hxV⟩, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    exact hx

/-- A cartesian square over `π ≫ U.ι` for an open `U ⊆ S` restricts to a cartesian square over
`f ∣_ U`. -/
lemma isPullback_morphismRestrict_lift {X S X' S' : Scheme.{u}} {f : X ⟶ S} {U : S.Opens}
    {π : S' ⟶ U.toScheme} {q₀ : X' ⟶ X} {f' : X' ⟶ S'} (H : IsPullback q₀ f' f (π ≫ U.ι)) :
    ∃ q : X' ⟶ (f ⁻¹ᵁ U).toScheme, IsPullback q f' (f ∣_ U) π := by
  have hr : Set.range q₀ ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f (q₀ x) ∈ U
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
    exact (π (f' x)).2
  refine ⟨IsOpenImmersion.lift (f ⁻¹ᵁ U).ι q₀ hr, IsPullback.of_right ?_ ?_
    (isPullback_morphismRestrict f U).flip⟩
  · rw [IsOpenImmersion.lift_fac]
    exact H
  · rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      IsOpenImmersion.lift_fac_assoc, H.w]

/-- If every point of a space is a specialization of a point of `s`, then `s` is dense. -/
lemma dense_of_forall_exists_specializes {X : Type*} [TopologicalSpace X] {s : Set X}
    (h : ∀ x, ∃ y ∈ s, y ⤳ x) : Dense s := fun x ↦ by
  obtain ⟨y, hy, hyx⟩ := h x
  exact closure_mono (Set.singleton_subset_iff.mpr hy) (specializes_iff_mem_closure.mp hyx)

/-- Blueprint `lem-fin-generic-radicial-smoothing`: A smooth dense open after a finite radicial
base change.

Let `S` be integral of finite type over a field `k` and let `f : X ⟶ S` be of finite type with
`X` nonempty. Then there are a nonempty open `U ⊆ S` and a finite, surjective, radicial
(universally injective) `π : S' ⟶ U`, with base change `f' : X' ⟶ S'` of `f` over `U`, and an
immersion `v : V ⟶ X'` from a reduced scheme, with open dense image (so that `V` is a dense open
of `(X')_red`), such that `V` is smooth over `S'`; `S'` is integral, being the spectrum of a
domain in the blueprint construction. For a given constructible sheaf `F` on `X`,
one may require the pullback of `F` to `V` to be finite locally constant.

Moreover, every point `x` of the generic fibre of `f'` outside `V` is a proper specialization of
a point of `V` in the generic fibre: in the generic fibre, the closure of `x` is a proper closed
subset of the irreducible closed subset of `X'` containing it, so that (the generic fibre being
of finite type over a field) every component of the complement of `V` in the generic fibre has
dimension strictly smaller than the component of `X'` containing it. -/
theorem exists_isFinite_universallyInjective_smooth_dense {k : Type u} [Field k]
    {S X : Scheme.{u}} [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] [Nonempty X]
    (Λ : Type (u + 1)) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] :
    ∃ (U : S.Opens) (S' : Scheme.{u}) (π : S' ⟶ U) (X' : Scheme.{u}) (q : X' ⟶ f ⁻¹ᵁ U)
      (f' : X' ⟶ S') (V : Scheme.{u}) (v : V ⟶ X'),
      (U : Set S).Nonempty ∧ IsIntegral S' ∧ IsFinite π ∧ Surjective π ∧ UniversallyInjective π ∧
      IsPullback q f' (f ∣_ U) π ∧ IsImmersion v ∧ IsReduced V ∧ IsOpen (Set.range v) ∧
      Dense (Set.range v) ∧ Smooth (v ≫ f') ∧
      IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (v ≫ q ≫ (f ⁻¹ᵁ U).ι)).obj F) ∧
      ∀ x : X', IsGenericPoint (f' x) Set.univ → x ∉ Set.range v →
        ∃ y ∈ Set.range v, IsGenericPoint (f' y) Set.univ ∧ y ⤳ x ∧ y ≠ x := by

  classical
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  -- generic smoothness on the generic fibre, after a purely inseparable extension
  set η := S.fromSpecFunctionField
  obtain ⟨L, _, _, _, _, YL, a, b, W, Z, z, hpb, hWd, hz₁, hz₂, hz₃⟩ :=
    exists_isPurelyInseparable_dense_isClosedImmersion_smooth S.functionField (pullback.snd f η)
  have hpb' := hpb.paste_horiz (IsPullback.of_hasPullback f η)
  -- a radicial model of `L` over a nonempty affine open of `S`
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hη, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint S)) isOpen_univ
  have : Nonempty U₀ := ⟨⟨_, hη⟩⟩
  have : IsNoetherianRing Γ(S, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  letI := TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨genericPoint S, hη⟩ : U₀)
  have := functionField_isFractionRing_of_isAffineOpen S U₀ hU₀
  obtain ⟨c, hc, B, _, _, _, _, _, hfin, huh, hcomp⟩ :=
    exists_finite_isUniversalHomeomorphism_isFractionRing Γ(S, U₀) S.functionField L
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing (Localization.Away c) B
  let j : Spec (.of (Localization.Away c)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U₀) _)) ≫ hU₀.fromSpec
  have : IsOpenImmersion j := by
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U₀)
        (Localization.Away c)))) := IsOpenImmersion.of_isLocalization c
    infer_instance
  let π₀ : Spec (.of B) ⟶ Spec (.of (Localization.Away c)) :=
    Spec.map (CommRingCat.ofHom (algebraMap _ B))
  have : IsFinite π₀ := by
    rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
    sorry
  have : IsUniversalHomeomorphism π₀ := huh.isUniversalHomeomorphism
  set σ := π₀ ≫ j
  have hσ : Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ σ =
      Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫ η := by
    rw [← hU₀.fromSpecStalk_eq_fromSpecStalk hη, IsAffineOpen.fromSpecStalk]
    simp only [σ, j, π₀, ← Spec.map_comp_assoc]
    congr 2
    ext r
    exact hcomp r
  -- spreading out
  obtain ⟨r, hr, V, v, O, hv₁, hv₂, hv₃, hO, hv₄⟩ :=
    exists_isImmersion_smooth_of_isFractionRing f σ (a ≫ pullback.fst f η) b
      (by rw [hσ]; exact hpb') W hWd z hz₃
  sorry

end AlgebraicGeometry
