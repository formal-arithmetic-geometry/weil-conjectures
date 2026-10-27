/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
import Sheaf.AlgebraicGeometry.BertiniFiniteCoverDimensionCut
import Sheaf.AlgebraicGeometry.FiniteFieldClosedSubschemeDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Curves through prescribed points preserving a finite étale cover

Let `X₀` be a smooth geometrically connected affine scheme of dimension `d ≥ 2` over a finite
field `k₀`, with geometric fiber `X = X₀ ×_{k₀} k̄`, let `T ⟶ X` be a connected finite étale
cover and `S` a nonempty finite set of `k̄`-points of `X`. A Bertini argument produces a smooth
connected closed affine curve `C ⊆ X` through `S` over which `T` stays connected; the curve is
defined over a finite extension of `k₀`, that is, it is stable under a power of the geometric
Galois Frobenius of `X`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_connectedSpace_pullback`: blueprint
  `lem-zl-bertini-finite-cover-curve`.

## Implementation notes

The blueprint lemma is stated over an arbitrary algebraically closed field `k`, with a
complement on descent when `k = 𝔽̄_q`. Only the case `k = 𝔽̄_q` is used, and it is stated here
directly for the geometric fiber of a scheme `X₀` over `𝔽_q`: "defined over a finite extension
`𝔽_{qᵐ}`" is rendered as stability of `C` under the `m`-th power of the geometric Galois Frobenius
`𝟙 × σ` of `X`, an automorphism `φ` of `C` with `φ ≫ i = i ≫ (𝟙 × σ)ᵐ`; by Galois descent, this
is the same as a model of `C ⟶ X` over `𝔽_{qᵐ}`. Dimensions are relative dimensions of smooth
morphisms.

## References

- [Stacks Project, Tags 0FD5, 0FD6 and 0G4F](https://stacks.math.columbia.edu/tag/0FD5), the
  Bertini theorems the proof uses.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

private theorem exists_curve_of_dimension_cut {k : Type u} [Field k] [IsAlgClosed k]
    (d : ℕ) (hd : 1 ≤ d) {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsAffine X] [ConnectedSpace X] [SmoothOfRelativeDimension d f]
    {T : Scheme.{u}} (π : T ⟶ X) [IsFinite π] [Etale π] [ConnectedSpace T]
    (S : Finset (Spec (.of k) ⟶ X)) (hS : S.Nonempty)
    (hS' : ∀ s ∈ S, s ≫ f = 𝟙 _) :
    ∃ (C : Scheme.{u}) (i : C ⟶ X), IsClosedImmersion i ∧ IsAffine C ∧
      SmoothOfRelativeDimension 1 (i ≫ f) ∧ ConnectedSpace C ∧
      (∀ s ∈ S, ∃ c, c ≫ i = s) ∧ ConnectedSpace ↑(pullback π i) := by
  classical
  induction d using Nat.strong_induction_on generalizing X T with
  | h d ih =>
    by_cases hdim : d = 1
    · subst d
      refine ⟨X, 𝟙 X, inferInstance, inferInstance, ?_, inferInstance, ?_, ?_⟩
      · simpa only [Category.id_comp] using
          (inferInstance : SmoothOfRelativeDimension 1 f)
      · intro s hs
        exact ⟨s, Category.comp_id _⟩
      · exact (asIso (pullback.fst π (𝟙 X))).hom.homeomorph.connectedSpace_iff.mpr
          inferInstance
    · have hd2 : 2 ≤ d := by omega
      obtain ⟨Y, j, hj, hY, hsm, hconn, hpoints, hcover⟩ :=
        AlgebraicGeometry.exists_smooth_finiteCover_dimension_cut f hd2 π S hS hS'
      have := hj
      have := hY
      have := hsm
      have := hconn
      have := hcover
      let t : S → (Spec (.of k) ⟶ Y) := fun s ↦ (hpoints s.val s.property).choose
      have ht (s : S) : t s ≫ j = s.val := (hpoints s.val s.property).choose_spec
      let R := S.attach.image t
      have hR : R.Nonempty := hS.attach.image t
      have hR' : ∀ r ∈ R, r ≫ (j ≫ f) = 𝟙 _ := by
        intro r hr
        obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hr
        rw [← Category.assoc, ht]
        exact hS' s.val s.property
      obtain ⟨C, i, hi, hC, hCsm, hCconn, hCpoints, hCcover⟩ :=
        ih (d - 1) (by omega) (by omega) (j ≫ f) (pullback.snd π j) R hR hR'
      have := hi
      refine ⟨C, i ≫ j, inferInstance, hC, ?_, hCconn, ?_, ?_⟩
      · simpa only [Category.assoc] using hCsm
      · intro s hs
        obtain ⟨c, hc⟩ := hCpoints (t ⟨s, hs⟩)
          (Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_attach _ _, rfl⟩)
        exact ⟨c, by rw [← Category.assoc, hc, ht]⟩
      · exact (pullbackLeftPullbackSndIso π j i).hom.homeomorph.connectedSpace_iff.mp
          hCcover

private theorem exists_frobenius_stable_closed_subscheme
    {k₀ : Type u} [Field k₀] [Finite k₀] {X₀ : Scheme.{u}}
    (f : X₀ ⟶ Spec (.of k₀)) [LocallyOfFiniteType f] [QuasiCompact f]
    (C : Scheme.{u}) (i : C ⟶ f.geometricFiber) [IsClosedImmersion i] :
    ∃ m : ℕ, 0 < m ∧ ∃ φ : C ≅ C,
      φ.hom ≫ i = i ≫ (f.geometricGaloisFrobenius ^ m).hom := by
  classical
  let _ := Fintype.ofFinite k₀
  obtain ⟨p, hp, a, hprime, hcard⟩ := FiniteField.card' k₀
  let D : WeilConjectures.FiniteFieldDatum.{u} :=
    { p := p
      a := a
      q := Fintype.card k₀
      prime := hprime
      exponent_pos := a.pos
      cardinality_eq := hcard
      k₀ := k₀
      card_base := Nat.card_eq_fintype_card
      k := AlgebraicClosure k₀ }
  have : LocallyOfFiniteType (Over.mk f).hom :=
    inferInstanceAs (LocallyOfFiniteType f)
  have : QuasiCompact (Over.mk f).hom := inferInstanceAs (QuasiCompact f)
  obtain ⟨m, hm, Cₘ, iₘ, _, _, φ, hφ⟩ :=
    D.exists_closed_subscheme_finiteField_descent (Over.mk f) C i
  have hF : D.geometricFrobenius (Over.mk f) = f.geometricGaloisFrobenius := by
    apply Iso.ext
    apply f.geometricFiber_hom_ext
    · rw [f.geometricGaloisFrobenius_hom_comp_geometricFiberProj]
      exact (D.galoisMap_projections f _).1
    · rw [f.geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure]
      exact (D.galoisMap_projections f _).2
  exact ⟨m, hm, φ, by simpa only [hF] using hφ⟩

/-- **Curves through prescribed points preserving a finite cover**
(blueprint: `lem-zl-bertini-finite-cover-curve`). Let `f : X₀ ⟶ Spec k₀` be a smooth
geometrically connected affine scheme of relative dimension `d ≥ 2` over a finite field, with
geometric fiber `X`, let `π : T ⟶ X` be a finite étale morphism with `T` connected, and let `S`
be a nonempty finite set of `k̄`-points of `X`. There is a closed immersion `i : C ⟶ X` of a
smooth connected affine curve over `k̄` through every point of `S`, such that `T ×_X C` is
connected and `C` is stable under some power `(𝟙 × σ)ᵐ`, `m ≥ 1`, of the geometric Galois
Frobenius of `X`. -/
theorem exists_isClosedImmersion_connectedSpace_pullback {k₀ : Type u} [Field k₀] [Finite k₀]
    {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k₀)) [IsAffine X₀] {d : ℕ} (hd : 2 ≤ d)
    [SmoothOfRelativeDimension d f] [GeometricallyConnected f] {T : Scheme.{u}}
    (π : T ⟶ f.geometricFiber) [IsFinite π] [Etale π] [ConnectedSpace T]
    (S : Finset (Spec (.of (AlgebraicClosure k₀)) ⟶ f.geometricFiber)) (hS : S.Nonempty)
    (hS' : ∀ s ∈ S, s ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _) :
    ∃ (C : Scheme.{u}) (i : C ⟶ f.geometricFiber), IsClosedImmersion i ∧ IsAffine C ∧
      SmoothOfRelativeDimension 1 (i ≫ f.geometricFiberToAlgebraicClosure) ∧
      ConnectedSpace C ∧ (∀ s ∈ S, ∃ c, c ≫ i = s) ∧ ConnectedSpace ↑(pullback π i) ∧
      ∃ m : ℕ, 0 < m ∧ ∃ φ : C ≅ C, φ.hom ≫ i = i ≫ (f.geometricGaloisFrobenius ^ m).hom := by
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : IsAffine f.geometricFiber :=
    isAffine_of_isAffineHom f.geometricFiberProj
  have : ConnectedSpace f.geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace
      (Scheme.specAlgebraicClosure k₀).hom f.geometricFiberProj
      f.geometricFiberToAlgebraicClosure (.of_hasPullback _ _)
  have : SmoothOfRelativeDimension d f.geometricFiberToAlgebraicClosure :=
    inferInstanceAs (SmoothOfRelativeDimension d
      (pullback.snd f (Scheme.specAlgebraicClosure k₀).hom))
  obtain ⟨C, i, hi, hC, hsm, hconn, hpoints, hcover⟩ :=
    exists_curve_of_dimension_cut d (by omega) f.geometricFiberToAlgebraicClosure π S hS hS'
  have := hi
  exact ⟨C, i, hi, hC, hsm, hconn, hpoints, hcover,
    exists_frobenius_stable_closed_subscheme f C i⟩

end AlgebraicGeometry.Scheme.Hom
