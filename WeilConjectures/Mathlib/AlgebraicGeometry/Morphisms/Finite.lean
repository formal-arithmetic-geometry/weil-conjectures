/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Group.Affine
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.Field

/-!
# Finite morphisms: finiteness over a field, and dimensions of local rings

A scheme `X` finite over a field `K` is affine, and its ring of global sections `Γ(X, ⊤)` is a
finite `K`-module, hence an artinian ring. Since the prime spectrum of an artinian ring is finite
and discrete, `X` is a finite discrete space, all of whose points are closed.

A finite morphism between integral schemes of finite type over a field which have the same
dimension preserves the dimension of the local rings. Locally the morphism is given by a finite
algebra `A → B` of finitely generated domains over the field, and the point upstairs and its image
correspond to a prime of `B` and its contraction to `A`; those two primes have the same height by
the dimension formula.

## Main results

- `AlgebraicGeometry.isAffine_of_isFinite_over_field`: a scheme finite over a field is affine.
- `AlgebraicGeometry.module_finite_presheafObj`: `Γ(X, ⊤)` is a finite `K`-module.
- `AlgebraicGeometry.finite_of_isFinite_over_field`,
  `AlgebraicGeometry.discreteTopology_of_isFinite_over_field`,
  `AlgebraicGeometry.isClosed_singleton_of_isFinite_over_field`: `X` is a finite discrete space
  of closed points.
- `AlgebraicGeometry.ringKrullDim_stalk_eq_of_isFinite`: for a finite morphism `f : X ⟶ Y`
  between integral schemes of finite type over a field with `dim X = dim Y`, the local rings
  `𝒪_{X,x}` and `𝒪_{Y,f x}` have the same Krull dimension.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- A scheme finite over a field is affine. -/
lemma isAffine_of_isFinite_over_field (f : X ⟶ Spec (.of K)) [IsFinite f] : IsAffine X :=
  isAffine_of_isAffineHom f

/-- The global sections of a scheme finite over `Spec K` form a finite `K`-module. -/
instance module_finite_presheafObj [X.Over (Spec (.of K))] [IsAffine X]
    [IsFinite (X ↘ Spec (.of K))] : Module.Finite K Γ(X, ⊤) := by
  rw [← RingHom.finite_algebraMap]
  have h : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite X.isoSpec.hom,
      isoSpec_hom_comp_specMap_algebraMap]
    infer_instance
  rwa [IsFinite.SpecMap_iff] at h

/-- The global sections of a scheme finite over a field form an artinian ring. -/
lemma isArtinianRing_presheafObj (K : Type u) [Field K] (X : Scheme.{u})
    [X.Over (Spec (.of K))] [IsAffine X] [IsFinite (X ↘ Spec (.of K))] :
    IsArtinianRing Γ(X, ⊤) :=
  isArtinian_of_tower K inferInstance

/-- A scheme finite over a field has finitely many points. -/
lemma finite_of_isFinite_over_field (f : X ⟶ Spec (.of K)) [IsFinite f] : Finite X := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  have : IsFinite (X ↘ Spec (.of K)) := ‹IsFinite f›
  have : IsAffine X := isAffine_of_isFinite_over_field f
  have := isArtinianRing_presheafObj K X
  have e : ↥X ≃ₜ PrimeSpectrum Γ(X, ⊤) := Scheme.homeoOfIso X.isoSpec
  exact .of_equiv _ e.toEquiv.symm

/-- A scheme finite over a field is a discrete space. -/
lemma discreteTopology_of_isFinite_over_field (f : X ⟶ Spec (.of K)) [IsFinite f] :
    DiscreteTopology X := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  have : IsFinite (X ↘ Spec (.of K)) := ‹IsFinite f›
  have : IsAffine X := isAffine_of_isFinite_over_field f
  have := isArtinianRing_presheafObj K X
  have e : ↥X ≃ₜ PrimeSpectrum Γ(X, ⊤) := Scheme.homeoOfIso X.isoSpec
  exact e.isEmbedding.discreteTopology

/-- Every point of a scheme finite over a field is closed. -/
lemma isClosed_singleton_of_isFinite_over_field (f : X ⟶ Spec (.of K)) [IsFinite f] (x : X) :
    IsClosed {x} :=
  have := discreteTopology_of_isFinite_over_field f
  isClosed_discrete _

/-- **A finite morphism between varieties of the same dimension preserves the dimension of the
local rings.**

Let `f : X ⟶ Y` be a finite morphism between integral schemes of finite type over a field `k`, and
suppose `X` and `Y` have the same dimension. Then `𝒪_{X,x}` and `𝒪_{Y,f x}` have the same Krull
dimension for every point `x` of `X`.

Surjectivity of `f` is not needed: it is automatic, the image of `f` being a closed irreducible
subset of `Y` of the same dimension as `Y`. -/
theorem ringKrullDim_stalk_eq_of_isFinite {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [IsFinite f] (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    (hdim : topologicalKrullDim X = topologicalKrullDim Y) (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) := by
  -- an affine open neighbourhood `V` of `f x`, whose preimage is affine since `f` is affine
  obtain ⟨V, hV, hxV⟩ : ∃ V : Y.Opens, IsAffineOpen V ∧ f x ∈ V :=
    ⟨(Y.affineCover.f (Y.affineCover.idx (f x))).opensRange, isAffineOpen_opensRange _,
      Y.affineCover.covers (f x)⟩
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have hxU : x ∈ f ⁻¹ᵁ V := hxV
  have : Nonempty V := ⟨⟨f x, hxV⟩⟩
  have : Nonempty (f ⁻¹ᵁ V) := ⟨⟨x, hxU⟩⟩
  -- the sections over `f ⁻¹ᵁ V` form a finite, hence integral, algebra over those over `V`
  let _ : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  have : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := IsFinite.finite_app f V hV
  have : Algebra.IsIntegral Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := Algebra.IsIntegral.of_finite _ _
  -- both are finitely generated domains over `k`, of the same dimension as the ambient scheme
  let _ := sY.sectionsAlgebra V
  let _ := sX.sectionsAlgebra (f ⁻¹ᵁ V)
  have : Algebra.FiniteType k Γ(Y, V) := sY.finiteType_sections hV
  have : Algebra.FiniteType k Γ(X, f ⁻¹ᵁ V) := sX.finiteType_sections hU
  have hAB : ringKrullDim Γ(Y, V) = ringKrullDim Γ(X, f ⁻¹ᵁ V) := by
    rw [hV.ringKrullDim_eq_topologicalKrullDim sY, hU.ringKrullDim_eq_topologicalKrullDim sX]
    exact hdim.symm
  -- the prime of `x` contracts to the prime of `f x`
  have hunder : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.under Γ(Y, V) =
      (hV.primeIdealOf ⟨f x, hxV⟩).asIdeal := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE (f := f) V hV (f ⁻¹ᵁ V) hU le_rfl hxU
    rw [← f.app_eq_appLE] at h
    exact congrArg PrimeSpectrum.asIdeal h
  -- so the two primes have the same height, by the dimension formula in each ring
  have hheight := Ideal.height_under_eq_of_ringKrullDim_eq k hAB (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  rw [hunder] at hheight
  -- and the height of the prime of a point of an affine open is the codimension of that point
  have hx : Order.coheight x = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.height := by
    rw [← hU.coheight_fromSpec (hU.primeIdealOf ⟨x, hxU⟩), hU.fromSpec_primeIdealOf]
  have hy : Order.coheight (f x) = (hV.primeIdealOf ⟨f x, hxV⟩).asIdeal.height := by
    rw [← hV.coheight_fromSpec (hV.primeIdealOf ⟨f x, hxV⟩), hV.fromSpec_primeIdealOf]
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx, hy, hheight]

end AlgebraicGeometry
