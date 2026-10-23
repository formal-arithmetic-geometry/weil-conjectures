/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineInputs
public import WeilConjectures.EtaleCohomology.Purity.Smooth.StrictlyHenselianBaseChange
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.CospecializationSections

/-!
# The cohomology of `𝔸¹` and `𝔾ₘ` over a strictly henselian local ring

Let `K` be a separably closed field and `Λ` a finite ring whose exponent is invertible in `K`.
Since `K` is strictly henselian, smooth base change along `Spec K̄ ⟶ Spec K` for an algebraic
closure `K̄` (`AlgebraicGeometry.Etale.nonempty_cohomology_constantComplex_iso_of_isPullback`)
identifies the cohomology of `𝔸¹_K` and of `𝔾_{m,K}` with that over `K̄`, computed in
`WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine`: `Hᵠ(𝔸¹_K, Λ)` is `Λ` for
`q = 0` and vanishes otherwise, `Hᵠ(𝔾_{m,K}, Λ)` is `Λ` for `q = 0, 1` and vanishes otherwise.
The same holds over every strictly henselian local ring `A` with a morphism
`Spec A ⟶ Spec K`, again by smooth base change. Over such a base the Tate twist `Λ(1)` is
trivial (`AlgebraicGeometry.Etale.nonempty_tateTwistObject_one_iso_constantComplex_of_isSepClosed`).

These are the computations of `sk-prop-a1-kummer` at a geometric point: the stalks of the direct
images of `Λ(1)` along `𝔸¹_B ⟶ B` and `𝔾_{m,B} ⟶ B` at a geometric point `s` of `B` are the
cohomology groups of `𝔸¹` and `𝔾ₘ` over the strict henselization of `B` at `s`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The projection of the affine line is smooth. -/
lemma smooth_affineLine_over (S : Scheme.{u}) : Smooth (𝔸(ULift.{u} (Fin 1); S) ↘ S) :=
  SmoothOfRelativeDimension.smooth (Nat.card (ULift.{u} (Fin 1))) _

attribute [local instance] smooth_affineLine_over

section BaseChange

variable {K : Type u} [Field K] [IsSepClosed K] [HasInvertibleExponent Λ (Spec (.of K))]
  {A : Type u} [CommRing A] [IsStrictlyHenselianLocalRing A] (g : Spec (.of A) ⟶ Spec (.of K))

include g

/-- The cohomology of `𝔸¹_A` is that of `𝔸¹_K`, for `A` strictly henselian over the separably
closed field `K`. -/
theorem nonempty_cohomology_affineLine_iso (q : ℤ) :
    Nonempty ((cohomology (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin 1); Spec (.of A)) q).obj
        (constantComplex Λ _) ≅
      (cohomology (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin 1); Spec (.of K)) q).obj
        (constantComplex Λ _)) :=
  nonempty_cohomology_constantComplex_iso_of_isPullback Λ g
    (𝔸(ULift.{u} (Fin 1); Spec (.of K)) ↘ Spec (.of K)) _ _ (AffineSpace.isPullback_map g).flip q

/-- The cohomology of the complement `G'` of the zero section of `𝔸¹_A` is that of the
complement `G` of the zero section of `𝔸¹_K`, for `A` strictly henselian over the separably
closed field `K`. -/
theorem nonempty_cohomology_complement_iso {G G' : Scheme.{u}}
    (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of K))) [IsOpenImmersion j]
    (hj : Set.range j.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of K))).base)ᶜ)
    (j' : G' ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of A))) [IsOpenImmersion j']
    (hj' : Set.range j'.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of A))).base)ᶜ) (q : ℤ) :
    Nonempty ((cohomology (ModuleCat.{u + 1} Λ) G' q).obj (constantComplex Λ G') ≅
      (cohomology (ModuleCat.{u + 1} Λ) G q).obj (constantComplex Λ G)) :=
  nonempty_cohomology_constantComplex_iso_of_isPullback Λ g
    (j ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of K)) ↘ Spec (.of K)) _ _
    (AffineSpace.isPullback_complementMap_over g j j' hj hj').flip q

end BaseChange

section SepClosed

variable {K : Type u} [Field K] [IsSepClosed K] [HasInvertibleExponent Λ (Spec (.of K))]

/-- The algebraic closure `Spec K̄ ⟶ Spec K` of a field, as a morphism of schemes. -/
noncomputable abbrev specAlgebraicClosure (K : Type u) [Field K] :
    Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))

/-- **The affine line over a separably closed field is acyclic**: `Hᵠ(𝔸¹_K, Λ) = 0` for
`q ≠ 0`. -/
theorem isZero_cohomology_affineLine_of_isSepClosed (q : ℤ) (hq : q ≠ 0) :
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin 1); Spec (.of K)) q).obj
      (constantComplex Λ _)) := by
  have : HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure K))) :=
    .of_hom (specAlgebraicClosure K)
  obtain ⟨e⟩ := nonempty_cohomology_affineLine_iso Λ (specAlgebraicClosure K) q
  exact (isZero_cohomology_affineLine Λ (k := AlgebraicClosure K) q hq).of_iso e.symm

/-- `H⁰(𝔸¹_K, Λ) ≅ Λ` over a separably closed field `K`. -/
theorem nonempty_iso_cohomology_zero_affineLine_of_isSepClosed :
    Nonempty ((cohomology (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin 1); Spec (.of K)) 0).obj
      (constantComplex Λ _) ≅ ModuleCat.of Λ Λ) := by
  have : HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure K))) :=
    .of_hom (specAlgebraicClosure K)
  obtain ⟨e⟩ := nonempty_cohomology_affineLine_iso Λ (specAlgebraicClosure K) 0
  exact ⟨e.symm ≪≫ (nonempty_iso_cohomology_zero_affineLine Λ (k := AlgebraicClosure K)).some⟩

variable {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of K))) [IsOpenImmersion j]
  (hj : Set.range j.base =
    (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of K))).base)ᶜ)

include hj in
/-- **`𝔾ₘ` over a separably closed field.** For the complement `G` of the zero section of
`𝔸¹_K`, `K` separably closed, `Hᵠ(G, Λ) = 0` for `q ∉ {0, 1}`. -/
theorem isZero_cohomology_multiplicativeGroup_of_isSepClosed (q : ℤ) (hq₀ : q ≠ 0)
    (hq₁ : q ≠ 1) :
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) G q).obj (constantComplex Λ G)) := by
  have : HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure K))) :=
    .of_hom (specAlgebraicClosure K)
  let g := specAlgebraicClosure K
  obtain ⟨e⟩ := nonempty_cohomology_complement_iso Λ g j hj
    (pullback.snd j (AffineSpace.map (ULift.{u} (Fin 1)) g))
    (AffineSpace.range_pullback_snd_map g j hj) q
  exact (isZero_cohomology_multiplicativeGroup Λ (k := AlgebraicClosure K) _
    (AffineSpace.range_pullback_snd_map g j hj) q hq₀ hq₁).of_iso e.symm

include hj in
/-- `H⁰(G, Λ) ≅ Λ` for the complement `G` of the zero section of `𝔸¹_K`, `K` separably
closed. -/
theorem nonempty_iso_cohomology_zero_multiplicativeGroup_of_isSepClosed :
    Nonempty ((cohomology (ModuleCat.{u + 1} Λ) G 0).obj (constantComplex Λ G) ≅
      ModuleCat.of Λ Λ) := by
  have : HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure K))) :=
    .of_hom (specAlgebraicClosure K)
  let g := specAlgebraicClosure K
  obtain ⟨e⟩ := nonempty_cohomology_complement_iso Λ g j hj
    (pullback.snd j (AffineSpace.map (ULift.{u} (Fin 1)) g))
    (AffineSpace.range_pullback_snd_map g j hj) 0
  exact ⟨e.symm ≪≫ (nonempty_iso_cohomology_zero_multiplicativeGroup Λ
    (k := AlgebraicClosure K) _ (AffineSpace.range_pullback_snd_map g j hj)).some⟩

include hj in
/-- `H¹(G, Λ) ≅ Λ` for the complement `G` of the zero section of `𝔸¹_K`, `K` separably
closed. -/
theorem nonempty_iso_cohomology_one_multiplicativeGroup_of_isSepClosed :
    Nonempty ((cohomology (ModuleCat.{u + 1} Λ) G 1).obj (constantComplex Λ G) ≅
      ModuleCat.of Λ Λ) := by
  have : HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure K))) :=
    .of_hom (specAlgebraicClosure K)
  let g := specAlgebraicClosure K
  let j' := pullback.snd j (AffineSpace.map (ULift.{u} (Fin 1)) g)
  have : HasInvertibleExponent Λ (pullback j (AffineSpace.map (ULift.{u} (Fin 1)) g)) :=
    .of_hom (j' ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of (AlgebraicClosure K))) ↘
      Spec (.of (AlgebraicClosure K)))
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); Spec (.of (AlgebraicClosure K))) :=
    .of_hom (𝔸(ULift.{u} (Fin 1); Spec (.of (AlgebraicClosure K))) ↘
      Spec (.of (AlgebraicClosure K)))
  obtain ⟨e⟩ := nonempty_cohomology_complement_iso Λ g j hj j'
    (AffineSpace.range_pullback_snd_map g j hj) 1
  exact ⟨e.symm ≪≫ (nonempty_iso_cohomology_one_multiplicativeGroup Λ
    (k := AlgebraicClosure K) j' (AffineSpace.range_pullback_snd_map g j hj)).some⟩

end SepClosed

section Twist

variable [NeZero (ringChar Λ)] {K : Type u} [Field K] [IsSepClosed K]

/-- Over a separably closed field, the Tate twist `Λ(1) = μₙ ⊗ Λ` is isomorphic to `Λ`: a
primitive `n`-th root of unity identifies `μₙ` with `ℤ/n`. -/
lemma nonempty_tateTwistObject_one_iso_constantComplex_of_isSepClosed {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ (Spec (.of K))] :
    Nonempty (tateTwistObject Λ X 1 ≅ constantComplex Λ X) := by
  have hN : ((ringChar Λ : ℕ) : K) ≠ 0 := by
    have h := (isUnit_ringChar_of_hasInvertibleExponent (Λ := Λ) (Spec (.of K))).map
      (Scheme.ΓSpecIso (.of K)).hom.hom
    rw [map_natCast] at h
    exact h.ne_zero
  have : NeZero ((ringChar Λ : ℕ) : K) := ⟨hN⟩
  obtain ⟨-, -, ζ, hζ, -⟩ := IsSepClosed.exists_isPrimitiveRoot.{u, u} K (ringChar Λ)
  let θ := X.constantZModIsoRootsOfUnitySheaf (ringChar Λ) f hζ
  exact ⟨tateTwistObjectOneIso X Λ ≪≫ (_root_.DerivedCategory.singleFunctor _ 0).mapIso
    ((extendScalars Λ X).mapIso θ.symm ≪≫
      extendScalarsConstantZModIso X ringChar.Nat.cast_ringChar) ≪≫
    (constantComplexIsoSingleFunctorConstantSheaf Λ X).symm⟩

end Twist

end Etale

end AlgebraicGeometry
