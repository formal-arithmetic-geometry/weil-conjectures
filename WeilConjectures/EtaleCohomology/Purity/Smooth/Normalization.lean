/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Trace

/-!
# Normalization of the smooth trace on the affine line

The fundamental class of the affine line `p : 𝔸¹_k ⟶ Spec k` is the image of the orientation
`pur_s : Λ_{V(t)} ⟶ Rs^! Λ(1)[2]` of its zero section
(`AlgebraicGeometry.Etale.affineLineOrientation`)
under `Rp_!` and the counit of `Rs_! ⊣ Rs^!`:

`cl : Λ ≅ R(s ≫ p)_! Λ ≅ Rp_! Rs_! Λ ⟶ Rp_! Rs_! Rs^! Λ(1)[2] ⟶ Rp_! Λ(1)[2]`.

The normalization of the smooth trace (blueprint `thm-pur-trace-normalization-transitivity`,
Step 2) is that `Tr^sm_p(cl) = 1`.

## Main definitions

- `AlgebraicGeometry.Etale.affineLineFundamentalClass`: the fundamental class `cl`.

## Main statements

- `AlgebraicGeometry.Etale.exists_affineLineFundamentalClass_comp_smoothTrace`: the trace of
  the fundamental class is `1`.

## Implementation notes

The composition isomorphism `α : R(s ≫ p)_! ≅ Rs_! ⋙ Rp_!` and the identification
`ψ : Λ_k ≅ R(s ≫ p)_! Λ_{V(t)}` (the morphism `s ≫ p` is an isomorphism) are only known to
exist, so they are arguments; the purity map of `p` is only known to exist as well, so the
normalization asserts that some purity map is normalized, which is the form in which it
determines the canonical one.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ] (Y : Scheme.{u})
  [HasCompactification (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
    {AffineSpace.coord Y (ULift.up 0)} ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))]

/-- The identification `Lp^* Λ_Y(1)[2] ≅ Λ_{𝔸¹}(1)[2]` of the source of the smooth trace of the
affine line with the shifted Tate twist. -/
noncomputable def affineLineTwistShiftIso :
    (twistShift Λ 𝔸(ULift.{u} (Fin 1); Y) ((1 : ℕ) : ℤ)).obj
        ((L((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ Y)) ≅
      (tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧ :=
  (twistShift Λ _ _).mapIso (leftDerivedUpperStarConstantComplexIso Λ _) ≪≫
    twistShiftConstantComplexIso Λ _ _ ≪≫ eqToIso (by norm_num)

/-- The fundamental class `cl : R(s ≫ p)_! Λ ⟶ Rp_! Λ(1)[2]` of the affine line, the image of
the orientation of the zero section `s` under `Rp_!` and the counit of `Rs_! ⊣ Rs^!`, read
through a composition isomorphism `α : R(s ≫ p)_! ≅ Rs_! ⋙ Rp_!`. -/
noncomputable def affineLineFundamentalClass
    (α : R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)} ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))_![ModuleCat.{u + 1} Λ] ≅
      R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)})_![ModuleCat.{u + 1} Λ] ⋙
        R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]) :
    (R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)} ≫
          (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))_![ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ _) ⟶
      (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧) :=
  α.hom.app _ ≫ (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).map
    ((R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)})_![ModuleCat.{u + 1} Λ]).map
        (affineLineOrientation Λ Y) ≫
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ)
        (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)})).counit.app
          ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧))

/-- Blueprint `thm-pur-trace-normalization-transitivity`: Trace normalization and transitivity

**The trace of the fundamental class is invertible.** Over a separably closed field, for every
purity isomorphism `γ_{p,Λ}` of the affine line, `Tr^sm_{p,Λ} ∘ cl ∘ ψ : Λ ⟶ Λ` is an
isomorphism: the counit `RΓ_c(𝔸¹, Rp^! Λ) ⟶ Λ` is an isomorphism and the fundamental class
generates `H²_c(𝔸¹, Λ(1)) ≅ Λ` (the adjoint form of affine-line purity,
`thm-pur-affine-line-purity`). -/
theorem isIso_affineLineFundamentalClass_comp_smoothTrace {k : Type u} [Field k]
    [IsSepClosed k] [HasKummerClass.IsNormalized Λ]
    [HasInvertibleExponent Λ (Spec (.of k))]
    [HasCompactification (𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
      {AffineSpace.coord (Spec (.of k)) (ULift.up 0)} ≫
        (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))]
    (α : R(𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of k)) (ULift.up 0)} ≫
          (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))_![ModuleCat.{u + 1} Λ] ≅
      R(𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of k)) (ULift.up 0)})_![ModuleCat.{u + 1} Λ] ⋙
        R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))_![ModuleCat.{u + 1} Λ])
    (ψ : constantComplex Λ (Spec (.of k)) ≅
      (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of k)) (ULift.up 0)} ≫
          (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))_![ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ _))
    (γ : (twistShift Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ((1 : ℕ) : ℤ)).obj
        ((L((𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^*[ModuleCat.{u + 1} Λ])).obj
          (constantComplex Λ (Spec (.of k)))) ≅
      (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^![ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ (Spec (.of k)))) :
    IsIso (ψ.hom ≫ affineLineFundamentalClass Λ (Spec (.of k)) α ≫
      (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))_![ModuleCat.{u + 1} Λ]).map
        (affineLineTwistShiftIso Λ (Spec (.of k))).inv ≫
      smoothTrace Λ ((1 : ℕ) : ℤ) _ γ) :=
  sorry

/-- Blueprint `thm-pur-trace-normalization-transitivity`: Trace normalization and transitivity

**Normalization on the affine line.** Over a separably closed field `k`, the smooth trace of
the affine line `p : 𝔸¹_k ⟶ Spec k` sends the fundamental class of `𝔸¹` to `1`: for every
composition isomorphism `α` and identification `ψ : Λ_k ≅ R(s ≫ p)_! Λ_{V(t)}` there is a
purity isomorphism `γ_{p,Λ} : Lp^* Λ(1)[2] ≅ Rp^! Λ` with `Tr^sm_{p,Λ} ∘ cl ∘ ψ = 1`. Together
with the transitivity `AlgebraicGeometry.Etale.smoothTrace_comp` this gives the normalization of
`Tr^sm_{p_d}` on the ordered fundamental class of `𝔸^d` by induction on `d`. -/
theorem exists_affineLineFundamentalClass_comp_smoothTrace {k : Type u} [Field k]
    [IsSepClosed k] [HasKummerClass.IsNormalized Λ]
    [HasInvertibleExponent Λ (Spec (.of k))]
    [HasCompactification (𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
      {AffineSpace.coord (Spec (.of k)) (ULift.up 0)} ≫
        (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))]
    (α : R(𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of k)) (ULift.up 0)} ≫
          (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))_![ModuleCat.{u + 1} Λ] ≅
      R(𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of k)) (ULift.up 0)})_![ModuleCat.{u + 1} Λ] ⋙
        R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))_![ModuleCat.{u + 1} Λ])
    (ψ : constantComplex Λ (Spec (.of k)) ≅
      (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of k)) (ULift.up 0)} ≫
          (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))_![ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ _)) :
    ∃ γ : (twistShift Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ((1 : ℕ) : ℤ)).obj
        ((L((𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^*[ModuleCat.{u + 1} Λ])).obj
          (constantComplex Λ (Spec (.of k)))) ≅
      (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^![ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ (Spec (.of k))),
      ψ.hom ≫ affineLineFundamentalClass Λ (Spec (.of k)) α ≫
        (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))_![ModuleCat.{u + 1} Λ]).map
          (affineLineTwistShiftIso Λ (Spec (.of k))).inv ≫
        smoothTrace Λ ((1 : ℕ) : ℤ) _ γ = 𝟙 _ := by
  have : SmoothOfRelativeDimension 1 (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) := by
    have := AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin 1)) (Spec (.of k))
    rwa [show Nat.card (ULift.{u} (Fin 1)) = 1 by simp] at this
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) :=
    .of_hom (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))
  obtain ⟨θ⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := 1)
    (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) (𝟙 _)
  let γ₀ : (twistShift Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ((1 : ℕ) : ℤ)).obj
        ((L((𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^*[ModuleCat.{u + 1} Λ])).obj
          (constantComplex Λ (Spec (.of k)))) ≅
      (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^![ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ (Spec (.of k))) :=
    (twistShift Λ _ _).mapIso
      (leftDerivedUpperStarConstantComplexIso Λ (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))
      ≪≫ θ.symm
  have hu := isIso_affineLineFundamentalClass_comp_smoothTrace Λ α ψ γ₀
  refine ⟨γ₀ ≪≫
    (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^![ModuleCat.{u + 1} Λ]).mapIso
      (asIso (ψ.hom ≫ affineLineFundamentalClass Λ (Spec (.of k)) α ≫
        (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))_![ModuleCat.{u + 1} Λ]).map
          (affineLineTwistShiftIso Λ (Spec (.of k))).inv ≫
          smoothTrace Λ ((1 : ℕ) : ℤ) _ γ₀)).symm, ?_⟩
  rw [smoothTrace, Iso.trans_hom, Functor.map_comp, Category.assoc, Functor.mapIso_hom,
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) _).counit_naturality]
  simp only [smoothTrace, Iso.symm_hom, asIso_inv] at hu ⊢
  simp only [← Category.assoc] at hu ⊢
  exact IsIso.hom_inv_id _

end Etale

end AlgebraicGeometry
