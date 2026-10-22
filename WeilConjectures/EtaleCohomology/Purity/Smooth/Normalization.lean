/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation
public import WeilConjectures.EtaleCohomology.Purity.Smooth.NormalizedTrace

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

- `AlgebraicGeometry.Etale.isIso_affineLineFundamentalClass_comp_smoothPurityTraceOfIso`: for every
  purity isomorphism, the trace of the fundamental class is invertible. It is the adjoint of the
  orientation, which is an isomorphism, and the counit of `R(s ≫ p)_! ⊣ R(s ≫ p)^!` is an
  isomorphism since `s ≫ p` is.
- `AlgebraicGeometry.Etale.pointFundamentalClassTrace_smoothPurityTrace_affineLine`: the canonical
  smooth trace sends the fundamental class of every `k`-point of `𝔸¹_k` to `1`.

## Implementation notes

The composition isomorphism `α : R(s ≫ p)_! ≅ Rs_! ⋙ Rp_!` and the identification
`ψ : Λ_k ≅ R(s ≫ p)_! Λ_{V(t)}` (the morphism `s ≫ p` is an isomorphism) are only known to
exist, so they are arguments of the invertibility statement, which holds for every purity map.
The normalization is stated for the canonical smooth trace
(`AlgebraicGeometry.Etale.smoothPurityTrace`), which is defined by the normalization on the
fundamental classes of `k`-points.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The affine line `𝔸¹_Y ⟶ Y` is smooth of relative dimension `1`. -/
instance smoothOfRelativeDimension_affineLine (Y : Scheme.{u}) :
    SmoothOfRelativeDimension 1 (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) := by
  have := AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin 1)) Y
  rwa [show Nat.card (ULift.{u} (Fin 1)) = 1 by simp] at this

/-- The exponent of `Λ` stays invertible on the affine line. -/
instance hasInvertibleExponent_affineLine (Λ : Type (u + 1)) [CommRing Λ] (Y : Scheme.{u})
    [HasInvertibleExponent Λ Y] : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); Y) :=
  .of_hom (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ] (Y : Scheme.{u})
  [HasInvertibleExponent Λ Y]
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

**The trace of the fundamental class is invertible.** For `Y` separated and locally
of finite type over a field and every purity isomorphism
`γ_{p,Λ} : Lp^* Λ(1)[2] ≅ Rp^! Λ` of the affine line `p : 𝔸¹_Y ⟶ Y`, the composite
`Tr^sm_{p,Λ} ∘ cl ∘ ψ : Λ_Y ⟶ Λ_Y` is an isomorphism. Writing `u = γ ∘ ι⁻¹ : Λ(1)[2] ≅ Rp^! Λ`,
the composite is the adjoint, for the composite adjunction `Rs_! ⋙ Rp_! ⊣ Rp^! ⋙ Rs^!`, of the
isomorphism `Rs^!(u) ∘ pur_s : Λ_{V(t)} ≅ Rs^! Rp^! Λ` (the orientation `pur_s` is an
isomorphism, `AlgebraicGeometry.Etale.isIso_affineLineOrientation`):

```
Λ_Y ──ψ──▶ R(s ≫ p)_! Λ ──α──▶ Rp_! Rs_! Λ ──Rp_! Rs_!(Rs^!(u) ∘ pur_s)──▶ Rp_! Rs_! Rs^! Rp^! Λ
                                                                                │ counit
                                                                                ▼
                                                                               Λ_Y
```

and the counit of the composite adjunction is an isomorphism because `s ≫ p : V(t) ⟶ Y` is an
isomorphism (`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekAdjunction_counit_of_isIso`),
through `α : R(s ≫ p)_! ≅ Rs_! ⋙ Rp_!`. -/
theorem isIso_affineLineFundamentalClass_comp_smoothPurityTraceOfIso [HasKummerClass.IsNormalized Λ]
    {k : Type u} [Field k] (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    (α : R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)} ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))_![ModuleCat.{u + 1} Λ] ≅
      R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)})_![ModuleCat.{u + 1} Λ] ⋙
        R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ])
    (ψ : constantComplex Λ Y ≅
      (R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)} ≫
          (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))_![ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ _))
    (γ : (twistShift Λ 𝔸(ULift.{u} (Fin 1); Y) ((1 : ℕ) : ℤ)).obj
        ((L((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj
          (constantComplex Λ Y)) ≅
      (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Y)) :
    IsIso (ψ.hom ≫ affineLineFundamentalClass Λ Y α ≫
      (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).map
        (affineLineTwistShiftIso Λ Y).inv ≫
      smoothPurityTraceOfIso Λ ((1 : ℕ) : ℤ) _ γ) := by
  have := isIso_affineLineOrientation Λ Y aY
  have : IsIso (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
      {AffineSpace.coord Y (ULift.up 0)} ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)) :=
    inferInstanceAs (IsIso (AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) Y
      (s := {AffineSpace.coord Y (ULift.up 0)}) Set.range_unique).inv)
  have hb := isIso_rightDerivedUpperShriekAdjunction_counit_of_isIso (ModuleCat.{u + 1} Λ)
    (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
      {AffineSpace.coord Y (ULift.up 0)} ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))
  set as := rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ)
    (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι {AffineSpace.coord Y (ULift.up 0)})
  set ap := rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ)
    (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)
  set b := rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ)
    (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
      {AffineSpace.coord Y (ULift.up 0)} ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))
  have : IsIso (as.comp ap).counit := (as.comp ap).isIso_counit_of_iso
    (Functor.isoWhiskerRight ((as.comp ap).rightAdjointUniq (b.ofNatIsoLeft α)) _ ≪≫
      Functor.isoWhiskerLeft _ α.symm ≪≫ asIso b.counit)
  have key : affineLineFundamentalClass Λ Y α ≫
      (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).map
        (affineLineTwistShiftIso Λ Y).inv ≫ smoothPurityTraceOfIso Λ ((1 : ℕ) : ℤ) _ γ =
      α.hom.app _ ≫ (R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)})_![ModuleCat.{u + 1} Λ] ⋙
          R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).map
        (affineLineOrientation Λ Y ≫ (R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
          {AffineSpace.coord Y (ULift.up 0)})^![ModuleCat.{u + 1} Λ]).map
            ((affineLineTwistShiftIso Λ Y).inv ≫ γ.hom)) ≫
        (as.comp ap).counit.app _ := by
    have h := congrArg (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).map
      (as.counit.naturality ((affineLineTwistShiftIso Λ Y).inv ≫ γ.hom))
    simp only [Functor.comp_map, Functor.id_map, Functor.map_comp, Category.assoc] at h
    simp only [affineLineFundamentalClass, smoothPurityTraceOfIso, Adjunction.comp_counit_app,
      Functor.comp_map, Functor.map_comp, Category.assoc, reassoc_of% h]
    rfl
  rw [key]
  infer_instance

/-- Blueprint `thm-pur-trace-normalization-transitivity`: Trace normalization and transitivity

**Normalization on the affine line.** Over a separably closed perfect field `k`, the canonical
smooth trace of the affine line `p : 𝔸¹_k ⟶ Spec k` (`AlgebraicGeometry.Etale.smoothPurityTrace`)
sends the fundamental class of every `k`-point of `𝔸¹_k` to `1`. Together with the transitivity
`AlgebraicGeometry.Etale.smoothPurityTraceOfIso_comp` this gives the normalization of `Tr^sm_{p_d}`
on the fundamental class of `𝔸^d` by induction on `d`. -/
theorem pointFundamentalClassTrace_smoothPurityTrace_affineLine {k : Type u} [Field k]
    [IsSepClosed k] [PerfectField k] [HasKummerClass.IsNormalized Λ]
    [HasInvertibleExponent Λ (Spec (.of k))]
    (x : Spec (.of k) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))
    (hx : x ≫ (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) = 𝟙 _)
    [IsRegularImmersion 1 x]
    (hZ : ∀ z : Spec (.of k), IsRegularLocalRing ((Spec (.of k)).presheaf.stalk z)) :
    pointFundamentalClassTrace Λ 1 (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))
      (smoothPurityTrace Λ 1 _) x hx hZ = 𝟙 _ :=
  pointFundamentalClassTrace_smoothPurityTrace Λ 1 _ x hx hZ

end Etale

end AlgebraicGeometry
