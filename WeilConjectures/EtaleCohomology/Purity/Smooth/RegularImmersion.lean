/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsOpenImmersion
public import WeilConjectures.SixFunctors.Integral.Exact
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekOpenRestriction
public import WeilConjectures.EtaleCohomology.Purity.Smooth.FrameIndependence
public import WeilConjectures.SixFunctors.Etale.Derived.HeartGluing

/-!
# Purity for regular closed immersions

Purity for a regular closed immersion is *not* one of the five moves of the proof of smooth
purity: it is a consequence of smooth purity applied to the two structure morphisms, together
with the co-projection formula for `Ri^!`. The deformation to the normal cone is never applied
to a general regular immersion.

The theorem is stated about the *fundamental class* `[Z ⊂ X] ∈ H^{2c}_Z(X, Λ(c))` of a
regular closed immersion `i : Z ⟶ X` of pure codimension `c`, which is *defined* by gluing
local classes. A *frame* of `Z` (`AlgebraicGeometry.Scheme.Hom.EtaleFrame`) is an étale
`e : U ⟶ X` with functions `f₁, …, f_c` on `U` generating the ideal of `Z ×_X U`; its class
is the cup product with supports `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c)` of the Kummer boundaries
(`AlgebraicGeometry.Etale.frameClass`), and `[Z ⊂ X]` is the unique global class restricting
to the frame class on every frame. Its adjoint is the morphism
`cl_i : Λ_Z ⟶ Ri^! (Λ_X(c)[2c])`, `1 ↦ [Z ⊂ X]`.

The statements about the fundamental class assume the rank-one datum with its normalisation,
`[HasKummerClass Λ] [HasKummerClass.IsNormalized Λ]`: without the normalisation the Kummer
classes, and with them the fundamental class, could be zero.

Classes with supports are morphisms `Λ_X ⟶ Ri_! Ri^! L`, with the supported term `Ri_!` of the
supported localization triangle; for the closed immersion `i` it is `Ri_*`. The coefficients
`Λ_X(c)[2c]` are placed inside `Ri^!`: the blueprint's `Ri^! Λ_X(c)[2c]` is
`Ri^! (Λ_X(c)[2c])`, which is `(Ri^! Λ_X)(c)[2c]` by the co-projection formula
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible`).

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.EtaleFrame`: a frame of a regular closed immersion.
- `AlgebraicGeometry.Etale.frameClass`: the class of a frame.
- `AlgebraicGeometry.Etale.fundamentalClass`: the fundamental class `[Z ⊂ X]`.
- `AlgebraicGeometry.Etale.fundamentalClassMap`: `cl_i : Λ_Z ⟶ Ri^! (Λ_X(c)[2c])`.

## Main statements

- `AlgebraicGeometry.Etale.isZero_homology_rightDerivedUpperShriek_of_isRegularImmersion`,
  `isLocallyConstantSheaf_homology_zero_rightDerivedUpperShriek_of_isRegularImmersion`,
  `exists_cover_nonempty_iso_homology_zero_rightDerivedUpperShriek_of_isRegularImmersion`:
  clause (a).
- `AlgebraicGeometry.Etale.existsUnique_fundamentalClass`,
  `AlgebraicGeometry.Etale.isIso_homology_zero_map_fundamentalClassMap`: clause (b).
- `AlgebraicGeometry.Etale.isIso_fundamentalClassMap`,
  `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_of_isRegularImmersion`: clause (c).
- `AlgebraicGeometry.Etale.restrictSupportedClass_fundamentalClass`,
  `AlgebraicGeometry.Etale.fundamentalClass_eq_cupWithSupportsTateObject`: clause (d).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory ZeroObject

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Scheme.Hom

variable {X Z : Scheme.{u}}

/-- A *frame* of a closed immersion `i : Z ⟶ X` of codimension `c`: an étale `e : U ⟶ X`
together with functions `f₁, …, f_c ∈ Γ(U, 𝒪_U)` generating the ideal of `Z_U = Z ×_X U`,
recorded as a pullback square

```
  V(f₁, …, f_c) ───toZ───▶ Z
        │                  │
  zeroLocusSubschemeι      │ i
        ▼                  ▼
        U ────────e──────▶ X
```

whose left side is the closed subscheme cut out by the `f_a`
(`AlgebraicGeometry.Scheme.zeroLocusSubschemeι`). Frames exist étale-locally (indeed
Zariski-locally) for a regular closed immersion. -/
structure EtaleFrame (c : ℕ) (i : Z ⟶ X) where
  /-- The source of the étale map. -/
  U : Scheme.{u}
  /-- The étale map `e : U ⟶ X`. -/
  e : U ⟶ X
  /-- `e` is étale. -/
  etale : AlgebraicGeometry.Etale e
  /-- The functions `f₁, …, f_c` on `U`. -/
  f : Fin c → Γ(U, ⊤)
  /-- The map from the closed subscheme `V(f₁, …, f_c)` to `Z`. -/
  toZ : U.zeroLocusSubscheme (Set.range f) ⟶ Z
  /-- `V(f₁, …, f_c)` is the base change `Z ×_X U`: the `f_a` generate the ideal of `Z_U`. -/
  isPullback : IsPullback toZ (U.zeroLocusSubschemeι (Set.range f)) i e

attribute [instance] EtaleFrame.etale

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

*Frames exist Zariski-locally.* Every point of `Z` lies in the zero locus of a frame of a regular
closed immersion `i : Z ⟶ X` of codimension `c` whose étale map is the inclusion of an affine
open `U ⊆ X`: the ideal of `Z` is generated on `U` by a regular sequence `f₁, …, f_c`. -/
theorem exists_etaleFrame_isOpenImmersion (c : ℕ) (i : Z ⟶ X)
    [IsRegularImmersion c i] (z : Z) :
    ∃ F : i.EtaleFrame c, IsOpenImmersion F.e ∧ z ∈ Set.range F.toZ ∧ IsAffine F.U ∧
      RingTheory.Sequence.IsWeaklyRegular Γ(F.U, ⊤) (List.ofFn F.f) := by
  obtain ⟨U, hzU, r, hr, hreg, hI⟩ :=
    IsRegularImmersion.exists_isWeaklyRegular_generators (c := c) (i := i) (i z)
  have : IsAffine U.1.toScheme := U.2
  let f : Fin c → Γ(U.1.toScheme, ⊤) := fun a ↦ U.1.topIso.inv (r.get (a.cast hr.symm))
  -- the sections `f` cut out `Z ∩ U`
  have hker : (i ∣_ U.1).ker = (U.1.toScheme.zeroLocusSubschemeι (Set.range f)).ker := by
    rw [IdealSheafData.ker_subschemeι]
    refine IdealSheafData.ext_of_isAffine ?_
    rw [IdealSheafData.ideal_top_ofIdealTop, ker_morphismRestrict_ideal,
      ← IdealSheafData.map_ideal' i.ker (U := ⟨_, _⟩) (V := U)
        (eqToHom U.1.ι_image_top).op, ← hI, Ideal.ofList, Ideal.map_span]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, f]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := List.mem_iff_get.mp hy
      exact ⟨a.cast hr, by simp [Scheme.Opens.topIso]; rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨r.get (a.cast hr.symm), List.get_mem _ _, by simp [Scheme.Opens.topIso]; rfl⟩
  let φ := IsClosedImmersion.lift (U.1.toScheme.zeroLocusSubschemeι (Set.range f)) (i ∣_ U.1)
    hker.ge
  have hφ : φ ≫ U.1.toScheme.zeroLocusSubschemeι (Set.range f) = i ∣_ U.1 :=
    IsClosedImmersion.lift_fac _ _ _
  have : IsIso φ := IsClosedImmersion.isIso_of_ker_eq _ _ φ hφ hker
  let F : i.EtaleFrame c :=
    { U := U.1.toScheme
      e := U.1.ι
      etale := inferInstance
      f := f
      toZ := inv φ ≫ (i ⁻¹ᵁ U.1).ι
      isPullback := by
        refine IsPullback.of_iso (isPullback_morphismRestrict i U.1).flip (asIso φ) (Iso.refl _)
          (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp [hφ] }
  have hreg' : RingTheory.Sequence.IsWeaklyRegular Γ(U.1.toScheme, ⊤) (List.ofFn f) := by
    have hf : List.ofFn f = r.map U.1.topIso.inv.hom := by
      refine List.ext_get (by simp [hr]) fun n h₁ h₂ ↦ ?_
      simp [f]
    rw [hf]
    exact hreg.map_of_flat (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso U.1.topIso.inv))
  refine ⟨F, inferInstanceAs (IsOpenImmersion U.1.ι), ⟨φ ⟨z, hzU⟩, ?_⟩, ‹_›, hreg'⟩
  change (inv φ ≫ (i ⁻¹ᵁ U.1).ι) (φ ⟨z, hzU⟩) = z
  rw [← Scheme.Hom.comp_apply, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rfl


/-- A frame of the base change `i'` of `i` along an étale `e` is a frame of `i`, through the
composite étale map. -/
@[simps]
noncomputable def EtaleFrame.ofIsPullback {c : ℕ} {i : Z ⟶ X} {X' Z' : Scheme.{u}} {i' : Z' ⟶ X'}
    {e : X' ⟶ X} [AlgebraicGeometry.Etale e] {g : Z' ⟶ Z} (hg : IsPullback g i' i e)
    (F : i'.EtaleFrame c) : i.EtaleFrame c where
  U := F.U
  e := F.e ≫ e
  etale := inferInstance
  f := F.f
  toZ := F.toZ ≫ g
  isPullback := F.isPullback.paste_horiz hg

/-- The frame of the closed subscheme `V(f₁, …, f_c) ⊂ U` cut out by functions on `U` given by an
étale `j : W ⟶ U` and the pulled back functions `j^* f_a`. -/
noncomputable def EtaleFrame.ofFunctions {c : ℕ} {U W : Scheme.{u}} (f : Fin c → Γ(U, ⊤))
    (j : W ⟶ U) [AlgebraicGeometry.Etale j] :
    (U.zeroLocusSubschemeι (Set.range f)).EtaleFrame c where
  U := W
  e := j
  etale := inferInstance
  f a := j.appTop (f a)
  toZ := (AlgebraicGeometry.Etale.exists_isPullback_zeroLocusSubschemeι j (Set.range f)
    (Set.range fun a ↦ j.appTop (f a)) (by rw [← Set.range_comp]; rfl)).choose
  isPullback := (AlgebraicGeometry.Etale.exists_isPullback_zeroLocusSubschemeι j (Set.range f)
    (Set.range fun a ↦ j.appTop (f a)) (by rw [← Set.range_comp]; rfl)).choose_spec
end Scheme.Hom

section

variable {X Z : Scheme.{u}}

/-- Two sets of functions on an affine scheme cutting out the same pullback of a closed
subscheme along a flat morphism generate the same ideal. -/
lemma Scheme.span_eq_of_isPullback_zeroLocusSubschemeι {Y : Scheme.{u}} [IsAffine Y]
    {i : Z ⟶ X} [IsClosedImmersion i] {φ : Y ⟶ X} [Flat φ] {s t : Set Γ(Y, ⊤)}
    {g₁ : Y.zeroLocusSubscheme s ⟶ Z}
    {g₂ : Y.zeroLocusSubscheme t ⟶ Z} (h₁ : IsPullback g₁ (Y.zeroLocusSubschemeι s) i φ)
    (h₂ : IsPullback g₂ (Y.zeroLocusSubschemeι t) i φ) :
    Ideal.span s = Ideal.span t := by
  have h := (Scheme.Hom.ker_of_isPullback i φ h₁).trans (Scheme.Hom.ker_of_isPullback i φ h₂).symm
  rw [IdealSheafData.ker_subschemeι, IdealSheafData.ker_subschemeι] at h
  rw [← IdealSheafData.ideal_top_ofIdealTop (Ideal.span s),
    ← IdealSheafData.ideal_top_ofIdealTop (Ideal.span t), h]

/-- An element which is a unit modulo the ideal generated by `s` is invertible near the zero
locus of `s`. -/
lemma Scheme.mem_basicOpen_of_isUnit_mk {Y : Scheme.{u}} {s : Set Γ(Y, ⊤)} {d : Γ(Y, ⊤)}
    (hd : IsUnit (Ideal.Quotient.mk (Ideal.span s) d)) {y : Y} (hy : y ∈ Y.zeroLocus s) :
    y ∈ Y.basicOpen d := by
  obtain ⟨u, hu⟩ := hd
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : Γ(Y, ⊤) ⧸ Ideal.span s)
  have hmem : d * b - 1 ∈ Ideal.span s := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, hb, ← hu]
    simp
  have hy' : y ∉ Y.basicOpen (d * b - 1) := by
    rw [← Y.zeroLocus_span, Scheme.mem_zeroLocus_iff] at hy
    exact hy _ hmem
  rw [Y.mem_basicOpen_top] at hy' ⊢
  by_contra hd'
  apply hy'
  have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
    (mem_nonunits_iff.mpr fun h ↦ hd' (isUnit_of_mul_isUnit_left h) :
      Y.presheaf.germ ⊤ y trivial d * Y.presheaf.germ ⊤ y trivial b ∈ nonunits _)
  rw [map_sub, map_mul, map_one]
  simpa [neg_sub] using this.neg

lemma _root_.CategoryTheory.IsPullback.exists_scheme_point {P A B C : Scheme.{u}} {fst : P ⟶ A}
    {snd : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C} (h : IsPullback fst snd f g) (a : A) (b : B)
    (hab : f a = g b) : ∃ p, fst p = a ∧ snd p = b := by
  obtain ⟨p, hp₁, hp₂⟩ := Scheme.Pullback.exists_preimage_pullback a b hab
  refine ⟨h.isoPullback.inv p, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hp₁]
  · rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hp₂]
end

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}}

section Purity

variable [Finite Λ]

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

**Purity for a regular closed immersion.** Let `i : Z ⟶ X` be a regular closed immersion of
pure codimension `c`, with `X` smooth of relative dimension `n` over a perfect field `k` and
`Z` regular — hence, by `AlgebraicGeometry.IsRegularImmersion.smooth_comp`, smooth of relative
dimension `m` where `m + c = n`. There is a canonical isomorphism

`Ri^! Λ_X ≅ Λ_Z(-c)[-2c]`,

the inverse of `cl_i(-c)[-2c]`, where `cl_i : Λ_Z ≅ Ri^! (Λ_X(c)[2c])`, `1 ↦ [Z ⊂ X]`, is
`AlgebraicGeometry.Etale.fundamentalClassMap` (an isomorphism by
`AlgebraicGeometry.Etale.isIso_fundamentalClassMap`); it is compatible with étale base change
and with exterior products (`AlgebraicGeometry.Etale.restrictSupportedClass_fundamentalClass`,
`AlgebraicGeometry.Etale.fundamentalClass_eq_cupWithSupportsTateObject`).

Smooth purity computes `ω_{a_X}` and `ω_{a_Z}`, and the co-projection formula lets one divide
the former into the latter. The relative dimension of `a_Z` is carried as `m` with
`hm : m + c = n` rather than as `n - c`: truncated subtraction would silently read `0` when
`c > n`. -/
theorem nonempty_iso_dualizingComplex_of_isRegularImmersion [HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k] [PerfectField k] (c n m : ℕ) (hm : m + c = n) (i : Z ⟶ X)
    [IsRegularImmersion c i] [HasCompactification i] (aX : X ⟶ Spec (.of k)) [IsSeparated aX]
    [SmoothOfRelativeDimension n aX] [HasCompactification aX]
    [SmoothOfRelativeDimension m (i ≫ aX)] [HasCompactification (i ≫ aX)]
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Z] :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) i ≅
      (twistShift Λ Z (-c : ℤ)).obj (constantComplex Λ Z)) := by
  -- Step 1: `ω_Z ≅ Ri^! ω_X`, `ω_X ≅ Λ_X(n)[2n]` and `ω_Z ≅ Λ_Z(m)[2m]`.
  obtain ⟨eComp⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ i aX
  obtain ⟨θX⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := n) aX (𝟙 (Spec (.of k)))
  obtain ⟨θZ⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := m) (i ≫ aX) (𝟙 (Spec (.of k)))
  -- Step 2: the co-projection with `K = Λ_X(0)` and the invertible `L = Λ_X(n)[2n]`.
  obtain ⟨cop⟩ := nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible Λ i
    (tateObject Λ X 0) ((tateObject Λ X n)⟦2 * (n : ℤ)⟧)
    (boundedConstructibleFiniteTor_tateObject Λ X 0)
    ((boundedConstructibleFiniteTor_tateObject Λ X n).shift _)
    ((isInvertible_tateObject Λ X n).shift _)
  let T : ℤ → _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    fun a ↦ (tateObject Λ Z a)⟦2 * a⟧
  let R := (R(i)^![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ X)
  let tens := derivedTensor (ModuleCat.{u + 1} Λ) Z
  -- `Ri^! Λ_X ⊗ Λ_Z(n)[2n] ≅ Λ_Z(m)[2m]`
  let E : (tens.obj R).obj (T n) ≅ T m :=
    ((tens.mapIso ((R(i)^![ModuleCat.{u + 1} Λ]).mapIso
        (HasTateTwist.twistObjectZeroIso (Λ := Λ) X).symm)).app _ ≪≫
      (tens.obj _).mapIso (leftDerivedUpperStarTateShiftIso Λ i n).symm ≪≫ cop.symm ≪≫
      (R(i)^![ModuleCat.{u + 1} Λ]).mapIso
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso
          (HasTateTwist.twistObjectZeroIso (Λ := Λ) X)).app _ ≪≫
          derivedTensorLeftUnitor _ X _ ≪≫ (twistShiftConstantComplexIso Λ X n).symm ≪≫
          θX.symm) ≪≫
      (eComp.app _).symm ≪≫ θZ ≪≫ twistShiftConstantComplexIso Λ Z m)
  -- cancel the invertible `Λ_Z(n)[2n]`
  have hmn : (m : ℤ) + -(n : ℤ) = -(c : ℤ) := by lia
  have h0 : (n : ℤ) + -(n : ℤ) = 0 := by lia
  exact ⟨(derivedTensorRightUnitor _ Z R).symm ≪≫
    (tens.obj R).mapIso ((HasTateTwist.twistObjectZeroIso (Λ := Λ) Z).symm ≪≫
      (shiftFunctorZero' _ (2 * ((n : ℤ) + -(n : ℤ))) (by lia)).symm.app _ ≪≫
      eqToIso (by rw [h0]; rfl) ≪≫ (shiftTateObjectAddIso Λ Z n (-(n : ℤ))).symm) ≪≫
    (derivedTensorAssociator _ Z _ _ _).symm ≪≫ (tens.mapIso E).app _ ≪≫
    shiftTateObjectAddIso Λ Z m (-(n : ℤ)) ≪≫ eqToIso (by rw [hmn]) ≪≫
    (twistShiftConstantComplexIso Λ Z _).symm⟩

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

The twisted form of purity, `Ri^! (Λ_X(c)[2c]) ≅ Λ_Z`: the co-projection formula moves the
invertible twist out of `Ri^!`, and `Ri^! Λ_X ≅ Λ_Z(-c)[-2c]`
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_of_isRegularImmersion`). -/
theorem nonempty_iso_rightDerivedUpperShriek_shiftTateObject_of_isRegularImmersion
    [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k] [PerfectField k] (c n m : ℕ) (hm : m + c = n) (i : Z ⟶ X)
    [IsRegularImmersion c i] [HasCompactification i] (aX : X ⟶ Spec (.of k)) [IsSeparated aX]
    [SmoothOfRelativeDimension n aX] [HasCompactification aX]
    [SmoothOfRelativeDimension m (i ≫ aX)] [HasCompactification (i ≫ aX)]
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Z] :
    Nonempty ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧) ≅
      constantComplex Λ Z) := by
  obtain ⟨θ⟩ := nonempty_iso_dualizingComplex_of_isRegularImmersion Λ c n m hm i aX
  obtain ⟨cop⟩ := nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible Λ i
    (tateObject Λ X 0) ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)
    (boundedConstructibleFiniteTor_tateObject Λ X 0)
    ((boundedConstructibleFiniteTor_tateObject Λ X c).shift _)
    ((isInvertible_tateObject Λ X c).shift _)
  let tens := derivedTensor (ModuleCat.{u + 1} Λ) Z
  have h0 : -(c : ℤ) + (c : ℤ) = 0 := by lia
  exact ⟨(R(i)^![ModuleCat.{u + 1} Λ]).mapIso
      ((((derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso
          (HasTateTwist.twistObjectZeroIso (Λ := Λ) X)).app _ ≪≫
        derivedTensorLeftUnitor _ X _).symm) ≪≫ cop ≪≫
    (tens.mapIso ((R(i)^![ModuleCat.{u + 1} Λ]).mapIso
        (HasTateTwist.twistObjectZeroIso (Λ := Λ) X) ≪≫ θ ≪≫
          twistShiftConstantComplexIso Λ Z _)).app _ ≪≫
    (tens.obj _).mapIso (leftDerivedUpperStarTateShiftIso Λ i c) ≪≫
    shiftTateObjectAddIso Λ Z (-(c : ℤ)) c ≪≫ eqToIso (by rw [h0]; rfl) ≪≫
    (shiftFunctorZero' _ (2 * (0 : ℤ)) (by lia)).app _ ≪≫
    HasTateTwist.twistObjectZeroIso (Λ := Λ) Z⟩

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

*The local form of purity.* Let `i : Z ⟶ X` be a regular closed immersion of pure codimension
`c`, with `X` smooth over a perfect field `k` and `Z` regular. Every point of `Z` has an affine
open neighbourhood `W` in `X` such that the restriction of `Ri^! (Λ_X(c)[2c])` to `Z ∩ W` is the
constant complex: on `W` the structure morphisms of `W` and of `Z ∩ W` have constant relative
dimensions `n` and `m` with `m + c = n`
(`AlgebraicGeometry.IsRegularImmersion.exists_isAffineOpen_smoothOfRelativeDimension`) and admit
compactifications, so the twisted form of purity applies to `i ∣_ W`, and `Ri^!` commutes with
the restriction to `W`. -/
theorem exists_nonempty_iso_upperStar_rightDerivedUpperShriek_of_isRegularImmersion
    [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ] [HasInvertibleExponent Λ X]
    {k : Type u} [Field k] [PerfectField k] (c : ℕ) (i : Z ⟶ X) [IsRegularImmersion c i]
    (aX : X ⟶ Spec (.of k)) [Smooth aX] (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z))
    (z : Z) :
    ∃ (W : X.Opens) (_ : i.base z ∈ W),
      Nonempty ((((i ⁻¹ᵁ W).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj
          ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) ≅
        constantComplex Λ (i ⁻¹ᵁ W)) := by
  obtain ⟨W, hW, hzW, n, m, hmn, hn, hm⟩ :=
    IsRegularImmersion.exists_isAffineOpen_smoothOfRelativeDimension c i aX hZ z
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ aX)
  obtain ⟨e₁⟩ := nonempty_iso_mapDerivedCategory_upperStar_rightDerivedUpperShriek Λ i W
    ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)
  have : IsAffine W := hW
  have : IsAffine (i ⁻¹ᵁ W) := (hW.preimage i : IsAffineOpen (i ⁻¹ᵁ W))
  have : IsRegularImmersion c (i ∣_ W) :=
    IsRegularImmersion.of_isPullback c (isPullback_morphismRestrict i W).flip
  have : HasCompactification (W.ι ≫ aX) := HasCompactification.of_isQuasiAffine _
  have hcomp : (i ∣_ W) ≫ W.ι ≫ aX = (i ⁻¹ᵁ W).ι ≫ i ≫ aX := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  have : SmoothOfRelativeDimension m ((i ∣_ W) ≫ W.ι ≫ aX) := hcomp ▸ hm
  have : HasCompactification ((i ∣_ W) ≫ W.ι ≫ aX) := HasCompactification.of_isQuasiAffine _
  have : HasInvertibleExponent Λ W := .of_hom W.ι
  have : HasInvertibleExponent Λ (i ⁻¹ᵁ W) := .of_hom ((i ⁻¹ᵁ W).ι ≫ i)
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_shiftTateObject_of_isRegularImmersion Λ c n
    m hmn (i ∣_ W) (W.ι ≫ aX)
  exact ⟨W, hzW, ⟨e₁ ≪≫ (R(i ∣_ W)^![ModuleCat.{u + 1} Λ]).mapIso
    ((leftDerivedUpperStarIsoMapDerivedCategory _ W.ι).symm.app _ ≪≫
      leftDerivedUpperStarTateShiftIso Λ W.ι c) ≪≫ e₂⟩⟩

end Purity

section FundamentalClass

variable [Finite Λ] {c : ℕ} {i : Z ⟶ X}

/-- The *class of a frame* `(e : U ⟶ X, f₁, …, f_c)` of `Z`:

`cl(f) = ∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c) ∈ H^{2c}_{Z_U}(U, Λ(c)) = Hom(Λ_U, Ri_{U!} Ri_U^! (Λ_U(c)[2c]))`,

the iterated cup product with supports of the Kummer boundaries
(`AlgebraicGeometry.Etale.kummerBoundaryProduct`), supported on
`V(f₁) ∩ ⋯ ∩ V(f_c) = Z_U`. -/
noncomputable def frameClass [HasKummerClass Λ] (F : i.EtaleFrame c) :
    constantComplex Λ F.U ⟶
      (R(F.U.zeroLocusSubschemeι (Set.range F.f))_![ModuleCat.{u + 1} Λ]).obj
        ((R(F.U.zeroLocusSubschemeι (Set.range F.f))^![ModuleCat.{u + 1} Λ]).obj
          ((tateObject Λ F.U c)⟦2 * (c : ℤ)⟧)) :=
  kummerBoundaryProduct Λ F.f

/-- The restriction of a class `γ ∈ H^{2c}_Z(X, Λ(c))` to a frame `(e : U ⟶ X, f)`, a class in
`H^{2c}_{Z_U}(U, Λ(c))`: the restriction of supports along the étale `e`
(`AlgebraicGeometry.Etale.restrictSupportedClass`), with `Λ_U ≅ Le^* Λ_X` and
`Le^* (Λ_X(c)[2c]) ≅ Λ_U(c)[2c]`. -/
noncomputable def frameRestriction [HasTateTwist Λ] [IsClosedImmersion i] (F : i.EtaleFrame c)
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))) :
    constantComplex Λ F.U ⟶
      (R(F.U.zeroLocusSubschemeι (Set.range F.f))_![ModuleCat.{u + 1} Λ]).obj
        ((R(F.U.zeroLocusSubschemeι (Set.range F.f))^![ModuleCat.{u + 1} Λ]).obj
          ((tateObject Λ F.U c)⟦2 * (c : ℤ)⟧)) :=
  restrictSupportedClass (ModuleCat.{u + 1} Λ) F.e i _ F.toZ F.isPullback
    (leftDerivedUpperStarConstantComplexIso Λ F.e).inv (leftDerivedUpperStarTateShiftIso Λ F.e c) γ

/-- A frame class restricts to the frame class of the pulled back functions. -/
lemma frameRestriction_kummerBoundaryProduct [HasKummerClass Λ] {U W : Scheme.{u}}
    [HasInvertibleExponent Λ U] (f : Fin c → Γ(U, ⊤)) (j : W ⟶ U) [AlgebraicGeometry.Etale j] :
    frameRestriction Λ (Scheme.Hom.EtaleFrame.ofFunctions f j) (kummerBoundaryProduct Λ f) =
      frameClass Λ (Scheme.Hom.EtaleFrame.ofFunctions f j) :=
  restrictSupportedClass_kummerBoundaryProduct Λ j f _ (fun _ ↦ rfl) _ _

/-- Restriction of classes with supports along a composite, with the standard identifications
of the constant and Tate complexes. -/
lemma restrictSupportedClass_comp_tateShift [HasKummerClass Λ] {U U' U₂ Z Z' Z₂ : Scheme.{u}}
    (e₁ : U₂ ⟶ U') (e : U' ⟶ U)
    (e' : U₂ ⟶ U) (he : e' = e₁ ≫ e)
    (i : Z ⟶ U) (i' : Z' ⟶ U') (i₂ : Z₂ ⟶ U₂) [IsClosedImmersion i] [IsClosedImmersion i']
    [IsClosedImmersion i₂] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    (g₂ : Z₂ ⟶ Z') (hg₂ : IsPullback g₂ i₂ i' e₁) (g' : Z₂ ⟶ Z) (hg' : IsPullback g' i₂ i e')
    (γ : constantComplex Λ U ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ U c)⟦2 * (c : ℤ)⟧))) :
    restrictSupportedClass (ModuleCat.{u + 1} Λ) e' i i₂ g' hg'
        (leftDerivedUpperStarConstantComplexIso Λ e').inv
        (leftDerivedUpperStarTateShiftIso Λ e' c) γ =
      restrictSupportedClass (ModuleCat.{u + 1} Λ) e₁ i' i₂ g₂ hg₂
        (leftDerivedUpperStarConstantComplexIso Λ e₁).inv (leftDerivedUpperStarTateShiftIso Λ e₁ c)
        (restrictSupportedClass (ModuleCat.{u + 1} Λ) e i i' g hg
          (leftDerivedUpperStarConstantComplexIso Λ e).inv
          (leftDerivedUpperStarTateShiftIso Λ e c) γ) := by
  rw [leftDerivedUpperStarConstantComplexIso_comp Λ e₁ e _ he,
    leftDerivedUpperStarTateShiftIso_comp Λ e₁ e _ he]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
  exact restrictSupportedClass_restrictSupportedClass (ModuleCat.{u + 1} Λ) e e₁ e' he i
    i' i₂ g hg g₂ hg₂ g' hg' _ _ _ _ γ

/-- A local class `δ : Le^* Λ_X ⟶ Le^* (Ri_! Ri^! Λ(c)[2c])` corresponding to the class `β` with
supports on `U` restricts along `a : W ⟶ U` to the restriction of `β`. -/
lemma constantComplexIso_inv_comp_leftDerivedUpperStarComp_map_supportedRestriction
    [HasKummerClass Λ]
    {U W X Z Z₁ Z' : Scheme.{u}} (e : U ⟶ X) (a : W ⟶ U) (w : W ⟶ X) (hw : w = a ≫ e)
    (i : Z ⟶ X) (i₁ : Z₁ ⟶ U) (i' : Z' ⟶ W) [IsClosedImmersion i] [IsClosedImmersion i₁]
    [IsClosedImmersion i'] (g₁ : Z₁ ⟶ Z) (hg₁ : IsPullback g₁ i₁ i e) (g₂ : Z' ⟶ Z₁)
    (hg₂ : IsPullback g₂ i' i₁ a) (g' : Z' ⟶ Z) (hg' : IsPullback g' i' i w)
    (δ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X) ⟶
      (L((e)^*[ModuleCat.{u + 1} Λ])).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))))
    (β : constantComplex Λ U ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₁)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ U c)⟦2 * (c : ℤ)⟧)))
    (hδ : δ ≫ supportedRestriction _ e i i₁ g₁ hg₁ _ _ (leftDerivedUpperStarTateShiftIso Λ e c) =
      (leftDerivedUpperStarConstantComplexIso Λ e).hom ≫ β) :
    (leftDerivedUpperStarConstantComplexIso Λ w).inv ≫
        (leftDerivedUpperStarComp _ a e w hw).hom.app _ ≫ (L((a)^*[_])).map δ ≫
          (leftDerivedUpperStarComp _ a e w hw).inv.app _ ≫
            supportedRestriction _ w i i' g' hg' _ _ (leftDerivedUpperStarTateShiftIso Λ w c) =
      restrictSupportedClass (ModuleCat.{u + 1} Λ) a i₁ i' g₂ hg₂
        (leftDerivedUpperStarConstantComplexIso Λ a).inv (leftDerivedUpperStarTateShiftIso Λ a c)
        β := by
  have ht := supportedRestriction_trans (ModuleCat.{u + 1} Λ) e a w hw i i₁ i' g₁ hg₁ g₂ hg₂
    g' hg' _ _ _ (leftDerivedUpperStarTateShiftIso Λ e c) (leftDerivedUpperStarTateShiftIso Λ a c)
  rw [← leftDerivedUpperStarTateShiftIso_comp Λ a e w hw] at ht
  rw [ht, leftDerivedUpperStarConstantComplexIso_comp Λ a e w hw]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, hδ,
    Iso.inv_hom_id_assoc]
  rfl

variable [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ X]
  {k : Type u} [Field k] [PerfectField k] (c) (i) [IsRegularImmersion c i]

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

**(a) Concentration in degree zero.** `Ri^! (Λ_X(c)[2c])` has no cohomology sheaves outside
degree `0`. The hypotheses are stable under étale base change `X' ⟶ X`, so this holds after
any étale base change too. -/
theorem isZero_homology_rightDerivedUpperShriek_of_isRegularImmersion
    (aX : X ⟶ Spec (.of k)) [Smooth aX] (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z))
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))) := by
  choose W hzW e using
    exists_nonempty_iso_upperStar_rightDerivedUpperShriek_of_isRegularImmersion Λ c i aX hZ
  -- the restrictions to the neighbourhoods `Z ∩ W` are the cohomology sheaves of `Λ`
  have := Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (ι := Z) (fun z ↦ (i ⁻¹ᵁ W z).ι) (fun z ↦ ⟨z, ⟨z, hzW z⟩, rfl⟩)
    (0 : (_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) ⟶ 0) (fun z ↦
      isIso_of_source_target_iso_zero _
        ((isZero_homology_constantComplex Λ _ n hn).of_iso
          ((((i ⁻¹ᵁ W z).ι)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryHomologyFunctorIso n).app _ ≪≫
            (_root_.DerivedCategory.homologyFunctor _ n).mapIso (e z).some)).isoZero
        (Functor.map_isZero _ (isZero_zero _)).isoZero)
  exact (isZero_zero _).of_iso (asIso (0 : (_root_.DerivedCategory.homologyFunctor _ n).obj
    ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) ⟶ 0))

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

**(a) Rank one.** `𝓗⁰(Ri^! (Λ_X(c)[2c]))` is free of rank one étale-locally: there is an étale
cover of `Z` on each member of which it becomes the constant sheaf `Λ`. Consequently
`H⁰(Z, Ri^! Λ_X(c)[2c]) = H^{2c}_Z(X, Λ(c)) = Γ(Z, 𝓗⁰)`, and likewise after étale base
change. -/
theorem exists_cover_nonempty_iso_homology_zero_rightDerivedUpperShriek_of_isRegularImmersion
    (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage Z, ∀ a : 𝒰.I₀,
      Nonempty ((upperStar (ModuleCat.{u + 1} Λ) (𝒰.f a)).obj
          ((_root_.DerivedCategory.homologyFunctor _ 0).obj
            ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))) ≅
        (constantSheaf (𝒰.X a).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ Λ)) := by
  choose W hzW e using
    exists_nonempty_iso_upperStar_rightDerivedUpperShriek_of_isRegularImmersion Λ c i aX hZ
  refine ⟨Scheme.Cover.mkOfCovers (P := @AlgebraicGeometry.Etale) Z
    (fun z ↦ (i ⁻¹ᵁ W z).toScheme) (fun z ↦ (i ⁻¹ᵁ W z).ι) (fun z ↦ ⟨z, ⟨z, hzW z⟩, rfl⟩),
    fun z ↦ ⟨?_⟩⟩
  exact (((i ⁻¹ᵁ W z).ι)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryHomologyFunctorIso 0).app _ ≪≫
    (_root_.DerivedCategory.homologyFunctor _ 0).mapIso (e z).some ≪≫
    homologyZeroConstantComplexIso Λ _

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

**(a) Lisse in degree zero.** `𝓗⁰(Ri^! (Λ_X(c)[2c]))` is a locally constant sheaf on `Z_ét`:
it is constant on the members of an étale cover of `Z`.
-/
theorem isLocallyConstantSheaf_homology_zero_rightDerivedUpperShriek_of_isRegularImmersion
    (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    Scheme.IsLocallyConstantSheaf ((_root_.DerivedCategory.homologyFunctor _ 0).obj
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))) := by
  obtain ⟨𝒰, h𝒰⟩ :=
    exists_cover_nonempty_iso_homology_zero_rightDerivedUpperShriek_of_isRegularImmersion Λ c i
      aX hZ
  refine ⟨⟨⟨𝒰, fun a ↦ ?_⟩⟩⟩
  rw [isConstant_over_iff_upperStar]
  exact Sheaf.isConstant_of_iso _ (h𝒰 a).some

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

Classes with supports `H^{2c}_Z(X, Λ(c))` are sections of a sheaf: `Ri_! Ri^! (Λ_X(c)[2c])` is a
sheaf placed in degree zero, since `Ri^! (Λ_X(c)[2c])` is (clause (a)) and `Ri_! = i_*` is exact.
-/
theorem exists_iso_singleFunctor_rightDerivedLowerShriek_of_isRegularImmersion
    (aX : X ⟶ Spec (.of k)) [Smooth aX] (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    ∃ G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      Nonempty ((R(i)_![ModuleCat.{u + 1} Λ]).obj
          ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj G) := by
  set K := (R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)
  have hK := isZero_homology_rightDerivedUpperShriek_of_isRegularImmersion Λ c i aX hZ
  have : K.IsGE 0 := (_root_.DerivedCategory.isGE_iff K 0).2 fun n hn ↦ hK n hn.ne
  have : K.IsLE 0 := (_root_.DerivedCategory.isLE_iff K 0).2 fun n hn ↦ hK n hn.ne'
  have := Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom Λ i
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar
    (ModuleCat.{u + 1} Λ) i
  have : (((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K).IsGE 0 :=
    ((i)_*[ModuleCat.{u + 1} Λ]).isGE_mapDerivedCategory_obj K 0
  have : (((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K).IsLE 0 :=
    ((i)_*[ModuleCat.{u + 1} Λ]).isLE_mapDerivedCategory_obj K 0
  obtain ⟨G, ⟨e'⟩⟩ := _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K) 0
  exact ⟨G, ⟨e.app K ≪≫
    ((i)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorIsoMapDerivedCategory.app K ≪≫ e'⟩⟩

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

*Uniqueness of the fundamental class.* Two classes in `H^{2c}_Z(X, Λ(c))` are equal if every
point of `Z` lies in a Zariski frame on which their restrictions agree. The classes are sections
of a sheaf
(`AlgebraicGeometry.Etale.exists_iso_singleFunctor_rightDerivedLowerShriek_of_isRegularImmersion`),
so they are determined by their pullbacks to the geometric points of `X`. A geometric point
outside `Z` sees nothing; a geometric point of `Z` factors through a Zariski frame, and the
restriction of supports along an open immersion is invertible
(`AlgebraicGeometry.Etale.isIso_supportedRestriction_of_isOpenImmersion`). -/
theorem eq_of_forall_exists_frameRestriction_eq (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z))
    {γ γ' : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))}
    (h : ∀ z : Z, ∃ F : i.EtaleFrame c, IsOpenImmersion F.e ∧ z ∈ Set.range F.toZ ∧
      frameRestriction Λ F γ = frameRestriction Λ F γ') :
    γ = γ' := by
  obtain ⟨G, ⟨eM⟩⟩ :=
    exists_iso_singleFunctor_rightDerivedLowerShriek_of_isRegularImmersion Λ c i aX hZ
  refine hom_ext_of_leftDerivedUpperStar_map_eq (constantComplexIsoSingleFunctor Λ X) eM
    fun Ω _ _ x ↦ ?_
  have : Subsingleton (Spec (.of Ω)) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  by_cases hx : Set.range x.base ⊆ Set.range i.openComplement.ι.base
  · -- `x` misses `Z`, where the classes live
    refine (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint
      (ModuleCat.{u + 1} Λ) i i.openComplement.ι ?_ x hx _).eq_of_tgt _ _
    rw [i.range_eq_compl_range_openComplement_ι]
    exact disjoint_compl_left
  · -- `x` is a point of `Z`, which lies in a Zariski frame
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ := Set.not_subset.mp hx
    rw [← Set.mem_compl_iff, ← i.range_eq_compl_range_openComplement_ι] at hy
    obtain ⟨z, hz⟩ := hy
    obtain ⟨F, hF, ⟨w, rfl⟩, hFγ⟩ := h z
    have hxe : Set.range x.base ⊆ Set.range F.e.base := by
      rintro _ ⟨y', rfl⟩
      refine ⟨(F.U.zeroLocusSubschemeι (Set.range F.f)) w, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← F.isPullback.w, Scheme.Hom.comp_apply, hz,
        Subsingleton.elim y' y]
    have he : (L((F.e)^*[ModuleCat.{u + 1} Λ])).map γ =
        (L((F.e)^*[ModuleCat.{u + 1} Λ])).map γ' := by
      have hψ := isIso_supportedRestriction_of_isOpenImmersion (ModuleCat.{u + 1} Λ) F.e i _ F.toZ
        F.isPullback _ _ (leftDerivedUpperStarTateShiftIso Λ F.e c)
      have := hFγ
      simp only [frameRestriction, restrictSupportedClass] at this
      rwa [cancel_epi, cancel_mono] at this
    have hx' := IsOpenImmersion.lift_fac F.e x hxe
    let comp := leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (IsOpenImmersion.lift F.e x hxe)
      F.e x hx'.symm
    rw [← NatIso.naturality_2 comp γ, ← NatIso.naturality_2 comp γ', Functor.comp_map,
      Functor.comp_map, he]

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

*Uniqueness of the fundamental class.* Two classes in `H^{2c}_Z(X, Λ(c))` whose restrictions to
every Zariski frame agree are equal
(`AlgebraicGeometry.Etale.eq_of_forall_exists_frameRestriction_eq`): every point of `Z` lies in a
Zariski frame (`AlgebraicGeometry.Scheme.Hom.exists_etaleFrame_isOpenImmersion`). -/
theorem eq_of_frameRestriction_eq (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z))
    {γ γ' : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))}
    (h : ∀ F : i.EtaleFrame c, IsOpenImmersion F.e →
      frameRestriction Λ F γ = frameRestriction Λ F γ') :
    γ = γ' :=
  eq_of_forall_exists_frameRestriction_eq Λ c i aX hZ fun z ↦
    have ⟨F, hF, hz, _⟩ := i.exists_etaleFrame_isOpenImmersion c z
    ⟨F, hF, hz, h F hF⟩

/-- **Frame classes agree on overlaps.** Two frames `F₁`, `F₂`, with `F₁` given by a weakly
regular sequence on an affine scheme, have the same restriction to any `W` étale over both. -/
theorem restrictSupportedClass_frameClass_eq (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) (F₁ F₂ : i.EtaleFrame c)
    [IsAffine F₁.U] (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(F₁.U, ⊤) (List.ofFn F₁.f))
    {W Z' : Scheme.{u}} (a : W ⟶ F₁.U) (b : W ⟶ F₂.U) [AlgebraicGeometry.Etale a]
    [AlgebraicGeometry.Etale b] (hab : a ≫ F₁.e = b ≫ F₂.e) (i' : Z' ⟶ W) [IsClosedImmersion i']
    (g₁ : Z' ⟶ _) (hg₁ : IsPullback g₁ i' (F₁.U.zeroLocusSubschemeι (Set.range F₁.f)) a)
    (g₂ : Z' ⟶ _) (hg₂ : IsPullback g₂ i' (F₂.U.zeroLocusSubschemeι (Set.range F₂.f)) b) :
    restrictSupportedClass (ModuleCat.{u + 1} Λ) a _ i' g₁ hg₁
        (leftDerivedUpperStarConstantComplexIso Λ a).inv (leftDerivedUpperStarTateShiftIso Λ a c)
        (frameClass Λ F₁) =
      restrictSupportedClass (ModuleCat.{u + 1} Λ) b _ i' g₂ hg₂
        (leftDerivedUpperStarConstantComplexIso Λ b).inv (leftDerivedUpperStarTateShiftIso Λ b c)
        (frameClass Λ F₂) := by
  have hw := hg₁.paste_horiz F₁.isPullback
  have := IsRegularImmersion.of_isPullback c hw
  have : HasInvertibleExponent Λ W := .of_hom (a ≫ F₁.e)
  have : AlgebraicGeometry.Etale (g₁ ≫ F₁.toZ) :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale) hw.flip inferInstance
  refine eq_of_forall_exists_frameRestriction_eq Λ c i' ((a ≫ F₁.e) ≫ aX)
    (isRegularLocalRing_stalk_of_etale (g₁ ≫ F₁.toZ) hZ) fun z ↦ ?_
  obtain ⟨D, hD, hzD⟩ : ∃ D : W.Opens, IsAffineOpen D ∧ i' z ∈ D := by
    obtain ⟨_, ⟨D, hD, rfl⟩, hzD, -⟩ :=
      W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (i' z)) isOpen_univ
    exact ⟨D, hD, hzD⟩
  have : IsAffine D.toScheme := hD
  let v : Fin c → Γ(D.toScheme, ⊤) := fun t ↦ (D.ι ≫ a).appTop (F₁.f t)
  let w : Fin c → Γ(D.toScheme, ⊤) := fun t ↦ (D.ι ≫ b).appTop (F₂.f t)
  have hv : RingTheory.Sequence.IsWeaklyRegular Γ(D.toScheme, ⊤) (List.ofFn v) := by
    have : List.ofFn v = (List.ofFn F₁.f).map (D.ι ≫ a).appTop.hom := by
      rw [List.map_ofFn]; rfl
    rw [this]
    exact hreg.map_of_flat (HasRingHomProperty.appTop @Flat (D.ι ≫ a) inferInstance)
  obtain ⟨gv, hgv⟩ := exists_isPullback_zeroLocusSubschemeι (D.ι ≫ a) (Set.range F₁.f)
    (Set.range v) (by rw [← Set.range_comp]; rfl)
  obtain ⟨gw, hgw⟩ := exists_isPullback_zeroLocusSubschemeι (D.ι ≫ b) (Set.range F₂.f)
    (Set.range w) (by rw [← Set.range_comp]; rfl)
  have heq : (D.ι ≫ b) ≫ F₂.e = (D.ι ≫ a) ≫ F₁.e := by simp [hab]
  have hspan : Ideal.span (Set.range w) = Ideal.span (Set.range v) :=
    Scheme.span_eq_of_isPullback_zeroLocusSubschemeι (heq ▸ hgw.paste_horiz F₂.isPullback)
      (hgv.paste_horiz F₁.isPullback)
  obtain ⟨M, hM, hdet⟩ := RingTheory.Sequence.IsWeaklyRegular.exists_mulVec_isUnit_det v w hv
    hspan
  -- the point `i' z` of `D` lies in the zero locus of `v`
  obtain ⟨p, hp⟩ : i' z ∈ Set.range D.ι.base := by rw [Scheme.Opens.range_ι]; exact hzD
  have hp0 : p ∈ D.toScheme.zeroLocus (Set.range v) := by
    rw [← Scheme.range_zeroLocusSubschemeι]
    obtain ⟨q, -, hq⟩ := hgv.exists_scheme_point (g₁ z) p (by
      rw [← Scheme.Hom.comp_apply, hg₁.w, Scheme.Hom.comp_apply, ← hp, ← Scheme.Hom.comp_apply])
    exact ⟨q, hq⟩
  -- the frame of `i'` on the basic open of `det M`, given by `v`
  set B := D.toScheme.basicOpen M.det
  obtain ⟨pB, hpB⟩ : p ∈ Set.range B.ι.base := by
    rw [Scheme.Opens.range_ι]; exact Scheme.mem_basicOpen_of_isUnit_mk hdet hp0
  let f : Fin c → Γ(B.toScheme, ⊤) := fun t ↦ B.ι.appTop (v t)
  obtain ⟨gB, hgB⟩ := exists_isPullback_zeroLocusSubschemeι B.ι (Set.range v) (Set.range f)
    (by rw [← Set.range_comp]; rfl)
  have hout := hgB.paste_horiz hgv
  let toZ := hg₁.lift (gB ≫ gv) (B.toScheme.zeroLocusSubschemeι (Set.range f) ≫ B.ι ≫ D.ι)
    (by rw [Category.assoc, hgv.w, reassoc_of% hgB.w]; simp)
  have hH : IsPullback toZ (B.toScheme.zeroLocusSubschemeι (Set.range f)) i' (B.ι ≫ D.ι) := by
    refine IsPullback.of_right (h₁₂ := g₁) (v₁₃ := F₁.U.zeroLocusSubschemeι (Set.range F₁.f))
      (h₂₂ := a) ?_ (hg₁.lift_snd _ _ _) hg₁
    rw [hg₁.lift_fst]
    simpa using hout
  let H : i'.EtaleFrame c :=
    { U := B.toScheme
      e := B.ι ≫ D.ι
      etale := inferInstance
      f := f
      toZ := toZ
      isPullback := hH }
  have : HasInvertibleExponent Λ B.toScheme := .of_hom (B.ι ≫ D.ι ≫ a ≫ F₁.e)
  refine ⟨H, inferInstanceAs (IsOpenImmersion (B.ι ≫ D.ι)), ?_, ?_⟩
  · obtain ⟨z', hz', -⟩ := hH.exists_scheme_point z pB (by
      rw [Scheme.Hom.comp_apply, hpB, hp])
    exact ⟨z', hz'⟩
  -- the restriction of the class of `F₁` is the class of `v`
  have h₁ : frameRestriction Λ H (restrictSupportedClass (ModuleCat.{u + 1} Λ) a _ i' g₁ hg₁
      (leftDerivedUpperStarConstantComplexIso Λ a).inv (leftDerivedUpperStarTateShiftIso Λ a c)
      (frameClass Λ F₁)) = kummerBoundaryProduct Λ f := by
    rw [frameRestriction, ← restrictSupportedClass_comp_tateShift Λ H.e a _ rfl _ _ _ g₁ hg₁
      toZ hH (toZ ≫ g₁) (hH.paste_horiz hg₁)]
    exact restrictSupportedClass_kummerBoundaryProduct Λ _ F₁.f f (fun _ ↦ rfl) _ _
  -- the restriction of the class of `F₂` is the class of `M v`, hence of `v`
  let w' : Fin c → Γ(B.toScheme, ⊤) := fun t ↦ B.ι.appTop (w t)
  let M' := M.map B.ι.appTop.hom
  have hw' : w' = M'.mulVec f := by
    funext t
    simp only [w', f, M', hM, RingHom.map_mulVec]
    rfl
  have hdet' : IsUnit M'.det := by
    rw [show M'.det = _ from (RingHom.map_det B.ι.appTop.hom M).symm]
    refine B.toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun y _ ↦ ?_
    rw [← B.toScheme.mem_basicOpen_top, ← Scheme.preimage_basicOpen_top]
    exact y.2
  obtain ⟨gw', hgw'⟩ := exists_isPullback_zeroLocusSubschemeι (H.e ≫ b) (Set.range F₂.f)
    (Set.range w') (by rw [← Set.range_comp]; rfl)
  obtain ⟨g₀, hg₀⟩ := Scheme.exists_isPullback_zeroLocusSubschemeι_of_span_eq
    (U := B.toScheme) (s := Set.range w') (s' := Set.range f)
    (by rw [hw', Ideal.span_range_mulVec_of_isUnit_det _ hdet'])
  have key : ∀ (w'' : Fin c → Γ(B.toScheme, ⊤)) (_ : w'' = M'.mulVec f) (g : _ ⟶ _)
      (hg : IsPullback g (B.toScheme.zeroLocusSubschemeι (Set.range f))
        (B.toScheme.zeroLocusSubschemeι (Set.range w'')) (𝟙 _)),
      restrictSupportedClass (ModuleCat.{u + 1} Λ) (𝟙 _) _ _ g hg
        (leftDerivedUpperStarConstantComplexIso Λ (𝟙 _)).inv
        (leftDerivedUpperStarTateShiftIso Λ (𝟙 _) c) (kummerBoundaryProduct Λ w'') =
      kummerBoundaryProduct Λ f := by
    rintro _ rfl g hg
    exact restrictSupportedClass_kummerBoundaryProduct_mulVec Λ f M' hdet' g hg
  have h₂ : frameRestriction Λ H (restrictSupportedClass (ModuleCat.{u + 1} Λ) b _ i' g₂ hg₂
      (leftDerivedUpperStarConstantComplexIso Λ b).inv (leftDerivedUpperStarTateShiftIso Λ b c)
      (frameClass Λ F₂)) = kummerBoundaryProduct Λ f := by
    rw [frameRestriction, ← restrictSupportedClass_comp_tateShift Λ H.e b _ rfl _ _ _ g₂ hg₂
      toZ hH (toZ ≫ g₂) (hH.paste_horiz hg₂),
      restrictSupportedClass_comp_tateShift Λ (𝟙 _) (H.e ≫ b) _ (Category.id_comp _).symm _ _ _
      gw' hgw'
      g₀ hg₀ (toZ ≫ g₂) (hH.paste_horiz hg₂)]
    rw [frameClass, restrictSupportedClass_kummerBoundaryProduct Λ _ F₂.f w' (fun _ ↦ rfl) _ _]
    exact key w' hw' g₀ hg₀
  rw [h₁, h₂]



/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

**(b) The fundamental class.** Let `i : Z ⟶ X` be a regular closed immersion of pure
codimension `c`, with `X` smooth over the perfect field `k` and `Z` regular. The frame classes
depend only on `Z_U ⊂ U`, not on the frame, and they glue: there is a unique class
`[Z ⊂ X] ∈ H^{2c}_Z(X, Λ(c))` whose restriction to every frame is the frame class.

Near every point of `Z` there is a frame given by a regular sequence on an affine open, and any
other frame differs from it, near `Z`, by a matrix with invertible determinant
(`RingTheory.Sequence.IsWeaklyRegular.exists_mulVec_isUnit_det`), under which the frame classes
agree (`AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_mulVec`); so frame
classes agree on overlaps (`AlgebraicGeometry.Etale.restrictSupportedClass_frameClass_eq`). By
(a) the classes are morphisms into a sheaf placed in degree zero, so the Zariski-local classes
glue (`AlgebraicGeometry.Etale.exists_hom_of_isOpenImmersion_cover`). -/
theorem existsUnique_fundamentalClass (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    ∃! γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)),
      ∀ F : i.EtaleFrame c, frameRestriction Λ F γ = frameClass Λ F := by
  obtain ⟨G, ⟨eM⟩⟩ :=
    exists_iso_singleFunctor_rightDerivedLowerShriek_of_isRegularImmersion Λ c i aX hZ
  choose F hFo hzF hFa hFr using fun z ↦ i.exists_etaleFrame_isOpenImmersion c z
  have hdisj : Disjoint (Set.range i.base) (Set.range i.openComplement.ι.base) := by
    rw [i.range_eq_compl_range_openComplement_ι]
    exact disjoint_compl_left
  -- the cover of `X` by the Zariski frames and the complement of `Z`
  let V : Option Z → Scheme.{u} := fun j ↦ Option.elim j i.openComplement.toScheme (F · |>.U)
  let e : ∀ j, V j ⟶ X := fun j ↦ match j with
    | none => i.openComplement.ι
    | some z => (F z).e
  have he : ∀ j, IsOpenImmersion (e j) := by
    rintro (_ | z)
    · exact inferInstanceAs (IsOpenImmersion i.openComplement.ι)
    · exact hFo z
  have hΨ : ∀ z, IsIso (supportedRestriction (ModuleCat.{u + 1} Λ) (F z).e i _ (F z).toZ
      (F z).isPullback _ _ (leftDerivedUpperStarTateShiftIso Λ (F z).e c)) := fun z ↦
    have := hFo z
    isIso_supportedRestriction_of_isOpenImmersion _ _ _ _ _ _ _ _ _
  let δ : ∀ j, (L((e j)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X) ⟶
      (L((e j)^*[ModuleCat.{u + 1} Λ])).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))) :=
    fun j ↦ match j with
    | none => 0
    | some z => (leftDerivedUpperStarConstantComplexIso Λ (F z).e).hom ≫ frameClass Λ (F z) ≫
        inv (supportedRestriction (ModuleCat.{u + 1} Λ) (F z).e i _ (F z).toZ
          (F z).isPullback _ _ (leftDerivedUpperStarTateShiftIso Λ (F z).e c))
  have hδ : ∀ z, δ (some z) ≫ supportedRestriction (ModuleCat.{u + 1} Λ) (F z).e i _ (F z).toZ
      (F z).isPullback _ _ (leftDerivedUpperStarTateShiftIso Λ (F z).e c) =
        (leftDerivedUpperStarConstantComplexIso Λ (F z).e).hom ≫ frameClass Λ (F z) := by
    intro z
    simp [δ]
  -- the restriction of `Ri_! Ri^! (Λ(c)[2c])` to the complement of `Z` vanishes
  have hzero : ∀ {W : Scheme.{u}} (w : W ⟶ X),
      Set.range w.base ⊆ Set.range i.openComplement.ι.base →
      IsZero ((L((w)^*[ModuleCat.{u + 1} Λ])).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)))) :=
    fun w hw ↦ isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint _ i
      i.openComplement.ι hdisj w hw _
  have hcov : ∀ x : X, ∃ j, x ∈ Set.range (e j).base := by
    intro x
    by_cases hx : x ∈ Set.range i.base
    · obtain ⟨z, rfl⟩ := hx
      obtain ⟨w, hw⟩ := hzF z
      refine ⟨some z, (F z).U.zeroLocusSubschemeι _ w, ?_⟩
      change (F z).e _ = i z
      rw [← Scheme.Hom.comp_apply, ← (F z).isPullback.w, Scheme.Hom.comp_apply, hw]
    · refine ⟨none, ?_⟩
      rwa [← Set.mem_compl_iff, i.range_eq_compl_range_openComplement_ι, compl_compl] at hx
  obtain ⟨γ, hγ⟩ := exists_hom_of_isOpenImmersion_cover (constantComplexIsoSingleFunctor Λ X) eM
    e hcov δ (by
    rintro (_ | z) (_ | z') W a b _ _ h
    · exact (hzero _ (by rintro _ ⟨y, rfl⟩; exact ⟨a y, rfl⟩)).eq_of_tgt _ _
    · exact (hzero _ (by rintro _ ⟨y, rfl⟩; exact ⟨a y, rfl⟩)).eq_of_tgt _ _
    · exact (hzero _ (by rw [h]; rintro _ ⟨y, rfl⟩; exact ⟨b y, rfl⟩)).eq_of_tgt _ _
    · -- two Zariski frames: compare the restrictions of the frame classes to `W`
      have := hFo z
      have := hFo z'
      have := hFa z
      change W ⟶ (F z).U at a
      change W ⟶ (F z').U at b
      change a ≫ (F z).e = b ≫ (F z').e at h
      obtain ⟨g₁, hg₁⟩ := exists_isPullback_zeroLocusSubschemeι a (Set.range (F z).f)
        (Set.range fun t ↦ a.appTop ((F z).f t)) (by rw [← Set.range_comp]; rfl)
      have hg' := hg₁.paste_horiz (F z).isPullback
      have hout : IsPullback (g₁ ≫ (F z).toZ)
          (W.zeroLocusSubschemeι (Set.range fun t ↦ a.appTop ((F z).f t))) i (b ≫ (F z').e) :=
        h ▸ hg'
      let g₂ := (F z').isPullback.lift (g₁ ≫ (F z).toZ)
        (W.zeroLocusSubschemeι (Set.range fun t ↦ a.appTop ((F z).f t)) ≫ b)
        (by rw [hout.w, Category.assoc])
      have hg₂ : IsPullback g₂ (W.zeroLocusSubschemeι (Set.range fun t ↦ a.appTop ((F z).f t)))
          _ b :=
        IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hout)
          ((F z').isPullback.lift_snd _ _ _)
          (F z').isPullback
      have := isIso_supportedRestriction_of_isOpenImmersion (ModuleCat.{u + 1} Λ) (a ≫ (F z).e) i
        _ _ hg' _ _ (leftDerivedUpperStarTateShiftIso Λ (a ≫ (F z).e) c)
      rw [← cancel_epi (leftDerivedUpperStarConstantComplexIso Λ (a ≫ (F z).e)).inv,
        ← cancel_mono (supportedRestriction (ModuleCat.{u + 1} Λ) (a ≫ (F z).e) i _ _ hg' _ _
          (leftDerivedUpperStarTateShiftIso Λ (a ≫ (F z).e) c))]
      simp only [Category.assoc]
      exact (constantComplexIso_inv_comp_leftDerivedUpperStarComp_map_supportedRestriction Λ
        (F z).e a _ rfl i _ _ (F z).toZ (F z).isPullback g₁ hg₁ _ hg' _ _ (hδ z)).trans
          ((restrictSupportedClass_frameClass_eq Λ c i aX hZ (F z) (F z') (hFr z) a b h _ g₁ hg₁
            g₂ hg₂).trans
          (constantComplexIso_inv_comp_leftDerivedUpperStarComp_map_supportedRestriction Λ
            (F z').e b _ h i _ _ (F z').toZ (F z').isPullback g₂ hg₂ _ hg' _ _ (hδ z')).symm))
  have hγz : ∀ z, frameRestriction Λ (F z) γ = frameClass Λ (F z) := by
    intro z
    have h : (L(((F z).e)^*[ModuleCat.{u + 1} Λ])).map γ = δ (some z) := hγ (some z)
    simp only [frameRestriction, restrictSupportedClass, h, δ, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, Iso.inv_hom_id_assoc]
  -- every frame is compared with the Zariski frames near each of its points
  have hall : ∀ F' : i.EtaleFrame c, frameRestriction Λ F' γ = frameClass Λ F' := by
    intro F'
    have := IsRegularImmersion.of_isPullback c F'.isPullback
    have : HasInvertibleExponent Λ F'.U := .of_hom F'.e
    have : AlgebraicGeometry.Etale F'.toZ :=
      MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale) F'.isPullback.flip
        inferInstance
    refine eq_of_forall_exists_frameRestriction_eq Λ c _ (F'.e ≫ aX)
      (isRegularLocalRing_stalk_of_etale F'.toZ hZ) fun z' ↦ ?_
    set z := F'.toZ z'
    have := hFo z
    have := hFa z
    let W : F'.U.Opens := F'.e ⁻¹ᵁ (F z).e.opensRange
    have hrange : Set.range (W.ι ≫ F'.e).base ⊆ Set.range (F z).e.base := by
      rintro _ ⟨y, rfl⟩
      exact y.2
    let a := IsOpenImmersion.lift (F z).e (W.ι ≫ F'.e) hrange
    have hab : a ≫ (F z).e = W.ι ≫ F'.e := IsOpenImmersion.lift_fac _ _ _
    have : AlgebraicGeometry.Etale (a ≫ (F z).e) := hab ▸ inferInstance
    have : AlgebraicGeometry.Etale a := .of_comp a (F z).e
    let H := Scheme.Hom.EtaleFrame.ofFunctions F'.f W.ι
    have hout : IsPullback (H.toZ ≫ F'.toZ) (W.toScheme.zeroLocusSubschemeι (Set.range H.f)) i
        (a ≫ (F z).e) := hab ▸ H.isPullback.paste_horiz F'.isPullback
    let g₁ := (F z).isPullback.lift (H.toZ ≫ F'.toZ)
      (W.toScheme.zeroLocusSubschemeι (Set.range H.f) ≫ a) (by rw [hout.w, Category.assoc])
    have hg₁ : IsPullback g₁ (W.toScheme.zeroLocusSubschemeι (Set.range H.f)) _ a :=
      IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hout)
        ((F z).isPullback.lift_snd _ _ _) (F z).isPullback
    refine ⟨H, inferInstanceAs (IsOpenImmersion W.ι), ?_, ?_⟩
    · obtain ⟨w₀, hw₀⟩ := hzF z
      obtain ⟨p, hp⟩ : (F'.U.zeroLocusSubschemeι (Set.range F'.f)) z' ∈ Set.range W.ι.base := by
        rw [Scheme.Opens.range_ι]
        refine ⟨(F z).U.zeroLocusSubschemeι _ w₀, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← (F z).isPullback.w, Scheme.Hom.comp_apply, hw₀,
          ← Scheme.Hom.comp_apply, F'.isPullback.w, Scheme.Hom.comp_apply]
      obtain ⟨q, hq, -⟩ := H.isPullback.exists_scheme_point z' p hp.symm
      exact ⟨q, hq⟩
    · have e₁ := restrictSupportedClass_comp_tateShift Λ W.ι F'.e (W.ι ≫ F'.e) rfl _ _ _ F'.toZ
        F'.isPullback H.toZ H.isPullback _ (H.isPullback.paste_horiz F'.isPullback) γ
      have e₂ := restrictSupportedClass_comp_tateShift Λ a (F z).e (W.ι ≫ F'.e) hab.symm _ _ _
        (F z).toZ (F z).isPullback g₁ hg₁ _ (H.isPullback.paste_horiz F'.isPullback) γ
      have e₃ := restrictSupportedClass_frameClass_eq Λ c i aX hZ (F z) F' (hFr z) a W.ι hab _ g₁
        hg₁ H.toZ H.isPullback
      exact e₁.symm.trans (e₂.trans ((congrArg (restrictSupportedClass _ a _ _ g₁ hg₁ _ _)
        (hγz z)).trans e₃))
  exact ⟨γ, hall, fun γ' hγ' ↦ eq_of_frameRestriction_eq Λ c i aX hZ fun F _ ↦ by
    rw [hγ' F, hall F]⟩

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

The *fundamental class* `[Z ⊂ X] = cl_{Z/X} ∈ H^{2c}_Z(X, Λ(c))` of a regular closed immersion
`i : Z ⟶ X` of pure codimension `c`, with `X` smooth over a perfect field and `Z` regular: the
unique class restricting to the frame class `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c)` on every frame.

It is *defined* as `Classical.choose` of
`AlgebraicGeometry.Etale.existsUnique_fundamentalClass`; uniqueness
is what makes the choice canonical. -/
noncomputable def fundamentalClass (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) :=
  (existsUnique_fundamentalClass Λ c i aX hZ).exists.choose

/-- The fundamental class restricts to the frame class on every frame. -/
theorem frameRestriction_fundamentalClass (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) (F : i.EtaleFrame c) :
    frameRestriction Λ F (fundamentalClass Λ c i aX hZ) = frameClass Λ F :=
  (existsUnique_fundamentalClass Λ c i aX hZ).exists.choose_spec F

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

The morphism `cl_i : Λ_Z ⟶ Ri^! (Λ_X(c)[2c])`, `1 ↦ [Z ⊂ X]`: the adjoint
(`AlgebraicGeometry.Etale.supportedClassMap`) of the fundamental class
`Λ_X ⟶ Ri_! Ri^! (Λ_X(c)[2c])`, through the forget-supports map `Ri_! ⟶ Ri_*`, which is an
isomorphism as `i` is a closed immersion. -/
noncomputable def fundamentalClassMap (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    constantComplex Λ Z ⟶
      (R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧) :=
  supportedClassMap Λ i (fundamentalClass Λ c i aX hZ)

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

**(b) The fundamental class generates.** `[Z ⊂ X]` generates `𝓗⁰(Ri^! Λ_X(c)[2c])` at every
geometric point: the map of sheaves `Λ_Z ⟶ 𝓗⁰(Ri^! Λ_X(c)[2c])` induced by `cl_i` is an
isomorphism. -/
theorem isIso_homology_zero_map_fundamentalClassMap (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map (fundamentalClassMap Λ c i aX hZ)) :=
  sorry

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

**(c) `cl_i` is an isomorphism**, `cl_i : Λ_Z ≅ Ri^! (Λ_X(c)[2c])`, `1 ↦ [Z ⊂ X]`.

It equals the isomorphism `Φ_i` assembled from smooth purity of `a_X` and `a_Z` in Steps 1–2
of the proof (`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_of_isRegularImmersion`).
That isomorphism is so far recorded only as `Nonempty`, so the agreement is a remark rather
than a statement. Twisting by `(-c)[-2c]`, the inverse of `cl_i(-c)[-2c]` is the canonical
isomorphism `Ri^! Λ_X ≅ Λ_Z(-c)[-2c]`. -/
theorem isIso_fundamentalClassMap (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    IsIso (fundamentalClassMap Λ c i aX hZ) :=
  sorry

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

**(d) Étale base change**, `[Z_{X'} ⊂ X'] = [Z ⊂ X]|_{X'}`: for an étale `e : X' ⟶ X` and the
base change `i' : Z' ⟶ X'` of `i`, the restriction of supports along `e`
(`AlgebraicGeometry.Etale.restrictSupportedClass`) carries the fundamental class of `i` to that
of `i'`. An étale map pulls frames back to frames and frame classes to frame classes.

The hypotheses on the base change are derived: `i'` is a regular immersion of codimension `c`
by flat base change, `e ≫ aX` is smooth, the exponent of `Λ` is invertible on `X'`, and `Z'`
is regular, being étale over `Z`. -/
theorem restrictSupportedClass_fundamentalClass (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) {X' Z' : Scheme.{u}} (e : X' ⟶ X)
    [AlgebraicGeometry.Etale e] (i' : Z' ⟶ X') (g : Z' ⟶ Z) (hg : IsPullback g i' i e) :
    haveI := IsRegularImmersion.of_isPullback c hg
    haveI : HasInvertibleExponent Λ X' := .of_hom e
    restrictSupportedClass (ModuleCat.{u + 1} Λ) e i i' g hg
        (leftDerivedUpperStarConstantComplexIso Λ e).inv (leftDerivedUpperStarTateShiftIso Λ e c)
        (fundamentalClass Λ c i aX hZ) =
      fundamentalClass Λ c i' (e ≫ aX)
        (haveI : AlgebraicGeometry.Etale g :=
          MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale) hg.flip inferInstance
        isRegularLocalRing_stalk_of_etale g hZ) := by
  have := IsRegularImmersion.of_isPullback c hg
  have : HasInvertibleExponent Λ X' := .of_hom e
  have : AlgebraicGeometry.Etale g :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale) hg.flip inferInstance
  refine eq_of_frameRestriction_eq Λ c i' (e ≫ aX) (isRegularLocalRing_stalk_of_etale g hZ)
    fun F _ ↦ ?_
  rw [frameRestriction_fundamentalClass]
  have h : restrictSupportedClass (ModuleCat.{u + 1} Λ) (F.e ≫ e) i _ (F.toZ ≫ g)
      (F.isPullback.paste_horiz hg) (leftDerivedUpperStarConstantComplexIso Λ (F.e ≫ e)).inv
      (leftDerivedUpperStarTateShiftIso Λ (F.e ≫ e) c) (fundamentalClass Λ c i aX hZ) =
        frameClass Λ F :=
    frameRestriction_fundamentalClass Λ c i aX hZ (Scheme.Hom.EtaleFrame.ofIsPullback hg F)
  rw [leftDerivedUpperStarConstantComplexIso_comp Λ F.e e _ rfl,
    leftDerivedUpperStarTateShiftIso_comp Λ F.e e _ rfl] at h
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] at h
  rw [restrictSupportedClass_restrictSupportedClass (ModuleCat.{u + 1} Λ) e F.e (F.e ≫ e) rfl i
    i' _ g hg F.toZ F.isPullback (F.toZ ≫ g) (F.isPullback.paste_horiz hg)] at h
  exact h

end FundamentalClass

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

**(d) Exterior products**,
`[Z₁ × Z₂ ⊂ X₁ × X₂] = [Z₁ ⊂ X₁] ⊠ [Z₂ ⊂ X₂]`. Let `(X₁, Z₁)` and `(X₂, Z₂)` be pairs as in the
theorem over the same perfect field `k`, of codimensions `c₁` and `c₂`, let
`P = X₁ ×_k X₂` with projections `p₁`, `p₂`, let `Z₁ ×_k X₂ ⟶ P` and `X₁ ×_k Z₂ ⟶ P` be the base
changes of `i₁` and `i₂` along them, and `i₁₂ : Z₁ ×_k Z₂ ⟶ P` the product of `i₁` and `i₂`, the
closed immersion of their intersection. Then the fundamental class of `i₁₂` is the cup product
with supports of the restrictions `p₁^* [Z₁ ⊂ X₁]` and `p₂^* [Z₂ ⊂ X₂]`: frames `f` on `U₁` and
`g` on `U₂` give the frame `(p₁^* f, p₂^* g)` on `U₁ ×_k U₂`, and cup products with supports are
natural and associative (no signs, all degrees even).

The hypotheses on the product are derived: `i₁₂` is a regular immersion of codimension
`c₁ + c₂` (`AlgebraicGeometry.IsRegularImmersion.pullback_map`), `Z₁ ×_k Z₂` is regular
(`AlgebraicGeometry.isRegularLocalRing_stalk_pullback`), `P` is smooth over `k` and the exponent
of `Λ` is invertible on `P`. -/
theorem fundamentalClass_eq_cupWithSupportsTateObject [Finite Λ] [HasKummerClass Λ]
    [HasKummerClass.IsNormalized Λ] {k : Type u} [Field k] [PerfectField k]
    {X₁ X₂ Z₁ Z₂ : Scheme.{u}} (c₁ c₂ : ℕ)
    (i₁ : Z₁ ⟶ X₁) (i₂ : Z₂ ⟶ X₂) [IsRegularImmersion c₁ i₁] [IsRegularImmersion c₂ i₂]
    (a₁ : X₁ ⟶ Spec (.of k)) (a₂ : X₂ ⟶ Spec (.of k)) [Smooth a₁] [Smooth a₂]
    [HasInvertibleExponent Λ X₁] [HasInvertibleExponent Λ X₂]
    (hZ₁ : ∀ z : Z₁, IsRegularLocalRing (Z₁.presheaf.stalk z))
    (hZ₂ : ∀ z : Z₂, IsRegularLocalRing (Z₂.presheaf.stalk z)) :
    haveI := IsRegularImmersion.pullback_map c₁ c₂ i₁ i₂ a₁ a₂
    haveI : HasInvertibleExponent Λ (pullback a₁ a₂) := .of_hom (pullback.fst a₁ a₂)
    fundamentalClass Λ (c₁ + c₂) (pullback.map (i₁ ≫ a₁) (i₂ ≫ a₂) a₁ a₂ i₁ i₂ (𝟙 _)
        (by simp) (by simp)) (pullback.fst a₁ a₂ ≫ a₁)
        (isRegularLocalRing_stalk_pullback (i₁ ≫ a₁) (i₂ ≫ a₂) hZ₁ hZ₂) =
      cupWithSupportsTateObject Λ (pullback.snd i₁ (pullback.fst a₁ a₂))
        (pullback.snd i₂ (pullback.snd a₁ a₂))
        (pullback.map (i₁ ≫ a₁) (i₂ ≫ a₂) a₁ a₂ i₁ i₂ (𝟙 _) (by simp) (by simp))
        (Scheme.Pullback.range_map_eq_inter _ _ _ _ _ _ _)
        (restrictSupportedClass (ModuleCat.{u + 1} Λ) (pullback.fst a₁ a₂) i₁ _ _
          (IsPullback.of_hasPullback _ _)
          (leftDerivedUpperStarConstantComplexIso Λ _).inv
          (leftDerivedUpperStarTateShiftIso Λ _ c₁) (fundamentalClass Λ c₁ i₁ a₁ hZ₁))
        (restrictSupportedClass (ModuleCat.{u + 1} Λ) (pullback.snd a₁ a₂) i₂ _ _
          (IsPullback.of_hasPullback _ _)
          (leftDerivedUpperStarConstantComplexIso Λ _).inv
          (leftDerivedUpperStarTateShiftIso Λ _ c₂) (fundamentalClass Λ c₂ i₂ a₂ hZ₂)) ≫
        eqToHom (by rw [Nat.cast_add]) :=
  sorry

end Etale

end AlgebraicGeometry
