/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.Affine
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceAdjunction
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso

/-!
# `𝔸¹ ⇒ 𝔸ⁿ`: the model purity

Let `B` be a scheme on which the exponent of the finite coefficient ring `Λ` is invertible,
`p_c : 𝔸^c_B → B` the projection and `z : B ↪ 𝔸^c_B` the zero section. This file proves the
two forms of the model purity of blueprint `sk-prop-an` by iterating the affine line:

* the `Rz^!`-form (clause (i)): `Rz^! Λ(c)[2c] ≅ Λ_B`;
* the `Rp_c^!`-form (clause (ii)): `Rp_c^! K ≅ Lp_c^* K (c)[2c]` for `K ∈ D^b_{ctf}(B, Λ)`.

Both proofs write `𝔸^{c+1}_B = 𝔸¹_{B'}` with `B' = 𝔸^c_B`
(`AlgebraicGeometry.AffineSpace.sumIso`), under which the zero section of `𝔸^{c+1}_B` is the
composite of the zero sections of `𝔸^c_B` and of `𝔸¹_{B'}`, and the projection is the
composite of the projections. The composition law for `R(-)^!`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp`) reduces each step to the
affine line, where the input is `sk-prop-a1` (for clause (i)) and affine-line purity
(`thm-pur-affine-line-purity`, for clause (ii)). For clause (i) the twist pulled back from
`B'` is moved through `Rs'^!` by the co-projection formula for the closed immersion `s'`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineSpaceZero`: clause (i),
  `Rz^! Λ(c)[2c] ≅ Λ_B`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineLine`: affine-line purity,
  `Rp^! K ≅ Lp^* K (1)[2]`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineSpace`: clause (ii),
  affine-space purity `Rp_c^! K ≅ Lp_c^* K (c)[2c]`.
- `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_affineSpace`: its case `K = Λ_B`,
  `ω_{p_c} ≅ Λ(c)[2c]`.
- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_affineSpace`: the section invariant of
  the standard pair, `𝒞(𝔸^c_B → B, 0) ≅ Λ_B(c)[2c]`.

## Implementation notes

The comparison maps of the blueprint — the Thom class `th`, the integration map `∫_π` and its
transpose `γ_{π,K}` — are not constructed: the projective-line trace and the Kummer boundary
with supports they are built from are not available. The isomorphisms are therefore recorded
as `Nonempty (_ ≅ _)`, and the normalization (iii), the composition law and the
compatibilities of `γ`, which are statements about these maps, are not stated. The
vector-bundle forms are not stated either, Mathlib having no vector bundles over a scheme.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

/-! ### Twists of pulled-back objects -/

section Twists

variable {X Y : Scheme.{u}} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

/-- `Λ_X(m)[2m] = (Λ_X ⊗^L Λ_X(m))[2m] ≅ Λ_X(m)[2m]`, through the left unitor. -/
noncomputable def twistShiftConstantComplexIso (X : Scheme.{u}) (m : ℤ) :
    (twistShift Λ X m).obj (constantComplex Λ X) ≅ (tateObject Λ X m)⟦2 * m⟧ :=
  (shiftFunctor _ (2 * m)).mapIso (derivedTensorLeftUnitor _ X _)

/-- The zero twist is trivial: `K(0)[0] ≅ K`. -/
noncomputable def twistShiftZeroIso (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    {m : ℤ} (hm : m = 0)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (twistShift Λ X m).obj K ≅ K :=
  (shiftFunctorZero' _ (2 * m) (by simp [hm])).app _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).mapIso
      (eqToIso (by rw [hm]; rfl) ≪≫ HasTateTwist.twistObjectZeroIso X) ≪≫
    derivedTensorRightUnitor _ X K

/-- Pullback commutes with twist-and-shift, `Lf^*(K(m)[2m]) ≅ (Lf^* K)(m)[2m]`. -/
noncomputable def leftDerivedUpperStarTwistShiftIso (f : X ⟶ Y) (m : ℤ)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).obj ((twistShift Λ Y m).obj K) ≅
      (twistShift Λ X m).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  ((L((f)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * m)).app _ ≪≫
    (shiftFunctor _ (2 * m)).mapIso
      (leftDerivedUpperStarTensorIso _ f K (tateObject Λ Y m) ≪≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj _).mapIso
          (leftDerivedUpperStarTateObjectIso f m))

/-- Twist-and-shifts compose additively, `(K(m)[2m])(m')[2m'] ≅ K(m + m')[2(m + m')]`. All
shifts are even, so no sign is involved. -/
noncomputable def twistShiftTwistShiftIso (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    (m m' : ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (twistShift Λ X m').obj ((twistShift Λ X m).obj K) ≅ (twistShift Λ X (m + m')).obj K :=
  (shiftFunctor _ (2 * m')).mapIso
      ((((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj (tateObject Λ X m')).commShiftIso
        (2 * m)).app _) ≪≫
    ((shiftFunctorAdd' _ (2 * m) (2 * m') (2 * (m + m')) (by ring)).app _).symm ≪≫
    (shiftFunctor _ (2 * (m + m'))).mapIso
      (derivedTensorAssociator _ X _ _ _ ≪≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).mapIso
          (HasTateTwist.twistObjectAddIso X m m'))

omit [HasInvertibleExponent Λ Y] in
/-- `Lf^* K (m)[2m]` lies in `D^b_{ctf}` when `K` does. -/
theorem boundedConstructibleFiniteTor_twistShift_leftDerivedUpperStar (f : X ⟶ Y) (m : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    DerivedCategory.boundedConstructibleFiniteTor Λ X
      ((twistShift Λ X m).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) :=
  DerivedCategory.boundedConstructibleFiniteTor.shift
    (constructibleFiniteTor_tensor _ X (constructibleFiniteTor_leftDerivedUpperStar _ f hK)
      (boundedConstructibleFiniteTor_tateObject Λ X m)) _

end Twists

/-! ### The `Rz^!`-form -/

/-- Blueprint `sk-prop-an`, Step 1: twists pulled back from the base pass through the zero
section `s : Y ↪ 𝔸¹_Y`. With `Λ(1 + m)[2(1 + m)] = Λ(1)[2] ⊗ Λ(m)[2m]`, the co-projection
formula for the closed immersion `s` and `Rs^! Λ(1)[2] ≅ Λ_Y` (`sk-prop-a1`),

`Rs^! Λ_{𝔸¹_Y}(1 + m)[2(1 + m)] ≅ Rs^! Λ(1)[2] ⊗ Ls^* Λ(m)[2m] ≅ Λ_Y(m)[2m]`. -/
theorem nonempty_iso_rightDerivedUpperShriek_affineLineZero_shiftTateObject
    [HasTateTwist.IsNormalized Λ]
    (Y : Scheme.{u}) {k : Type u} [Field k] (aY : Y ⟶ Spec (.of k)) [IsSeparated aY]
    [LocallyOfFiniteType aY] [HasInvertibleExponent Λ Y] (m : ℤ) :
    Nonempty ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ)
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).obj
        ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) (1 + m))⟦2 * (1 + m)⟧) ≅
      (tateObject Λ Y m)⟦2 * m⟧) := by
  obtain ⟨a1⟩ := nonempty_iso_rightDerivedUpperShriek_affineLineZero Λ aY
  obtain ⟨cop⟩ := nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible Λ
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)
    ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦2 * (1 : ℤ)⟧)
    ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) m)⟦2 * m⟧)
    ((boundedConstructibleFiniteTor_tateObject Λ _ 1).shift _)
    ((boundedConstructibleFiniteTor_tateObject Λ _ m).shift _)
    ((isInvertible_tateObject Λ _ m).shift _)
  exact ⟨(R(AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)^![ModuleCat.{u + 1} Λ]).mapIso
      (shiftTateObjectAddIso Λ _ 1 m).symm ≪≫ cop ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) Y).mapIso
      ((R(AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)^![ModuleCat.{u + 1} Λ]).mapIso
        (twistShiftConstantComplexIso Λ _ 1).symm ≪≫ a1)).app _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj _).mapIso
      (leftDerivedUpperStarTateShiftIso Λ _ m) ≪≫ derivedTensorLeftUnitor _ Y _⟩

/-- The identification `𝔸^{c+1}_B ≅ 𝔸¹_{𝔸^c_B}` of `AlgebraicGeometry.AffineSpace.sumIso`,
the last coordinate becoming the coordinate of the affine line. -/
noncomputable def affineSpaceSuccIso (c : ℕ) (B : Scheme.{u}) :
    𝔸(ULift.{u} (Fin (c + 1)); B) ≅ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin c); B)) :=
  AffineSpace.reindexIso B
      ((Equiv.sumCongr Equiv.ulift Equiv.ulift).trans (finSumFinEquiv.trans Equiv.ulift.symm)) ≪≫
    AffineSpace.sumIso B

@[reassoc (attr := simp)]
lemma zeroSection_comp_affineSpaceSuccIso_hom (c : ℕ) (B : Scheme.{u}) :
    AffineSpace.zeroSection (ULift.{u} (Fin (c + 1))) B ≫ (affineSpaceSuccIso c B).hom =
      AffineSpace.zeroSection (ULift.{u} (Fin c)) B ≫
        AffineSpace.zeroSection (ULift.{u} (Fin 1)) 𝔸(ULift.{u} (Fin c); B) := by
  simp [affineSpaceSuccIso]

@[reassoc (attr := simp)]
lemma affineSpaceSuccIso_hom_over_over (c : ℕ) (B : Scheme.{u}) :
    (affineSpaceSuccIso c B).hom ≫
        𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin c); B)) ↘ 𝔸(ULift.{u} (Fin c); B) ≫
          𝔸(ULift.{u} (Fin c); B) ↘ B = 𝔸(ULift.{u} (Fin (c + 1)); B) ↘ B := by
  rw [affineSpaceSuccIso, Iso.trans_hom, Category.assoc, AffineSpace.sumIso_hom_over_over,
    AffineSpace.reindexIso_hom, AffineSpace.reindex_over]

/-- Blueprint `sk-prop-an`, Step 1: the zero section of `𝔸^{c+1}_B` is that of `𝔸¹_{B'}`
after that of `B' = 𝔸^c_B`, so by the composition law
`Rz_{c+1}^! Λ(c+1)[2(c+1)] ≅ Rz_c^! Rs'^! Λ(1 + c)[2(1 + c)]`. -/
theorem nonempty_iso_rightDerivedUpperShriek_affineSpaceZero_succ (c : ℕ) (B : Scheme.{u})
    [HasInvertibleExponent Λ B] :
    Nonempty ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ)
          (AffineSpace.zeroSection (ULift.{u} (Fin (c + 1))) B)).obj
        ((tateObject Λ 𝔸(ULift.{u} (Fin (c + 1)); B) ((c + 1 : ℕ) : ℤ))⟦2 * ((c + 1 : ℕ) : ℤ)⟧) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ)
          (AffineSpace.zeroSection (ULift.{u} (Fin c)) B)).obj
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ)
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) 𝔸(ULift.{u} (Fin c); B))).obj
          ((tateObject Λ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin c); B)) (1 + (c : ℤ)))⟦
            2 * (1 + (c : ℤ))⟧))) := by
  set φ := affineSpaceSuccIso c B
  obtain ⟨comp₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ
    (AffineSpace.zeroSection (ULift.{u} (Fin (c + 1))) B) φ.hom
  obtain ⟨heq⟩ := nonempty_iso_rightDerivedUpperShriek_of_eq (ModuleCat.{u + 1} Λ)
    (zeroSection_comp_affineSpaceSuccIso_hom c B)
  obtain ⟨comp₂⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ
    (AffineSpace.zeroSection (ULift.{u} (Fin c)) B)
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) 𝔸(ULift.{u} (Fin c); B))
  exact ⟨(R(AffineSpace.zeroSection (ULift.{u} (Fin (c + 1))) B)^![ModuleCat.{u + 1} Λ]).mapIso
      ((leftDerivedUpperStarTateShiftIso Λ φ.hom _).symm ≪≫
        (rightDerivedUpperShriekIsoOfIso _ φ).symm.app _) ≪≫
    comp₁.symm.app _ ≪≫ heq.app _ ≪≫ comp₂.app _ ≪≫
    (R(AffineSpace.zeroSection (ULift.{u} (Fin c)) B)^![ModuleCat.{u + 1} Λ]).mapIso
      ((R(AffineSpace.zeroSection (ULift.{u} (Fin 1)) _)^![ModuleCat.{u + 1} Λ]).mapIso
        (eqToIso (congrArg (fun m : ℤ ↦ (tateObject Λ _ m)⟦2 * m⟧)
          (show ((c + 1 : ℕ) : ℤ) = 1 + c by push_cast; ring))))⟩

/-- The `Rz^!`-form of the model purity with the twisting object in place of the twisted
constant complex: `Rz^! Λ(c)[2c] ≅ Λ_B`, by induction on `c` (`sk-prop-an`, Step 1). -/
theorem nonempty_iso_rightDerivedUpperShriek_affineSpaceZero_shiftTateObject
    [HasTateTwist.IsNormalized Λ] {k : Type u} [Field k] (c : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ B] :
    Nonempty ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ)
          (AffineSpace.zeroSection (ULift.{u} (Fin c)) B)).obj
        ((tateObject Λ 𝔸(ULift.{u} (Fin c); B) c)⟦2 * (c : ℤ)⟧) ≅ constantComplex Λ B) := by
  induction c with
  | zero =>
    let e := asIso (𝔸(ULift.{u} (Fin 0); B) ↘ B)
    have hz : AffineSpace.zeroSection (ULift.{u} (Fin 0)) B = e.symm.hom := by
      rw [← cancel_mono e.hom]
      simp [e]
    obtain ⟨i⟩ := nonempty_iso_rightDerivedUpperShriek_of_eq (ModuleCat.{u + 1} Λ) hz
    exact ⟨i.app _ ≪≫ (rightDerivedUpperShriekIsoOfIso _ e.symm).app _ ≪≫
      leftDerivedUpperStarTateShiftIso Λ _ _ ≪≫
      (shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _ ≪≫
      eqToIso (by simp [tateObject]) ≪≫ HasTateTwist.twistObjectZeroIso B⟩
  | succ c ih =>
    obtain ⟨ih⟩ := ih
    obtain ⟨t⟩ := nonempty_iso_rightDerivedUpperShriek_affineSpaceZero_succ Λ c B
    obtain ⟨w⟩ :=
      nonempty_iso_rightDerivedUpperShriek_affineLineZero_shiftTateObject Λ
        𝔸(ULift.{u} (Fin c); B) (𝔸(ULift.{u} (Fin c); B) ↘ B ≫ aB) c
    exact ⟨t ≪≫
      (R(AffineSpace.zeroSection (ULift.{u} (Fin c)) B)^![ModuleCat.{u + 1} Λ]).mapIso w ≪≫ ih⟩

/-- Blueprint `sk-prop-an`: `𝔸¹ ⇒ 𝔸ⁿ`: the model purity

**(i) The `Rz^!`-form.** For the zero section `z : B ↪ 𝔸^c_B` of relative affine `c`-space,

`Rz^! Λ(c)[2c] ≅ Λ_B`,

i.e. `Rz^! Λ ≅ Λ_B(-c)[-2c]`. This is also the isomorphism of blueprint
`cor-pur-affine-space-zero-section-purity`; its normalization by the product of the Kummer
boundaries of the coordinates is not stated, the Kummer boundary with supports being
unavailable (see the implementation notes).

The proof is Step 1 of the blueprint: write `𝔸^c_B = 𝔸¹_{B'}` with `B' = 𝔸^{c-1}_B`, so that
`z = s' ∘ z_{c-1}` and `Rz^! ≅ Rz_{c-1}^! Rs'^!`; pass the twist pulled back from `B'` through
`Rs'^!` and conclude by `sk-prop-a1` and induction on `c`. -/
theorem nonempty_iso_rightDerivedUpperShriek_affineSpaceZero [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k] (c : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ B] :
    Nonempty ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ)
          (AffineSpace.zeroSection (ULift.{u} (Fin c)) B)).obj
        ((twistShift Λ 𝔸(ULift.{u} (Fin c); B) c).obj
          (constantComplex Λ 𝔸(ULift.{u} (Fin c); B))) ≅
      constantComplex Λ B) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_affineSpaceZero_shiftTateObject Λ c B aB
  exact ⟨(R(AffineSpace.zeroSection (ULift.{u} (Fin c)) B)^![ModuleCat.{u + 1} Λ]).mapIso
    (twistShiftConstantComplexIso Λ _ c) ≪≫ e⟩

/-! ### The `Rp^!`-form -/

/-- Blueprint `thm-pur-affine-line-purity`: affine-line purity

For the projection `p : 𝔸¹_Y → Y` of the affine line over a separated scheme of finite type
over a field, on which the exponent of `Λ` is invertible, and `K ∈ D^b_{ctf}(Y, Λ)`,

`Rp^! K ≅ Lp^* K (1)[2]`.

In the blueprint the isomorphism is the comparison `γ_{p,K}`, the transpose under
`Rp_! ⊣ Rp^!` of the integration map built from the projective-line trace
(`def-pur-affine-line-purity-comparison`); this comparison is not constructed, so only the
existence of the isomorphism is recorded.

The proof follows the blueprint: `Rp^!` is by definition the right adjoint of `Rp_!`, and
`Rp_! ⊣ p^*(1)[2]` is the affine-space ambient adjunction
(`AlgebraicGeometry.Etale.nonempty_rightDerivedLowerShriek_adjunction_affineSpace`,
`cor-amb-affine-space-adjunction`), so the two right adjoints agree. In particular the
isomorphism holds for every `K`, constructible or not. -/
theorem nonempty_iso_rightDerivedUpperShriek_affineLine [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k]
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [HasInvertibleExponent Λ Y]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    Nonempty ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ)
          (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).obj K ≅
      (twistShift Λ 𝔸(ULift.{u} (Fin 1); Y) 1).obj
        ((L(((𝔸(ULift.{u} (Fin 1); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  obtain ⟨adj⟩ := nonempty_rightDerivedLowerShriek_adjunction_affineSpace Λ 1 Y
  exact ⟨((rightDerivedUpperShriekAdjunction _ _).rightAdjointUniq adj).app K⟩

omit [HasTateTwist Λ] in
/-- Blueprint `sk-prop-an`, Step 6: the projection of `𝔸^{d+1}_Y` is that of `𝔸¹_{Y'}`
followed by that of `Y' = 𝔸^d_Y`, so by the composition law and `Re^! ≅ Le^*` for the
isomorphism `e : 𝔸^{d+1}_Y ≅ 𝔸¹_{Y'}`, `Rp_{d+1}^! K ≅ Le^* Rp'^! Rp_d^! K`. -/
theorem nonempty_iso_rightDerivedUpperShriek_affineSpace_succ (d : ℕ) (Y : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ)
          (𝔸(ULift.{u} (Fin (d + 1)); Y) ↘ Y)).obj K ≅
      (L(((affineSpaceSuccIso d Y).hom)^*[ModuleCat.{u + 1} Λ])).obj
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ)
          (𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); Y)) ↘ 𝔸(ULift.{u} (Fin d); Y))).obj
          ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ)
            (𝔸(ULift.{u} (Fin d); Y) ↘ Y)).obj K))) := by
  set φ := affineSpaceSuccIso d Y
  set q := 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); Y)) ↘ 𝔸(ULift.{u} (Fin d); Y)
  set p := 𝔸(ULift.{u} (Fin d); Y) ↘ Y
  have : HasCompactification (φ.hom ≫ q) := HasCompactification.comp_of_isOpenImmersion q φ.hom
  have h : 𝔸(ULift.{u} (Fin (d + 1)); Y) ↘ Y = (φ.hom ≫ q) ≫ p := by
    rw [Category.assoc]
    exact (affineSpaceSuccIso_hom_over_over d Y).symm
  have : HasCompactification ((φ.hom ≫ q) ≫ p) := .of_eq h
  obtain ⟨heq⟩ := nonempty_iso_rightDerivedUpperShriek_of_eq (ModuleCat.{u + 1} Λ) h
  obtain ⟨comp₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ
    (φ.hom ≫ q) p
  obtain ⟨comp₂⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ φ.hom q
  exact ⟨heq.app K ≪≫ comp₁.app K ≪≫ comp₂.app _ ≪≫ (rightDerivedUpperShriekIsoOfIso _ φ).app _⟩

omit [Finite Λ] in
/-- Blueprint `sk-prop-an`, Step 6: the twists of the two steps add up,

`Le^* ((Lp'^* (Lp_d^* K (d)[2d]))(1)[2]) ≅ Lp_{d+1}^* K (d + 1)[2(d + 1)]`. -/
theorem nonempty_iso_leftDerivedUpperStar_affineSpaceSuccIso_twistShift (d : ℕ)
    (Y : Scheme.{u}) [HasInvertibleExponent Λ Y]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((L(((affineSpaceSuccIso d Y).hom)^*[ModuleCat.{u + 1} Λ])).obj
        ((twistShift Λ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); Y)) 1).obj
          ((L(((𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); Y)) ↘
            𝔸(ULift.{u} (Fin d); Y)))^*[ModuleCat.{u + 1} Λ])).obj
            ((twistShift Λ 𝔸(ULift.{u} (Fin d); Y) d).obj
              ((L(((𝔸(ULift.{u} (Fin d); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).obj K)))) ≅
      (twistShift Λ 𝔸(ULift.{u} (Fin (d + 1)); Y) (d + 1 : ℕ)).obj
        ((L(((𝔸(ULift.{u} (Fin (d + 1)); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  set φ := affineSpaceSuccIso d Y
  set q := 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); Y)) ↘ 𝔸(ULift.{u} (Fin d); Y)
  set p := 𝔸(ULift.{u} (Fin d); Y) ↘ Y
  have h : 𝔸(ULift.{u} (Fin (d + 1)); Y) ↘ Y = φ.hom ≫ q ≫ p :=
    (affineSpaceSuccIso_hom_over_over d Y).symm
  -- the pullbacks compose: `Le^* Lq^* Lp^* ≅ L(e ≫ q ≫ p)^*`
  let pb : (L((φ.hom)^*[ModuleCat.{u + 1} Λ])).obj ((L((q)^*[ModuleCat.{u + 1} Λ])).obj
        ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K)) ≅
      (L(((𝔸(ULift.{u} (Fin (d + 1)); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).obj K :=
    (L((φ.hom)^*[ModuleCat.{u + 1} Λ])).mapIso
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) q p).app K).symm ≪≫
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) φ.hom (q ≫ p)
        (𝔸(ULift.{u} (Fin (d + 1)); Y) ↘ Y) h).app K).symm
  exact ⟨leftDerivedUpperStarTwistShiftIso Λ φ.hom 1 _ ≪≫
    (twistShift Λ _ 1).mapIso ((L((φ.hom)^*[ModuleCat.{u + 1} Λ])).mapIso
      (leftDerivedUpperStarTwistShiftIso Λ q d _) ≪≫
        leftDerivedUpperStarTwistShiftIso Λ φ.hom d _) ≪≫
    twistShiftTwistShiftIso Λ _ d 1 _ ≪≫
    (twistShift Λ _ _).mapIso pb ≪≫
    eqToIso (by push_cast; rfl)⟩

/-- Blueprint `cor-pur-affine-space-purity`: affine-space purity

This is clause (ii) of blueprint `sk-prop-an`. For the projection `p_d : 𝔸^d_Y → Y`, `d ≥ 0`,
of relative affine space over a separated scheme of finite type over a field, on which the
exponent of `Λ` is invertible, and `K ∈ D^b_{ctf}(Y, Λ)`,

`Rp_d^! K ≅ Lp_d^* K (d)[2d]`;

in particular `ω_{p_d} = Rp_d^! Λ_Y ≅ Λ(d)[2d]`. In the blueprint the isomorphism is the
comparison `γ_{p_d,K}` (`def-pur-affine-space-comparison`), the ordered composite of the
affine-line comparisons; these are not constructed, so only the existence of the isomorphism
is recorded.

The proof is Step 6 of the blueprint: write `𝔸^{d+1}_Y = 𝔸¹_{Y'}` with `Y' = 𝔸^d_Y`, apply
affine-line purity (`thm-pur-affine-line-purity`) over `Y'` to `Rp_d^! K ≅ Lp_d^* K (d)[2d]`,
which lies in `D^b_{ctf}`, and add up the twists. -/
theorem nonempty_iso_rightDerivedUpperShriek_affineSpace [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k] (d : ℕ)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [HasInvertibleExponent Λ Y]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    Nonempty ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ)
          (𝔸(ULift.{u} (Fin d); Y) ↘ Y)).obj K ≅
      (twistShift Λ 𝔸(ULift.{u} (Fin d); Y) d).obj
        ((L(((𝔸(ULift.{u} (Fin d); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  induction d with
  | zero =>
    let e := asIso (𝔸(ULift.{u} (Fin 0); Y) ↘ Y)
    exact ⟨(rightDerivedUpperShriekIsoOfIso _ e).app K ≪≫
      (twistShiftZeroIso Λ _ (by simp) _).symm⟩
  | succ d ih =>
    obtain ⟨ih⟩ := ih
    obtain ⟨t⟩ := nonempty_iso_rightDerivedUpperShriek_affineSpace_succ Λ d Y K
    obtain ⟨l⟩ := nonempty_iso_rightDerivedUpperShriek_affineLine Λ 𝔸(ULift.{u} (Fin d); Y)
      (𝔸(ULift.{u} (Fin d); Y) ↘ Y ≫ aY) _
      (boundedConstructibleFiniteTor_twistShift_leftDerivedUpperStar Λ _ d hK)
    obtain ⟨s⟩ := nonempty_iso_leftDerivedUpperStar_affineSpaceSuccIso_twistShift Λ d Y K
    exact ⟨t ≪≫ (L(((affineSpaceSuccIso d Y).hom)^*[ModuleCat.{u + 1} Λ])).mapIso
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) (𝔸(ULift.{u} (Fin 1);
        𝔸(ULift.{u} (Fin d); Y)) ↘ 𝔸(ULift.{u} (Fin d); Y))).mapIso ih ≪≫ l) ≪≫ s⟩

/-- Blueprint `cor-pur-affine-space-purity`: affine-space purity

*The dualizing complex.* For the projection `p_d : 𝔸^d_Y → Y` of relative affine space over
a separated scheme of finite type over a field, on which the exponent of `Λ` is invertible,

`ω_{p_d} = Rp_d^! Λ_Y ≅ Λ_{𝔸^d_Y}(d)[2d]`.

This is the case `K = Λ_Y` of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineSpace`, with
`Lp_d^* Λ_Y ≅ Λ_{𝔸^d_Y}`; `Λ_Y` lies in `D^b_{ctf}` as the twisting object `Λ_Y(0)`. -/
theorem nonempty_iso_dualizingComplex_affineSpace [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k] (d : ℕ)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [HasInvertibleExponent Λ Y] :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) (𝔸(ULift.{u} (Fin d); Y) ↘ Y) ≅
      (twistShift Λ 𝔸(ULift.{u} (Fin d); Y) d).obj
        (constantComplex Λ 𝔸(ULift.{u} (Fin d); Y))) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_affineSpace Λ d Y aY (tateObject Λ Y 0)
    (boundedConstructibleFiniteTor_tateObject Λ Y 0)
  exact ⟨(rightDerivedUpperShriek _ _).mapIso (HasTateTwist.twistObjectZeroIso Y).symm ≪≫ e ≪≫
    (twistShift Λ _ d).mapIso ((L(((𝔸(ULift.{u} (Fin d); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).mapIso
      (HasTateTwist.twistObjectZeroIso Y) ≪≫ leftDerivedUpperStarUnitIso _ _)⟩

/-- Blueprint `sk-thm-smooth-purity`: Finite-coefficient smooth purity

*Step 3, the standard pair.* For the projection `π : 𝔸^c_B ⟶ B` of a trivial vector bundle of
rank `c` with zero section `0`, over a separated scheme of finite type over a field, the
section invariant is the Tate twist:

`𝒞(π, 0) = L0^* ω_π ≅ L0^* Λ(c)[2c] ≅ Λ_B(c)[2c]`,

by affine-space purity (`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_affineSpace`)
and the compatibility of the twist with pullback. -/
theorem nonempty_iso_sectionInvariant_affineSpace [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k] (c : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ B] :
    Nonempty (sectionInvariant Λ (𝔸(ULift.{u} (Fin c); B) ↘ B)
        (AffineSpace.zeroSection (ULift.{u} (Fin c)) B) ≅
      (twistShift Λ B c).obj (constantComplex Λ B)) := by
  obtain ⟨e⟩ := nonempty_iso_dualizingComplex_affineSpace Λ c B aB
  exact ⟨(L((AffineSpace.zeroSection (ULift.{u} (Fin c)) B)^*[ModuleCat.{u + 1} Λ])).mapIso
      (e ≪≫ twistShiftConstantComplexIso Λ _ _) ≪≫
    leftDerivedUpperStarTateShiftIso Λ _ _ ≪≫ (twistShiftConstantComplexIso Λ B _).symm⟩

end Etale

end AlgebraicGeometry
