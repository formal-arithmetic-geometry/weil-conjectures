/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.TensorFormula
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# Cohomological smoothness and finite-coefficient smooth purity

The two central statements of the block. For `f : X ⟶ Y` smooth separated of pure relative
dimension `d` and a finite coefficient ring `Λ` whose exponent is invertible on `X`:

* *cohomological smoothness* (`sk-prop-cohsm`): the dualizing complex `ω_f = Rf^! Λ_Y` is
  ⊗-invertible, `Rf^! K ≅ Lf^* K ⊗^L ω_f` for every `K ∈ D^b_{ctf}(Y, Λ)`, and the formation
  of `Rf^!` commutes with base change;
* *smooth purity* (`sk-thm-smooth-purity`): `ω_f ≅ Λ_X(d)[2d]`, hence
  `Rf^! K ≅ Lf^* K(d)[2d]`.

The route is the blueprint's: the model case is affine-space purity
`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_affineSpace`, transported along the
deformation to the normal cone (`AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_normalCone`)
of the diagonal, a closed section of the first projection `X ×_Y X ⟶ X`.

## Implementation notes

The blueprint asserts that each isomorphism below is *canonical*: `sk-prop-cohsm` (b) is about
the mate `φ_K : Lf^* K ⊗ ω_f ⟶ Rf^! K` of the projection formula, and `sk-thm-smooth-purity`
about the normalized comparison. Neither map exists in the repository — the projection map
itself is a TODO of `WeilConjectures.SixFunctors.Etale.Derived.Exchange` — so each statement
records the existence of the isomorphism only, with a `TODO(unify)` marker. For the same
reason the smooth purity map `γ_{f,K}` and the smooth pullback exchange are built from their
constituent isomorphisms, which are arguments of the constructions.

The statements of `sk-prop-cohsm` carry `include d in`: their statements do not mention the
relative dimension `d`, and without it the hypothesis `[SmoothOfRelativeDimension d f]` would
silently be dropped.

## Main definitions

- `AlgebraicGeometry.Etale.twistShiftObjIso`: the twist reassociation
  `M(m)[2m] ≅ M ⊗ Λ_X(m)[2m]`.
- `AlgebraicGeometry.Etale.smoothPurityIso`: the smooth purity map
  `γ_{f,K} : Lf^* K(d)[2d] ≅ Rf^! K`.
- `AlgebraicGeometry.Etale.smoothPullbackExchange`: the smooth pullback exchange
  `Lg^* Rf^! K ≅ Rf'^! Lv^* K`.

## Main statements

- `AlgebraicGeometry.Etale.isInvertible_dualizingComplex`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_derivedTensor`
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek`
- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_diagonal`: `𝒞(p₁, Δ) ≅ ω_f`.
- `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`: `ω_f ≅ Λ_X(d)[2d]`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_twistShift`:
  `Rf^! K ≅ Lf^* K(d)[2d]`.
- `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_comp`: `ω_{g ≫ f} ≅ ω_g ⊗ Lg^* ω_f`.
- `AlgebraicGeometry.Etale.leftDerivedUpperStar_map_comp_smoothPullbackExchange_hom`: smooth
  base-change coherence.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {d : ℕ} (f : X ⟶ Y) [IsSeparated f] [SmoothOfRelativeDimension d f] [HasCompactification f]
  [HasInvertibleExponent Λ X]

include d in
/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

*Clause (a).* For `f` smooth separated of pure relative dimension `d` the dualizing complex
`ω_f = Rf^! Λ_Y` is ⊗-invertible: it is a lisse rank-one object, twisted and shifted. This is
the form of cohomological smoothness that does not yet name the twist; smooth purity
identifies `ω_f` with `Λ_X(d)[2d]`. -/
theorem isInvertible_dualizingComplex :
    DerivedCategory.isInvertible Λ X (dualizingComplex (ModuleCat.{u + 1} Λ) f) :=
  sorry

attribute [local instance] isIso_projectionMap_of_finite

include d in
/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

*Clause (b), the tensor formula.* This is clause (1) of blueprint
`thm-pur-cohomological-smoothness` and clause (2) of `def-pur-co-smoothness`. For `f` smooth
separated of pure relative dimension `d` and `K ∈ D^b_{ctf}(Y, Λ)`, the canonical map

`φ_K : ω_f ⊗^L Lf^* K ⟶ Rf^! K`

is an isomorphism. Here `φ` is `AlgebraicGeometry.Etale.dualizingComplexTensorMap`, the mate of
the projection formula with the counit of `Rf_! ⊣ Rf^!`. The blueprint writes its source as
`Lf^* K ⊗^L ω_f`; the projection formula puts `ω_f` on the left (see the implementation notes
of `WeilConjectures.SixFunctors.Etale.Derived.TensorFormula`). -/
theorem isIso_dualizingComplexTensorMap_app
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    IsIso ((dualizingComplexTensorMap (ModuleCat.{u + 1} Λ) f).app K) :=
  sorry

/-- The tensor formula `φ_K : ω_f ⊗^L Lf^* K ≅ Rf^! K` of `sk-prop-cohsm` (b) for
`K ∈ D^b_{ctf}(Y, Λ)`, as an isomorphism: the component at `K` of the canonical map
`AlgebraicGeometry.Etale.dualizingComplexTensorMap`, which is invertible by
`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_app`. -/
noncomputable def dualizingComplexTensorIso
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f)).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K :=
  have := isIso_dualizingComplexTensorMap_app Λ (d := d) f K hK
  asIso ((dualizingComplexTensorMap (ModuleCat.{u + 1} Λ) f).app K)

@[simp]
lemma dualizingComplexTensorIso_hom
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    (dualizingComplexTensorIso Λ (d := d) f K hK).hom =
      (dualizingComplexTensorMap (ModuleCat.{u + 1} Λ) f).app K :=
  rfl

include d in
/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

*Clause (b), the tensor formula, in the order of the blueprint.* For `f` smooth separated of
pure relative dimension `d` and `K ∈ D^b_{ctf}(Y, Λ)`,

`Rf^! K ≅ Lf^* K ⊗^L ω_f`.

It is the canonical map `AlgebraicGeometry.Etale.dualizingComplexTensorIso` composed with the
symmetry of `- ⊗^L -` (`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_flip`). -/
theorem nonempty_iso_rightDerivedUpperShriek_obj_derivedTensor
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
          (dualizingComplex (ModuleCat.{u + 1} Λ) f) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K) := by
  obtain ⟨σ⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) X
  exact ⟨(σ.app _).app _ ≪≫ dualizingComplexTensorIso Λ (d := d) f K hK⟩

include d in
/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

*Clause (c), smooth base change for `R^!`.* In the cartesian square

```
  X' --g'--> X          Rf^! ⋙ Lg'^*  ≅  Lg^* ⋙ Rf'^!
  |          |
  f'         f          as functors D(Y_ét, Λ) ⥤ D(X'_ét, Λ)
  |          |
  v          v
  Y' --g---> Y
```

with `f` smooth and `f'` its base change along `g`, the formation of `Rf^!` commutes with base
change. Applied to the diagonal square `W = X ×_Y X` this gives `ω_{p₁} ≅ Lp₂^* ω_f` and
`ω_{p₂} ≅ Lp₁^* ω_f`, which is what makes the diagonal computation of the purity theorem
possible. -/
theorem nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek {X' Y' : Scheme.{u}}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    [HasCompactification f'] :
    Nonempty (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f ⋙
        L((g')^*[ModuleCat.{u + 1} Λ]) ≅
      L((g)^*[ModuleCat.{u + 1} Λ]) ⋙
        rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f') :=
  sorry

/-! ### The twist reassociation and its compatibility with pullback -/

section Twist

variable (X) in
/-- Blueprint `def-coefficient-twists-detailed`: the twist reassociation

`M(m)[2m] = (M ⊗ Λ_X(m))[2m] ≅ M ⊗ Λ_X(m)[2m]`,

moving the shift into the twisting factor (`M ⊗ -` commutes with shifts) and reading
`Λ_X(m)[2m]` as the twist-and-shift of `Λ_X`. All shifts are even, so no sign occurs. -/
noncomputable def twistShiftObjIso (m : ℤ)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (twistShift Λ X m).obj M ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).obj
        ((twistShift Λ X m).obj (constantComplex Λ X)) :=
  ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).commShiftIso (2 * m)).app
      (tateObject Λ X m)).symm ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).mapIso (twistShiftConstantComplexIso Λ X m).symm

variable (X) in
omit [Finite Λ] [HasInvertibleExponent Λ X] in
/-- The twist reassociation `M(m)[2m] ≅ M ⊗ Λ_X(m)[2m]` is natural in `M`. This rests on the
naturality of the shift compatibility of `M ⊗ᴸ -` in the fixed factor `M`
(`AlgebraicGeometry.Etale.derivedTensor_map_app_comp_commShiftIso_hom_app`). -/
@[reassoc]
lemma twistShift_map_comp_twistShiftObjIso_hom (m : ℤ)
    {M M' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (g : M ⟶ M') :
    (twistShift Λ X m).map g ≫ (twistShiftObjIso Λ X m M').hom =
      (twistShiftObjIso Λ X m M).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).map g).app _ := by
  have h := derivedTensor_map_app_comp_commShiftIso_hom_app _ g (2 * m) (tateObject Λ X m)
  have h' : (((derivedTensor (ModuleCat.{u + 1} Λ) X).map g).app (tateObject Λ X m))⟦2 * m⟧' ≫
      ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M').commShiftIso (2 * m)).inv.app
        (tateObject Λ X m)) =
      ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).commShiftIso (2 * m)).inv.app
        (tateObject Λ X m)) ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).map g).app ((tateObject Λ X m)⟦2 * m⟧) := by
    rw [← cancel_epi ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).commShiftIso
      (2 * m)).hom.app (tateObject Λ X m)), Iso.hom_inv_id_app_assoc, ← reassoc_of% h,
      Iso.hom_inv_id_app]
    exact Category.comp_id _
  dsimp only [twistShiftObjIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
  rw [Category.assoc, NatTrans.naturality]
  exact (reassoc_of% h') _
end Twist

/-! ### The diagonal -/

include d in
/-- Blueprint `lem-pur-diagonal-base-change`: Base change for the dualizing object of a
projection

Let `W = X ×_Y X` with projections `p₁, p₂`. The square `p₂ ≫ f = p₁ ≫ f` is cartesian and
`p₁` is the base change of the smooth `f`, so smooth base change for `R^!` (`sk-prop-cohsm`
(c)) gives

`ω_{p₁} = Rp₁^! Λ_X ≅ Lp₂^* Rf^! Λ_Y = Lp₂^* ω_f`. -/
theorem nonempty_iso_dualizingComplex_pullbackFst :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) (pullback.fst f f) ≅
      (L((pullback.snd f f)^*[ModuleCat.{u + 1} Λ])).obj
        (dualizingComplex (ModuleCat.{u + 1} Λ) f)) := by
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek Λ (d := d) f
    (IsPullback.of_hasPullback f f).flip
  obtain ⟨ι⟩ := nonempty_iso_leftDerivedUpperStar_unit (ModuleCat.{u + 1} Λ) f
  exact ⟨(rightDerivedUpperShriek _ (pullback.fst f f)).mapIso ι.symm ≪≫ (e.app (𝟙_ _)).symm⟩

include d in
/-- Blueprint `lem-pur-diagonal-base-change`: Base change for the dualizing object of a
projection

The symmetric statement: `ω_{p₂} ≅ Lp₁^* ω_f`. -/
theorem nonempty_iso_dualizingComplex_pullbackSnd :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) (pullback.snd f f) ≅
      (L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ])).obj
        (dualizingComplex (ModuleCat.{u + 1} Λ) f)) := by
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek Λ (d := d) f
    (IsPullback.of_hasPullback f f)
  obtain ⟨ι⟩ := nonempty_iso_leftDerivedUpperStar_unit (ModuleCat.{u + 1} Λ) f
  exact ⟨(rightDerivedUpperShriek _ (pullback.snd f f)).mapIso ι.symm ≪≫ (e.app (𝟙_ _)).symm⟩

include d in
/-- Blueprint `lem-pur-diagonal-base-change`: Base change for the dualizing object of a
projection

The section invariant of the diagonal `Δ : X ⟶ X ×_Y X`, a closed section of `p₁`, is the
dualizing complex of `f`: since `Δ ≫ p₂ = 𝟙 X`,

`𝒞(p₁, Δ) = LΔ^* ω_{p₁} ≅ LΔ^* Lp₂^* ω_f ≅ L(𝟙 X)^* ω_f ≅ ω_f`. -/
theorem nonempty_iso_sectionInvariant_diagonal :
    Nonempty (sectionInvariant Λ (pullback.fst f f) (pullback.diagonal f) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) f) := by
  obtain ⟨e⟩ := nonempty_iso_dualizingComplex_pullbackFst Λ (d := d) f
  exact ⟨(L((pullback.diagonal f)^*[ModuleCat.{u + 1} Λ])).mapIso e ≪≫
    ((leftDerivedUpperStarComp _ (pullback.diagonal f) (pullback.snd f f) (𝟙 X)
      (pullback.diagonal_snd f).symm).app _).symm ≪≫
    (Functor.leftDerivedFunctorNatIso _ (Etale.upperStarId _ X) ≪≫
      (𝟭 _).leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _).app _⟩

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

/-- Blueprint `sk-thm-smooth-purity`: Finite-coefficient smooth purity

**Smooth purity, finite coefficients.** For `f : X ⟶ Y` smooth separated of pure relative
dimension `d`, `Y` separated of finite type over a field, and a finite coefficient ring `Λ`
whose exponent is invertible on `X`,

`ω_f = Rf^! Λ_Y ≅ Λ_X(d)[2d]`,

canonically, compatibly with base change and additively in the twist under composition of
smooth morphisms.

This is also blueprint `thm-pur-diagonal-dualizing-object`. The proof is the blueprint's
diagonal argument. Let `W = X ×_Y X` and `Δ : X ⟶ W` the diagonal, a closed section of the
smooth projection `p₁`.
1. `𝒞(p₁, Δ) ≅ ω_f` by smooth base change
   (`AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_diagonal`).
2. The deformation to the normal cone (`sk-thm-dnc`,
   `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_normalCone`) identifies `𝒞(p₁, Δ)`
   with the section invariant of a rank-`d` vector bundle with its zero section.
3. That section invariant is `Λ_X(d)[2d]` by affine-space purity
   (`AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_affineSpace`), which needs `X` of
   finite type over the field.

The normal bundle of `Δ` is the relative tangent bundle `T_{X/Y}`, which is étale-locally
trivial of rank `d` (`sk-lem-diag-reg`). Mathlib has neither vector bundles nor `T_{X/Y}`, so
the normal cone datum is recorded through `AlgebraicGeometry.Scheme.Hom.NormalConeData`, which
only asks for a smooth rank-`d` projection with a closed zero section; the trivial bundle
`𝔸^d_X` is used in step 2, for which step 3 is affine-space purity. -/
theorem nonempty_iso_dualizingComplex_twistShift [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k]
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY] :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X)) := by
  -- TODO: the normal cone datum of `Δ` should be its normal bundle `T_{X/Y}`, as in blueprint
  -- `thm-pur-dnc-invariance`, and step 3 vector-bundle purity for it. `NormalConeData` does not
  -- tie the datum to the immersion, so the trivial bundle `𝔸^d_X` is accepted here; undo this
  -- shortcut once the datum is pinned down.
  let N : (pullback.diagonal f).NormalConeData d :=
    { scheme := 𝔸(ULift.{u} (Fin d); X)
      proj := 𝔸(ULift.{u} (Fin d); X) ↘ X
      zeroSection := AffineSpace.zeroSection _ X
      zeroSection_comp_proj := AffineSpace.zeroSection_over _ X
      isClosedImmersion_zeroSection := inferInstance
      smoothOfRelativeDimension_proj := by
        have := AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) X
        rwa [show Nat.card (ULift.{u} (Fin d)) = d by simp] at this }
  have : HasCompactification N.proj := HasCompactification.affineSpace_over _ X
  obtain ⟨e₁⟩ := nonempty_iso_sectionInvariant_diagonal Λ (d := d) f
  obtain ⟨e₂⟩ := nonempty_iso_sectionInvariant_normalCone Λ d (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f) N
  obtain ⟨e₃⟩ := nonempty_iso_sectionInvariant_affineSpace Λ d X (f ≫ aY)
  exact ⟨e₁.symm ≪≫ e₂ ≪≫ e₃⟩

/-! ### The smooth purity map -/

variable (X) in
/-- A symmetry `K ⊗ᴸ M ≅ M ⊗ᴸ K` of the derived tensor product on `D(X_ét, Λ)`, natural in both
variables. The library only records that a symmetry exists
(`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_flip`), so one is chosen. -/
noncomputable def derivedTensorFlipIso :
    derivedTensor (ModuleCat.{u + 1} Λ) X ≅ (derivedTensor (ModuleCat.{u + 1} Λ) X).flip :=
  Classical.choice (nonempty_iso_derivedTensor_flip _ X)

/-- Blueprint `def-pur-smooth-purity-map`: Smooth purity map

For `f` smooth separated of pure relative dimension `d` and `K ∈ D^b_{ctf}(Y, Λ)`, the *smooth
purity map* is the composite

`γ_{f,K} : Lf^* K(d)[2d] ≅ Lf^* K ⊗ Λ_X(d)[2d] ≅ Lf^* K ⊗ ω_f ≅ Rf^! K`

of the twist reassociation (`AlgebraicGeometry.Etale.twistShiftObjIso`), the inverse of the
identification `θ : ω_f ≅ Λ_X(d)[2d]` of `thm-pur-diagonal-dualizing-object`, and the tensor
formula of `sk-prop-cohsm` (b). The tensor formula is the canonical map
`AlgebraicGeometry.Etale.dualizingComplexTensorIso`, which has `ω_f` as its left factor; it is
preceded by the symmetry `AlgebraicGeometry.Etale.derivedTensorFlipIso`.

The library only provides the existence of `θ`
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`), so `θ` is an argument
of the construction. -/
noncomputable def smoothPurityIso
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K)
    (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X)) :
    (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K :=
  twistShiftObjIso Λ X d _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).mapIso
      θ.symm ≪≫
    ((derivedTensorFlipIso Λ X).app _).app _ ≪≫ dualizingComplexTensorIso Λ (d := d) f K hK

/-- Blueprint `prop-pur-smooth-purity-naturality-cover`: Naturality and independence of the
smooth purity map

**Naturality.** The smooth purity map `γ_{f,K}` (`AlgebraicGeometry.Etale.smoothPurityIso`) is
natural in `K ∈ D^b_{ctf}(Y, Λ)`: for `g : K ⟶ K'` the square

```
Lf^* K(d)[2d] ──γ_{f,K}──▶ Rf^! K
      │                        │
Lf^* g(d)[2d]               Rf^! g
      ▼                        ▼
Lf^* K'(d)[2d] ─γ_{f,K'}─▶ Rf^! K'
```

commutes. Each step of the construction is natural: the twist reassociation, by the naturality
of the shift compatibility of `- ⊗ᴸ -` in the fixed factor; `𝟙 ⊗ θ⁻¹` and the symmetry, by
the functoriality of `- ⊗ᴸ -`; and the tensor formula, which is the component of the natural
transformation `AlgebraicGeometry.Etale.dualizingComplexTensorMap`. -/
@[reassoc]
theorem twistShift_map_comp_smoothPurityIso_hom
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K)
    (hK' : DerivedCategory.boundedConstructibleFiniteTor Λ Y K')
    (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X)) (g : K ⟶ K') :
    (twistShift Λ X d).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map g) ≫
        (smoothPurityIso Λ f K' hK' θ).hom =
      (smoothPurityIso Λ f K hK θ).hom ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).map g := by
  have hσ := congr_app ((derivedTensorFlipIso Λ X).hom.naturality
    ((L((f)^*[ModuleCat.{u + 1} Λ])).map g)) (dualizingComplex (ModuleCat.{u + 1} Λ) f)
  have hφ := (dualizingComplexTensorMap (ModuleCat.{u + 1} Λ) f).naturality g
  dsimp at hσ hφ
  simp only [smoothPurityIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    dualizingComplexTensorIso_hom, Category.assoc,
    twistShift_map_comp_twistShiftObjIso_hom_assoc]
  rw [← NatTrans.naturality_assoc, reassoc_of% hσ]
  exact congrArg (_ ≫ _ ≫ _ ≫ ·) hφ

/-- Blueprint `prop-pur-smooth-purity-naturality-cover`: Naturality and independence of the
smooth purity map

The smooth purity map as a natural isomorphism `Lf^*(-)(d)[2d] ≅ Rf^!` of functors on
`D^b_{ctf}(Y, Λ)`, with components `AlgebraicGeometry.Etale.smoothPurityIso`
(`AlgebraicGeometry.Etale.twistShift_map_comp_smoothPurityIso_hom`).

**Independence of choices.** The construction involves no choice besides the identification
`θ : ω_f ≅ Λ_X(d)[2d]` and the symmetry of `- ⊗ᴸ -`: the twist reassociation and the tensor
formula are canonical. In the blueprint `θ` is the unique identification normalized on the
standard pairs (`thm-pur-dnc-invariance`); that uniqueness is not available in the library
(see the implementation notes of `WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation`),
so `θ` is an argument, and the naturality holds for every `θ`. -/
noncomputable def smoothPurityNatIso
    (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X)) :
    (DerivedCategory.boundedConstructibleFiniteTor Λ Y).ι ⋙
        L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ X d ≅
      (DerivedCategory.boundedConstructibleFiniteTor Λ Y).ι ⋙
        rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f :=
  NatIso.ofComponents (fun K ↦ smoothPurityIso Λ f K.obj K.property θ)
    (fun _ ↦ twistShift_map_comp_smoothPurityIso_hom Λ f _ _ θ _)

@[simp]
lemma smoothPurityNatIso_hom_app
    (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X))
    (K : (DerivedCategory.boundedConstructibleFiniteTor Λ Y).FullSubcategory) :
    (smoothPurityNatIso Λ f θ).hom.app K = (smoothPurityIso Λ f K.obj K.property θ).hom :=
  rfl

/-- Blueprint `sk-thm-smooth-purity`: Finite-coefficient smooth purity

**The purity isomorphism on all coefficients.** Combining the tensor formula of
`sk-prop-cohsm` (b) with `ω_f ≅ Λ_X(d)[2d]`: for `f` smooth separated of pure relative
dimension `d` and every `K ∈ D^b_{ctf}(Y, Λ)`,

`Rf^! K ≅ (Lf^* K)(d)[2d]`.

This is also blueprint `thm-pur-finite-coefficient-smooth-purity` and
`cor-pur-dualizing-object-purity`: the isomorphism is the smooth purity map
`AlgebraicGeometry.Etale.smoothPurityIso`. -/
theorem nonempty_iso_rightDerivedUpperShriek_twistShift [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k]
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    Nonempty ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K ≅
      (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  obtain ⟨θ⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := d) f aY
  exact ⟨(smoothPurityIso Λ f K hK θ).symm⟩

include d in
/-- Blueprint `sk-thm-smooth-purity`: Finite-coefficient smooth purity

**Additivity of the dualizing complex under composition.** For composable smooth separated
morphisms `g : W ⟶ X` and `f : X ⟶ Y`,

`ω_{g ≫ f} ≅ ω_g ⊗^L Lg^* ω_f`,

which is the multiplicativity of the twist that `sk-thm-regular` divides one dualizing complex
into another with. This is the dualizing-object form of blueprint
`thm-pur-composition-coherence`. It is the twist additivity of smooth purity: if `g` has
relative dimension `e` and `f` relative dimension `d`, all three objects are Tate twists,
`ω_{g ≫ f} ≅ Λ_W(e + d)[2(e + d)]`, `ω_g ≅ Λ_W(e)[2e]` and `Lg^* ω_f ≅ Λ_W(d)[2d]`, and
`Λ_W(e)[2e] ⊗ Λ_W(d)[2d] ≅ Λ_W(e + d)[2(e + d)]`
(`AlgebraicGeometry.Etale.shiftTateObjectAddIso`). -/
theorem nonempty_iso_dualizingComplex_comp [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k] (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] {W : Scheme.{u}} {e : ℕ} (g : W ⟶ X)
    [IsSeparated g] [SmoothOfRelativeDimension e g] [HasCompactification g]
    [HasCompactification (g ≫ f)] [HasInvertibleExponent Λ W] :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) (g ≫ f) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) W).obj
          (dualizingComplex (ModuleCat.{u + 1} Λ) g)).obj
        ((L((g)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f))) := by
  obtain ⟨θ⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := e + d) (g ≫ f) aY
  obtain ⟨θg⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := e) g (f ≫ aY)
  obtain ⟨θf⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := d) f aY
  exact ⟨θ ≪≫ twistShiftConstantComplexIso Λ W _ ≪≫ eqToIso (by push_cast; rfl) ≪≫
    (shiftTateObjectAddIso Λ W e d).symm ≪≫
    ((derivedTensor _ W).mapIso (θg ≪≫ twistShiftConstantComplexIso Λ W e).symm).app _ ≪≫
    ((derivedTensor _ W).obj (dualizingComplex _ g)).mapIso
      ((L((g)^*[ModuleCat.{u + 1} Λ])).mapIso (θf ≪≫ twistShiftConstantComplexIso Λ X d) ≪≫
        leftDerivedUpperStarTateShiftIso Λ g d).symm⟩

/-! ### Base change -/

section BaseChange

variable {X' Y' : Scheme.{u}} {g : X' ⟶ X} {f' : X' ⟶ Y'} {v : Y' ⟶ Y}

variable (d) in
/-- The base-change identification of the source of the purity map: for a commutative square
`g ≫ f = f' ≫ v`,

`Lg^* (Lf^* K(d)[2d]) ≅ (Lg^* Lf^* K)(d)[2d] ≅ (Lf'^* Lv^* K)(d)[2d]`. -/
noncomputable def leftDerivedUpperStarTwistShiftBaseChangeIso (sq : CommSq g f' f v)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).obj
        ((twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ≅
      (twistShift Λ X' d).obj ((L((f')^*[ModuleCat.{u + 1} Λ])).obj
        ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K)) :=
  leftDerivedUpperStarTwistShiftIso Λ g d _ ≪≫ (twistShift Λ X' d).mapIso
    (((leftDerivedUpperStarComp _ g f (g ≫ f) rfl).app K).symm ≪≫
      (leftDerivedUpperStarComp _ f' v (g ≫ f) sq.w).app K)

variable [IsSeparated f'] [SmoothOfRelativeDimension d f'] [HasCompactification f']
  [HasInvertibleExponent Λ X']

omit [Finite Λ] [HasTateTwist Λ] [HasInvertibleExponent Λ X] in
/-- `Lv^* K` lies in `D^b_{ctf}` when `K` does. -/
theorem boundedConstructibleFiniteTor_leftDerivedUpperStar {Y' : Scheme.{u}} (v : Y' ⟶ Y)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    DerivedCategory.boundedConstructibleFiniteTor Λ Y' ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  constructibleFiniteTor_leftDerivedUpperStar _ v hK

/-- Blueprint `def-pur-smooth-pullback-exchange`: Smooth pullback exchange for exceptional
inverse image

For a cartesian square `g ≫ f = f' ≫ v` with `f` smooth of relative dimension `d` and
`K ∈ D^b_{ctf}(Y, Λ)`, the smooth pullback exchange is the composite

`Ex^{!,sm}_{f,v,K} : Lg^* Rf^! K ≅ Lg^* Lf^* K(d)[2d] ≅ Lf'^* Lv^* K(d)[2d] ≅ Rf'^! Lv^* K`

of the inverse of `Lg^* γ_{f,K}`, the base-change identification
`AlgebraicGeometry.Etale.leftDerivedUpperStarTwistShiftBaseChangeIso` and `γ_{f',Lv^* K}`,
where `γ` and `γ'` are the smooth purity maps of `f` and of `f'`
(`AlgebraicGeometry.Etale.smoothPurityIso`), built from the identifications `θ, θ'` of the
dualizing complexes. It is distinct from the mate of the compact-support base change. -/
noncomputable def smoothPullbackExchange (sq : IsPullback g f' f v)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K)
    (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X))
    (θ' : dualizingComplex (ModuleCat.{u + 1} Λ) f' ≅
      (twistShift Λ X' d).obj (constantComplex Λ X')) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f').obj
        ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  (L((g)^*[ModuleCat.{u + 1} Λ])).mapIso (smoothPurityIso Λ f K hK θ).symm ≪≫
    leftDerivedUpperStarTwistShiftBaseChangeIso Λ d f sq.toCommSq K ≪≫
      smoothPurityIso Λ f' _ (boundedConstructibleFiniteTor_leftDerivedUpperStar Λ v hK) θ'

/-- Blueprint `thm-pur-smooth-base-change-coherence`: Smooth base-change coherence

For a cartesian square `g ≫ f = f' ≫ v` with `f` smooth of relative dimension `d`, the pullback
of the purity isomorphism is the purity isomorphism of the base change: the square

```
Lg^* Lf^* K(d)[2d] ──Lg^* γ_{f,K}──▶ Lg^* Rf^! K
        │ ≅                              │ Ex^{!,sm}_{f,v,K}
        ▼                                ▼
Lf'^* Lv^* K(d)[2d] ──γ_{f',Lv^*K}──▶ Rf'^! Lv^* K
```

commutes. -/
theorem leftDerivedUpperStar_map_comp_smoothPullbackExchange_hom (sq : IsPullback g f' f v)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K)
    (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X))
    (θ' : dualizingComplex (ModuleCat.{u + 1} Λ) f' ≅
      (twistShift Λ X' d).obj (constantComplex Λ X')) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).map (smoothPurityIso Λ f K hK θ).hom ≫
        (smoothPullbackExchange Λ f sq K hK θ θ').hom =
      (leftDerivedUpperStarTwistShiftBaseChangeIso Λ d f sq.toCommSq K).hom ≫
        (smoothPurityIso Λ f' _ (boundedConstructibleFiniteTor_leftDerivedUpperStar Λ v hK)
          θ').hom := by
  simp [smoothPullbackExchange, ← Functor.map_comp_assoc]

end BaseChange

end Etale

end AlgebraicGeometry
