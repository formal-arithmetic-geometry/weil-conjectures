/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
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

The route is the blueprint's: the model case is the `𝔸ⁿ`-purity of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineSpaceZero`, transported
along the deformation to the normal cone of the diagonal, which is a regular immersion of
codimension `d` by `AlgebraicGeometry.isRegularImmersion_diagonal`.

## Implementation notes

The blueprint asserts that each isomorphism below is *canonical*: `sk-prop-cohsm` (b) is about
the mate `φ_K : Lf^* K ⊗ ω_f ⟶ Rf^! K` of the projection formula, and `sk-thm-smooth-purity`
about the normalized comparison. Neither map exists in the repository — the projection map
itself is a TODO of `WeilConjectures.SixFunctors.Etale.Derived.Exchange` — so each statement
records the existence of the isomorphism only, with a `TODO(unify)` marker.

## Main statements

- `AlgebraicGeometry.Etale.isInvertible_dualizingComplex`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_derivedTensor`
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek`
- `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_comp`
- `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_twistShift`
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

include d in
/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

*Clause (b), the tensor formula.* For `f` smooth separated of pure relative dimension `d` and
`K ∈ D^b_{ctf}(Y, Λ)`,

`Rf^! K ≅ Lf^* K ⊗^L ω_f`.

Equivalently, `Rf^!` is `Lf^*` twisted by the invertible object `ω_f` of clause (a); this is
what turns the computation of `ω_f` into a computation of `Rf^!` on all coefficients. The
blueprint statement is that the mate `φ_K` of the projection formula is this isomorphism. -/
-- TODO(unify): sk-prop-cohsm — state `IsIso φ_K` once the projection map is available.
theorem nonempty_iso_rightDerivedUpperShriek_obj_derivedTensor
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
          (dualizingComplex (ModuleCat.{u + 1} Λ) f) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K) :=
  sorry

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

include d in
/-- Blueprint `sk-thm-smooth-purity`: Finite-coefficient smooth purity

**Additivity of the dualizing complex under composition.** For composable smooth separated
morphisms `g : W ⟶ X` and `f : X ⟶ Y`,

`ω_{g ≫ f} ≅ ω_g ⊗^L Lg^* ω_f`,

which is the multiplicativity of the twist that `sk-thm-regular` divides one dualizing complex
into another with. It is the mate of the composition law `R(g ≫ f)^! ≅ Rf^! ⋙ Rg^!` of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp` applied to `Λ_Y`. -/
theorem nonempty_iso_dualizingComplex_comp {W : Scheme.{u}} {e : ℕ} (g : W ⟶ X)
    [IsSeparated g] [SmoothOfRelativeDimension e g] [HasCompactification g]
    [HasCompactification (g ≫ f)] [HasInvertibleExponent Λ W] :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) (g ≫ f) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) W).obj
          (dualizingComplex (ModuleCat.{u + 1} Λ) g)).obj
        ((L((g)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f))) :=
  sorry

/-! ### The twist reassociation and its compatibility with pullback -/

section Twist

variable (X) in
/-- The twist-and-shift of the constant complex is the shifted twisting object:
`Λ_X(m)[2m] = (Λ_X ⊗ Λ_X(m))[2m] ≅ Λ_X(m)[2m]`, by the left unitor
(`AlgebraicGeometry.Etale.derivedTensorLeftUnitor`). -/
noncomputable def twistShiftConstantComplexIso (m : ℤ) :
    (twistShift Λ X m).obj (constantComplex Λ X) ≅ (tateObject Λ X m)⟦2 * m⟧ :=
  (shiftFunctor _ (2 * m)).mapIso (derivedTensorLeftUnitor _ X (tateObject Λ X m))

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

/-- Blueprint `def-coefficient-twists-detailed`: the twist-and-shift commutes with pullback,

`Lg^*(M(m)[2m]) ≅ (Lg^* M)(m)[2m]`,

through the shift compatibility of `Lg^*`, its monoidal structure and the identification
`Lg^* Λ_X(m) ≅ Λ_{X'}(m)` of the Tate twist datum. -/
noncomputable def leftDerivedUpperStarTwistShiftIso {X' : Scheme.{u}} (g : X' ⟶ X) (m : ℤ)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((twistShift Λ X m).obj M) ≅
      (twistShift Λ X' m).obj ((L((g)^*[ModuleCat.{u + 1} Λ])).obj M) :=
  ((L((g)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * m)).app _ ≪≫
    (shiftFunctor _ (2 * m)).mapIso
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g M (tateObject Λ X m) ≪≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X').obj
          ((L((g)^*[ModuleCat.{u + 1} Λ])).obj M)).mapIso (leftDerivedUpperStarTateObjectIso g m))

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

*Step 3, the standard pair.* For the projection `π : 𝔸(n; B) ⟶ B` of a trivial vector bundle
of rank `c = #n` with zero section `0`, the section invariant is the Tate twist:

`𝒞(π, 0) = L0^* ω_π ≅ L0^* Λ(c)[2c] ≅ Λ_B(c)[2c]`,

by vector-bundle purity
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_affineSpace`) and the compatibility
of the twist with pullback. -/
theorem nonempty_iso_sectionInvariant_affineSpace (n : Type u) [Finite n] (B : Scheme.{u})
    [HasInvertibleExponent Λ B] :
    Nonempty (sectionInvariant Λ (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B) ≅
      (twistShift Λ B (Nat.card n)).obj (constantComplex Λ B)) := by
  obtain ⟨e⟩ := nonempty_iso_dualizingComplex_affineSpace Λ n B
  exact ⟨(L((AffineSpace.zeroSection n B)^*[ModuleCat.{u + 1} Λ])).mapIso
      (e ≪≫ twistShiftConstantComplexIso Λ _ _) ≪≫
    leftDerivedUpperStarTateShiftIso Λ _ _ ≪≫ (twistShiftConstantComplexIso Λ B _).symm⟩

/-- Blueprint `sk-thm-smooth-purity`: Finite-coefficient smooth purity

**Smooth purity, finite coefficients.** For `f : X ⟶ Y` smooth separated of pure relative
dimension `d` and a finite coefficient ring `Λ` whose exponent is invertible on `X`,

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
3. That section invariant is `Λ_X(d)[2d]` by vector-bundle purity
   (`AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_affineSpace`).

The normal bundle of `Δ` is the relative tangent bundle `T_{X/Y}`, which is étale-locally
trivial of rank `d` (`sk-lem-diag-reg`). Mathlib has neither vector bundles nor `T_{X/Y}`, so
the normal cone datum is recorded through `AlgebraicGeometry.Scheme.Hom.NormalConeData`, which
only asks for a smooth rank-`d` projection with a closed zero section; the trivial bundle
`𝔸^d_X` is used in step 2, for which step 3 is affine-space purity. -/
theorem nonempty_iso_dualizingComplex_twistShift :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X)) := by
  have hd : Nat.card (ULift.{u} (Fin d)) = d := by simp
  let N : (pullback.diagonal f).NormalConeData d :=
    { scheme := 𝔸(ULift.{u} (Fin d); X)
      proj := 𝔸(ULift.{u} (Fin d); X) ↘ X
      zeroSection := AffineSpace.zeroSection _ X
      zeroSection_comp_proj := AffineSpace.zeroSection_over _ X
      isClosedImmersion_zeroSection := inferInstance
      smoothOfRelativeDimension_proj := by
        have := AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) X
        rwa [hd] at this }
  have : HasCompactification N.proj := AffineSpace.hasCompactification X
  obtain ⟨e₁⟩ := nonempty_iso_sectionInvariant_diagonal Λ (d := d) f
  obtain ⟨e₂⟩ := nonempty_iso_sectionInvariant_normalCone Λ d (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f) N
  obtain ⟨e₃⟩ := nonempty_iso_sectionInvariant_affineSpace Λ (ULift.{u} (Fin d)) X
  rw [hd] at e₃
  exact ⟨e₁.symm ≪≫ e₂ ≪≫ e₃⟩

/-! ### The smooth purity map -/

/-- Blueprint `def-pur-smooth-purity-map`: Smooth purity map

For `f` smooth separated of pure relative dimension `d` and `K ∈ D(Y_ét, Λ)`, the *smooth
purity map* is the composite

`γ_{f,K} : Lf^* K(d)[2d] ≅ Lf^* K ⊗ Λ_X(d)[2d] ≅ Lf^* K ⊗ ω_f ≅ Rf^! K`

of the twist reassociation (`AlgebraicGeometry.Etale.twistShiftObjIso`), the inverse of the
identification `θ : ω_f ≅ Λ_X(d)[2d]` of `thm-pur-diagonal-dualizing-object`, and the tensor
formula `φ : Lf^* K ⊗ ω_f ≅ Rf^! K` of `sk-prop-cohsm` (b).

The blueprint's `θ` and `φ` are canonical maps; the library only provides their existence
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`,
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_derivedTensor`), so they
are arguments of the construction. -/
noncomputable def smoothPurityIso
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X))
    (φ : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
          (dualizingComplex (ModuleCat.{u + 1} Λ) f) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K) :
    (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K :=
  twistShiftObjIso Λ X d _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).mapIso
      θ.symm ≪≫ φ

/-- Blueprint `sk-thm-smooth-purity`: Finite-coefficient smooth purity

**The purity isomorphism on all coefficients.** Combining the tensor formula of
`sk-prop-cohsm` (b) with `ω_f ≅ Λ_X(d)[2d]`: for `f` smooth separated of pure relative
dimension `d` and every `K ∈ D^b_{ctf}(Y, Λ)`,

`Rf^! K ≅ (Lf^* K)(d)[2d]`.

This is also blueprint `thm-pur-finite-coefficient-smooth-purity` and
`cor-pur-dualizing-object-purity`: the isomorphism is the smooth purity map
`AlgebraicGeometry.Etale.smoothPurityIso` built from the two identifications. -/
theorem nonempty_iso_rightDerivedUpperShriek_twistShift
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    Nonempty ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K ≅
      (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  obtain ⟨θ⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := d) f
  obtain ⟨φ⟩ := nonempty_iso_rightDerivedUpperShriek_obj_derivedTensor Λ (d := d) f K hK
  exact ⟨(smoothPurityIso Λ (d := d) f K θ φ).symm⟩

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

variable [HasCompactification f']

/-- Blueprint `def-pur-smooth-pullback-exchange`: Smooth pullback exchange for exceptional
inverse image

For a cartesian square `g ≫ f = f' ≫ v` with `f` smooth of relative dimension `d`, the smooth
pullback exchange is the composite

`Ex^{!,sm}_{f,v,K} : Lg^* Rf^! K ≅ Lg^* Lf^* K(d)[2d] ≅ Lf'^* Lv^* K(d)[2d] ≅ Rf'^! Lv^* K`

of the inverse of `Lg^* γ_{f,K}`, the base-change identification
`AlgebraicGeometry.Etale.leftDerivedUpperStarTwistShiftBaseChangeIso` and `γ_{f',Lv^* K}`,
where `γ` and `γ'` are the smooth purity maps of `f` and of `f'`
(`AlgebraicGeometry.Etale.smoothPurityIso`). It is distinct from the mate of the
compact-support base change. -/
noncomputable def smoothPullbackExchange (_sq : IsPullback g f' f v)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (γ : (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K)
    (γ' : (twistShift Λ X' d).obj ((L((f')^*[ModuleCat.{u + 1} Λ])).obj
        ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K)) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f').obj
        ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f').obj
        ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  (L((g)^*[ModuleCat.{u + 1} Λ])).mapIso γ.symm ≪≫
    leftDerivedUpperStarTwistShiftBaseChangeIso Λ d f _sq.toCommSq K ≪≫ γ'

omit [Finite Λ] [IsSeparated f] [SmoothOfRelativeDimension d f] [HasInvertibleExponent Λ X] in
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
    (γ : (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K)
    (γ' : (twistShift Λ X' d).obj ((L((f')^*[ModuleCat.{u + 1} Λ])).obj
        ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K)) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f').obj
        ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).map γ.hom ≫ (smoothPullbackExchange Λ f sq K γ γ').hom =
      (leftDerivedUpperStarTwistShiftBaseChangeIso Λ d f sq.toCommSq K).hom ≫ γ'.hom := by
  simp [smoothPullbackExchange, ← Functor.map_comp_assoc]

end BaseChange

end Etale

end AlgebraicGeometry
