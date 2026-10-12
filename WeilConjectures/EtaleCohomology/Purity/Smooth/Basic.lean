/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# Finite-coefficient smooth purity

The central statement of the block. For `f : X ⟶ Y` smooth separated of pure relative
dimension `d` and a finite coefficient ring `Λ` whose exponent is invertible on `X`, *smooth
purity* (`sk-thm-smooth-purity`) says `ω_f ≅ Λ_X(d)[2d]`, hence `Rf^! K ≅ Lf^* K(d)[2d]`.
It rests on *cohomological smoothness* (`sk-prop-cohsm`), stated in
`WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness`.

The route is the blueprint's: the model case is affine-space purity
`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_affineSpace`, transported along the
deformation to the normal cone (`AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_normalCone`)
of the diagonal, a closed section of the first projection `X ×_Y X ⟶ X`.

## Implementation notes

The blueprint asserts that each isomorphism below is *canonical*: `sk-thm-smooth-purity` is
about the normalized comparison, built from the mate `φ_K : Lf^* K ⊗ ω_f ⟶ Rf^! K` of the
projection formula. That map does not exist in the repository — the projection map itself is a
TODO of `WeilConjectures.SixFunctors.Etale.Derived.Exchange` — so each statement records the
existence of the isomorphism only, with a `TODO(unify)` marker. For the same reason the smooth
purity map `γ_{f,K}` and the smooth pullback exchange are built from their constituent
isomorphisms, which are arguments of the constructions.

Statements whose type does not mention the relative dimension `d` carry `include d in`;
without it the hypothesis `[SmoothOfRelativeDimension d f]` would silently be dropped.

## Main definitions

- `AlgebraicGeometry.Etale.twistShiftObjIso`: the twist reassociation
  `M(m)[2m] ≅ M ⊗ Λ_X(m)[2m]`.
- `AlgebraicGeometry.Etale.smoothPurityIso`: the smooth purity map
  `γ_{f,K} : Lf^* K(d)[2d] ≅ Rf^! K`.
- `AlgebraicGeometry.Etale.smoothPullbackExchange`: the smooth pullback exchange
  `Lg^* Rf^! K ≅ Rf'^! Lv^* K`.

## Main statements

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
end Twist

/-! ### The diagonal -/

omit [HasTateTwist Λ] [IsSeparated f] in
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

omit [HasTateTwist Λ] [IsSeparated f] in
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

omit [HasTateTwist Λ] [IsSeparated f] in
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
    (leftDerivedUpperStarCompSectionIso _ _ _ (pullback.diagonal_snd f)).app _⟩

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
2. The deformation to the normal cone of `Δ` (`sk-thm-dnc`,
   `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_normalCone`) identifies `𝒞(p₁, Δ)`
   with the section invariant of its normal bundle, a rank-`d` vector bundle.
3. That section invariant is `Λ_X(d)[2d]` by affine-space purity
   (`AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_affineSpace`), which needs `X` of
   finite type over the field.

The normal bundle of `Δ` is the relative tangent bundle `T_{X/Y}`, which is étale-locally
trivial of rank `d` (`sk-lem-diag-reg`), so that step 3 is affine-space purity étale-locally.
Mathlib has neither vector bundles nor `T_{X/Y}`, and the normal cone datum
`AlgebraicGeometry.Scheme.Hom.NormalConeData` is not yet tied to the immersion, so the proof is
left as a TODO. -/
theorem nonempty_iso_dualizingComplex_twistShift [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k]
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY] :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X)) :=
  -- TODO: step 2 needs a deformation to the normal cone of `Δ` whose normal cone datum is the
  -- normal bundle `T_{X/Y}` (`nonempty_iso_sectionInvariant_normalCone`), and step 3
  -- vector-bundle purity for it. `NormalConeData` does not yet tie the datum to the immersion,
  -- and the existence of a deformation datum (`nonempty_deformationToNormalConeData`) is false
  -- for an arbitrary one, so the proof waits for the normal bundle
  -- (`prove2/sk-thm-smooth-purity-2`).
  sorry

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
theorem nonempty_iso_rightDerivedUpperShriek_twistShift [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k]
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    Nonempty ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K ≅
      (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  obtain ⟨θ⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := d) f aY
  obtain ⟨φ⟩ := nonempty_iso_rightDerivedUpperShriek_obj_derivedTensor Λ (d := d) f K hK
  exact ⟨(smoothPurityIso Λ (d := d) f K θ φ).symm⟩

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
  [HasInvertibleExponent Λ X']

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
where `γ = smoothPurityIso f K θ φ` and `γ' = smoothPurityIso f' (Lv^* K) θ' φ'` are the smooth
purity maps of `f` and of `f'` (`AlgebraicGeometry.Etale.smoothPurityIso`), built from the
identifications `θ, θ'` of the dualizing complexes and the tensor formulas `φ, φ'`. It is
distinct from the mate of the compact-support base change. -/
noncomputable def smoothPullbackExchange (sq : IsPullback g f' f v)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X))
    (φ : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
          (dualizingComplex (ModuleCat.{u + 1} Λ) f) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K)
    (θ' : dualizingComplex (ModuleCat.{u + 1} Λ) f' ≅
      (twistShift Λ X' d).obj (constantComplex Λ X'))
    (φ' : ((derivedTensor (ModuleCat.{u + 1} Λ) X').obj
        ((L((f')^*[ModuleCat.{u + 1} Λ])).obj ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K))).obj
          (dualizingComplex (ModuleCat.{u + 1} Λ) f') ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f').obj
        ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f').obj
        ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  (L((g)^*[ModuleCat.{u + 1} Λ])).mapIso (smoothPurityIso Λ f K θ φ).symm ≪≫
    leftDerivedUpperStarTwistShiftBaseChangeIso Λ d f sq.toCommSq K ≪≫
      smoothPurityIso Λ f' _ θ' φ'

omit [IsSeparated f] [SmoothOfRelativeDimension d f] in
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
    (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X))
    (φ : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
          (dualizingComplex (ModuleCat.{u + 1} Λ) f) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K)
    (θ' : dualizingComplex (ModuleCat.{u + 1} Λ) f' ≅
      (twistShift Λ X' d).obj (constantComplex Λ X'))
    (φ' : ((derivedTensor (ModuleCat.{u + 1} Λ) X').obj
        ((L((f')^*[ModuleCat.{u + 1} Λ])).obj ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K))).obj
          (dualizingComplex (ModuleCat.{u + 1} Λ) f') ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f').obj
        ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).map (smoothPurityIso Λ f K θ φ).hom ≫
        (smoothPullbackExchange Λ f sq K θ φ θ' φ').hom =
      (leftDerivedUpperStarTwistShiftBaseChangeIso Λ d f sq.toCommSq K).hom ≫
        (smoothPurityIso Λ f' _ θ' φ').hom := by
  simp [smoothPullbackExchange, ← Functor.map_comp_assoc]

end BaseChange

end Etale

end AlgebraicGeometry
