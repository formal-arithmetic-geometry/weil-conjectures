/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.BoundedAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Triangulated.HomologySequenceMorphism
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenComplement

/-!
# The projection formula with a finitely presented constant coefficient

Let `Λ` be a noetherian commutative ring, `f : X ⟶ Y` a morphism of schemes and `K` an object of
`D(X_ét, Λ)`. For a finitely generated `Λ`-module `M`, with constant sheaves `M_X` and `M_Y`, the
projection map

`Rf_* K ⊗ᴸ M_Y ⟶ Rf_*(K ⊗ᴸ Lf^* M_Y) ≅ Rf_*(K ⊗ᴸ M_X)`

is an isomorphism as soon as `Rf_* K` and all the `Rf_*(K ⊗ᴸ Z_X)`, for `Z` finitely generated,
lie in degrees `≤ B` for one bound `B`
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_constantSheaf_of_isLE`). Under
the uniform vanishing `UDV(f, Λ; N)` of the higher direct images this holds for every `K` of finite
Tor amplitude (`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_constantSheaf`,
blueprint `lem-sf-projection-finite-constant`).

## Proof

The projection map is an isomorphism at the constant sheaf of a finite free module, which is
dualizable. A presentation `0 ⟶ Z ⟶ Λʳ ⟶ M ⟶ 0` gives a distinguished triangle
`Z_Y ⟶ Λʳ_Y ⟶ M_Y ⟶ Z_Y[1]`, carried by the projection map, which commutes with the shifts, to a
morphism of distinguished triangles. Both sides vanish in degrees `> B`, and the four and five
lemmas on the long exact homology sequences show, by descending induction on the degree `n` and
simultaneously for all finitely generated `M`, first that `Hⁿ` of the projection map is an
epimorphism, then that it is an isomorphism. This replaces the infinite free resolution and the
brutal truncations of the blueprint proof: the syzygy `Z` is again finitely generated, and the
uniform bound `B` is what makes the induction start.

## Main results

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_constantSheaf_of_isLE`
- `AlgebraicGeometry.Etale.isLE_rightDerivedLowerStar_of_hasUniformDirectImageVanishingLE`,
  `AlgebraicGeometry.Etale.isGE_rightDerivedLowerStar_of_isGE`: amplitude of `Rf_*` on bounded
  objects.
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_constantSheaf`
  (`lem-sf-projection-finite-constant`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The constant sheaf on `X_ét` with value a `Λ`-module `M`, placed in degree `0` of
`D(X_ét, Λ)`. -/
noncomputable abbrev constantSingle (X : Scheme.{u}) (M : ModuleCat.{u + 1} Λ) :
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (_root_.DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)

section Dualizable

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The constant sheaf of a finite projective `Λ`-module, placed in degree `0`, is dualizable in
`D(X_ét, Λ)`: the constant sheaf functor is monoidal, and a bounded complex of dualizable sheaves
is dualizable in the derived category. -/
lemma isDualizable_constantSingle (X : Scheme.{u}) (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    [Module.Projective Λ M] : IsDualizable (constantSingle X M) := by
  let G := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  have hG : IsDualizable G := IsDualizable.map _ (ModuleCat.isDualizable_of_projective M)
  refine IsDualizable.of_iso
    ((_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app G).symm
    (_root_.DerivedCategory.isDualizable_Q_obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G) 0 0 fun n ↦ ?_)
  by_cases hn : n = 0
  · subst hn
    exact IsDualizable.of_iso (HomologicalComplex.singleObjXSelf _ 0 G).symm hG
  · have hZ := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G n hn
    exact ⟨{ rightDual := _
             exact :=
              { coevaluation' := 0
                evaluation' := 0
                coevaluation_evaluation' := (hZ.of_iso (ρ_ _).symm).eq_of_src _ _
                evaluation_coevaluation' := (hZ.of_iso (λ_ _).symm).eq_of_src _ _ } }⟩

end Dualizable

/-- **The projection map at a finitely generated constant coefficient.** Let `Λ` be noetherian,
`f : X ⟶ Y` a morphism of schemes and `K` an object of `D(X_ét, Λ)` such that `Rf_* K` and all
the `Rf_*(K ⊗ᴸ Z_X)`, for `Z` a finitely generated `Λ`-module, lie in degrees `≤ B`. Then for
every finitely generated `Λ`-module `M` the projection map
`Rf_* K ⊗ᴸ M_Y ⟶ Rf_*(K ⊗ᴸ Lf^* M_Y)` is an isomorphism.

For a presentation `0 ⟶ Z ⟶ Λʳ ⟶ M ⟶ 0` the projection map is an isomorphism at `Λʳ_Y`, which is
dualizable, and both sides vanish in degrees `> B`. Descending induction on the degree, using the
four and five lemmas on the homology sequences of the triangle `Z_Y ⟶ Λʳ_Y ⟶ M_Y ⟶ Z_Y[1]`, shows
first that `Hⁿ` of the projection map is an epimorphism for all `M`, then that it is an
isomorphism. -/
theorem isIso_rightDerivedLowerStarProjectionMap_constantSheaf_of_isLE [IsNoetherianRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (B : ℤ)
    (hK : ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K).IsLE B)
    (hKZ : ∀ (Z : ModuleCat.{u + 1} Λ), Module.Finite Λ Z →
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj (K ⊗ constantSingle X Z)).IsLE B)
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app K).app
      (constantSingle Y M)) := by
  let τ := (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app K
  let H := _root_.DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0
  -- both sides vanish above `B`
  have hz₁ (M : ModuleCat.{u + 1} Λ) (n : ℤ) (hn : B < n) :
      IsZero ((H.shift n).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K ⊗ constantSingle Y M)) := by
    have : ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K ⊗ constantSingle Y M).IsLE (B + 0) :=
      _root_.DerivedCategory.isLE_tensor _ _ B 0
    exact _root_.DerivedCategory.isZero_of_isLE _ (B + 0) n (by lia)
  have hz₂ (M : ModuleCat.{u + 1} Λ) (hM : Module.Finite Λ M) (n : ℤ) (hn : B < n) :
      IsZero ((H.shift n).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
        (K ⊗ (L((f)^*[ModuleCat.{u + 1} Λ])).obj (constantSingle Y M)))) := by
    have := hKZ M hM
    have : ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
        (K ⊗ (L((f)^*[ModuleCat.{u + 1} Λ])).obj (constantSingle Y M))).IsLE B :=
      TStructure.t.isLE_of_iso ((R((f)_*[ModuleCat.{u + 1} Λ])).mapIso
        (whiskerLeftIso K (leftDerivedUpperStarSingleConstantSheafIso Λ f M))).symm B
    exact _root_.DerivedCategory.isZero_of_isLE _ B n hn
  have hiso_of_gt (M : ModuleCat.{u + 1} Λ) (hM : Module.Finite Λ M) (n : ℤ) (hn : B < n) :
      IsIso ((H.shift n).map (τ.app (constantSingle Y M))) :=
    ⟨⟨(hz₂ M hM n hn).to_ _, (hz₁ M n hn).eq_of_src _ _, (hz₂ M hM n hn).eq_of_src _ _⟩⟩
  -- the projection map is an isomorphism at a finite free module
  have hfree (r : ℕ) (n : ℤ) :
      IsIso ((H.shift n).map (τ.app (constantSingle Y (ModuleCat.of Λ (Fin r → Λ))))) := by
    have := isIso_rightDerivedLowerStarProjectionMap_app_app_of_isDualizable _ f K
      (isDualizable_constantSingle Y (ModuleCat.of Λ (Fin r → Λ)))
    infer_instance
  -- the triangle `Z_Y ⟶ Λʳ_Y ⟶ M_Y ⟶ Z_Y[1]` of a presentation of `M`
  have key (M : Type (u + 1)) [AddCommGroup M] [Module Λ M] [Module.Finite Λ M] :
      ∃ (Z : Type (u + 1)) (_ : AddCommGroup Z) (_ : Module Λ Z) (_ : Module.Finite Λ Z),
        ∀ n₀ n₁ : ℤ, n₀ + 1 = n₁ →
          (Epi ((H.shift n₁).map (τ.app (constantSingle Y (ModuleCat.of Λ Z)))) →
            Epi ((H.shift n₀).map (τ.app (constantSingle Y (ModuleCat.of Λ M))))) ∧
          (Epi ((H.shift n₀).map (τ.app (constantSingle Y (ModuleCat.of Λ Z)))) →
            IsIso ((H.shift n₁).map (τ.app (constantSingle Y (ModuleCat.of Λ Z)))) →
            IsIso ((H.shift n₀).map (τ.app (constantSingle Y (ModuleCat.of Λ M))))) := by
    obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' Λ M
    let Z := LinearMap.ker π
    have hex := LinearMap.exact_subtype_ker_map π
    have hS := ModuleCat.shortComplex_shortExact
      (ModuleCat.shortComplexOfCompEqZero Z.subtype π hex.linearMap_comp_eq_zero) hex
      Z.injective_subtype hπ
    have hS' := hS.map_of_exact (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    let T := hS'.singleTriangle
    have hT : T ∈ distTriang _ := hS'.singleTriangle_distinguished
    let φ := (NatTrans.mapTriangle τ).app T
    have hT₁ := ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)).map_distinguished T hT
    have hT₂ := ((L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K) ⋙
      R((f)_*[ModuleCat.{u + 1} Λ])).map_distinguished T hT
    refine ⟨Z, inferInstance, inferInstance, Module.IsNoetherian.finite Λ Z,
      fun n₀ n₁ h ↦ ⟨fun h₁ ↦ ?_, fun h₁ h₂ ↦ ?_⟩⟩
    · exact Functor.epi_shift_map_hom₃ (F := H) (φ := φ) (h := h) hT₁ hT₂
        (hfree r n₀).epi_of_iso h₁ (hfree r n₁).mono_of_iso
    · exact Functor.isIso_shift_map_hom₃ (F := H) (φ := φ) (h := h) hT₁ hT₂ h₁ (hfree r n₀) h₂
        (hfree r n₁).mono_of_iso
  -- descending induction on the degree
  have hepi (k : ℕ) : ∀ (M : Type (u + 1)) [AddCommGroup M] [Module Λ M] [Module.Finite Λ M],
      Epi ((H.shift (B + 1 - k)).map (τ.app (constantSingle Y (ModuleCat.of Λ M)))) := by
    induction k with
    | zero =>
      intro M _ _ _
      have := hiso_of_gt (ModuleCat.of Λ M) inferInstance (B + 1 - ((0 : ℕ) : ℤ)) (by lia)
      infer_instance
    | succ k ih =>
      intro M _ _ _
      obtain ⟨Z, _, _, _, hZ⟩ := key M
      exact (hZ (B + 1 - ((k + 1 : ℕ) : ℤ)) (B + 1 - k) (by lia)).1 (ih Z)
  have hiso (k : ℕ) : ∀ (M : Type (u + 1)) [AddCommGroup M] [Module Λ M] [Module.Finite Λ M],
      IsIso ((H.shift (B + 1 - k)).map (τ.app (constantSingle Y (ModuleCat.of Λ M)))) := by
    induction k with
    | zero =>
      intro M _ _ _
      exact hiso_of_gt (ModuleCat.of Λ M) inferInstance (B + 1 - ((0 : ℕ) : ℤ)) (by lia)
    | succ k ih =>
      intro M _ _ _
      obtain ⟨Z, _, _, _, hZ⟩ := key M
      exact (hZ (B + 1 - ((k + 1 : ℕ) : ℤ)) (B + 1 - k) (by lia)).2 (hepi (k + 1) Z) (ih Z)
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  by_cases hn : B < n
  · exact hiso_of_gt M inferInstance n hn
  · have := hiso (B + 1 - n).toNat M
    rwa [show B + 1 - ((B + 1 - n).toNat : ℤ) = n by lia] at this

/-! ### Amplitude of the direct image -/

/-- The derived direct image of a bounded object concentrated in degrees `≥ a` is concentrated
in degrees `≥ a`. -/
lemma isGE_rightDerivedLowerStar_of_isGE {X Y : Scheme.{u}} (f : X ⟶ Y) (a b : ℤ)
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [E.IsGE a] [E.IsLE b] : ((R((f)_*[ModuleCat.{u + 1} Λ])).obj E).IsGE a :=
  _root_.DerivedCategory.isGE_obj_of_bounded _
    (fun F ↦ ((f)_*[ModuleCat.{u + 1} Λ]).isGE_rightDerivedFunctor_obj_singleFunctor F) a b E

/-- Under the uniform vanishing `UDV(f, Λ; N)` of the higher direct images above `N`
(`def-sf-uniform-direct-image-vanishing`), the derived direct image of a bounded object
concentrated in degrees `≤ b` is concentrated in degrees `≤ b + N`. -/
lemma isLE_rightDerivedLowerStar_of_hasUniformDirectImageVanishingLE {X Y : Scheme.{u}}
    (f : X ⟶ Y) (N : ℕ) (hf : HasUniformDirectImageVanishingLE Λ f N) (a b : ℤ)
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [E.IsGE a] [E.IsLE b] : ((R((f)_*[ModuleCat.{u + 1} Λ])).obj E).IsLE (b + N) :=
  _root_.DerivedCategory.isLE_obj_of_bounded _ N (fun F ↦
    (_root_.DerivedCategory.isLE_iff _ _).2 fun q hq ↦
      (hf F q hq).of_iso (higherDirectImageIsoHomologyRightDerivedLowerStar Λ f q F).symm) a b E

/-- Blueprint `lem-sf-projection-finite-constant`: The projection formula with a finitely
presented constant coefficient.

Let `f : X ⟶ Y` be a morphism of schemes, `Λ` a noetherian commutative ring, and assume
`UDV(f, Λ; N)`: `Rᵠf_* F = 0` for every sheaf of `Λ`-modules `F` and every `q > N`. Let `K` be
an object of `D(X_ét, Λ)` of Tor amplitude in `[a, b]` and `M` a finitely generated `Λ`-module.
Then the projection map `Rf_* K ⊗ᴸ M_Y ⟶ Rf_*(K ⊗ᴸ Lf^* M_Y)` is an isomorphism; its target is
`Rf_*(K ⊗ᴸ M_X)` by `AlgebraicGeometry.Etale.leftDerivedUpperStarSingleConstantSheafIso`. The map
is natural in `M`, being a component of the natural transformation
`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`.

The blueprint allows any `K ∈ D^-(X_ét, Λ)`; here `K` has finite Tor amplitude, which is the case
used in `thm-sf-direct-image-tor-amplitude` and makes all the complexes `K ⊗ᴸ Z_X` bounded, so
that `UDV(f, Λ; N)` bounds their direct images
(`AlgebraicGeometry.Etale.isLE_rightDerivedLowerStar_of_hasUniformDirectImageVanishingLE`). The
proof is `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_constantSheaf_of_isLE`
with the bound `b + N`. -/
theorem isIso_rightDerivedLowerStarProjectionMap_constantSheaf [IsNoetherianRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ) (hf : HasUniformDirectImageVanishingLE Λ f N)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {a b : ℤ}
    (hK : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K)
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app K).app
      (constantSingle Y M)) := by
  obtain ⟨_, _⟩ := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hK
  refine isIso_rightDerivedLowerStarProjectionMap_constantSheaf_of_isLE f K (b + N)
    (isLE_rightDerivedLowerStar_of_hasUniformDirectImageVanishingLE f N hf a b K)
    (fun Z _ ↦ ?_) M
  obtain ⟨_, _⟩ := hK ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj Z)
  exact isLE_rightDerivedLowerStar_of_hasUniformDirectImageVanishingLE f N hf a b _

end Etale

end AlgebraicGeometry
