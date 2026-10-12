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

open CategoryTheory Limits MonoidalCategory

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

end Scheme.Hom

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}}

section FundamentalClass

variable [Finite Λ] {c : ℕ} {i : Z ⟶ X}

/-- The *class of a frame* `(e : U ⟶ X, f₁, …, f_c)` of `Z`:

`cl(f) = ∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c) ∈ H^{2c}_{Z_U}(U, Λ(c)) = Hom(Λ_U, Ri_{U!} Ri_U^! (Λ_U(c)[2c]))`,

the iterated cup product with supports of the Kummer boundaries
(`AlgebraicGeometry.Etale.kummerBoundaryProduct`), supported on
`V(f₁) ∩ ⋯ ∩ V(f_c) = Z_U`. -/
noncomputable def frameClass [HasKummerClass Λ] [HasInvertibleExponent Λ X] (F : i.EtaleFrame c) :
    constantComplex Λ F.U ⟶
      (R(F.U.zeroLocusSubschemeι (Set.range F.f))_![ModuleCat.{u + 1} Λ]).obj
        ((R(F.U.zeroLocusSubschemeι (Set.range F.f))^![ModuleCat.{u + 1} Λ]).obj
          ((tateObject Λ F.U c)⟦2 * (c : ℤ)⟧)) :=
  haveI : HasInvertibleExponent Λ F.U := .of_hom F.e
  kummerBoundaryProduct Λ F.f

/-- The restriction of a class `γ ∈ H^{2c}_Z(X, Λ(c))` to a frame `(e : U ⟶ X, f)`, a class in
`H^{2c}_{Z_U}(U, Λ(c))`: the restriction of supports along the étale `e`
(`AlgebraicGeometry.Etale.restrictSupportedClass`), with `Λ_U ≅ Le^* Λ_X` and
`Le^* (Λ_X(c)[2c]) ≅ Λ_U(c)[2c]`. -/
noncomputable def frameRestriction [HasTateTwist Λ] [IsClosedImmersion i]
    [HasInvertibleExponent Λ X] (F : i.EtaleFrame c)
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))) :
    constantComplex Λ F.U ⟶
      (R(F.U.zeroLocusSubschemeι (Set.range F.f))_![ModuleCat.{u + 1} Λ]).obj
        ((R(F.U.zeroLocusSubschemeι (Set.range F.f))^![ModuleCat.{u + 1} Λ]).obj
          ((tateObject Λ F.U c)⟦2 * (c : ℤ)⟧)) :=
  haveI : HasInvertibleExponent Λ F.U := .of_hom F.e
  restrictSupportedClass (ModuleCat.{u + 1} Λ) F.e i _ F.toZ F.isPullback
    (leftDerivedUpperStarConstantComplexIso Λ F.e).inv (leftDerivedUpperStarTateShiftIso Λ F.e c) γ

variable [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ X]
  {k : Type u} [Field k] [PerfectField k] (c) (i) [IsRegularImmersion c i]

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

**(b) The fundamental class.** Let `i : Z ⟶ X` be a regular closed immersion of pure
codimension `c`, with `X` smooth over the perfect field `k` and `Z` regular. The frame classes
depend only on `Z_U ⊂ U`, not on the frame, and they glue: there is a unique class
`[Z ⊂ X] ∈ H^{2c}_Z(X, Λ(c))` whose restriction to every frame is the frame class.

Two frames on the same `U` differ Zariski-locally by a matrix in `GL_c(𝒪)`, a product of
diagonal, permutation and elementary matrices, under which the cup product of Kummer
boundaries is invariant (`∂κ(u) = 0` for a unit, even degrees, and `𝔸¹`-invariance for the
shears); by (a) the classes are sections of the sheaf `𝓗⁰(Ri^! Λ_X(c)[2c])`, so they glue. -/
theorem existsUnique_fundamentalClass (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    ∃! γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)),
      ∀ F : i.EtaleFrame c, frameRestriction Λ F γ = frameClass Λ F :=
  sorry

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

The *fundamental class* `[Z ⊂ X] = cl_{Z/X} ∈ H^{2c}_Z(X, Λ(c))` of a regular closed immersion
`i : Z ⟶ X` of pure codimension `c`, with `X` smooth over a perfect field and `Z` regular: the
unique class restricting to the frame class `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c)` on every frame.

It is *defined* as `Classical.choose` of
`AlgebraicGeometry.Etale.existsUnique_fundamentalClass`, which is not yet proved; uniqueness
is what makes the choice canonical. -/
noncomputable def fundamentalClass (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) :=
  (existsUnique_fundamentalClass Λ c i aX hZ).exists.choose

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

**(a) Concentration in degree zero.** `Ri^! (Λ_X(c)[2c])` has no cohomology sheaves outside
degree `0`. The hypotheses are stable under étale base change `X' ⟶ X`, so this holds after
any étale base change too. -/
theorem isZero_homology_rightDerivedUpperShriek_of_isRegularImmersion
    (aX : X ⟶ Spec (.of k)) [Smooth aX] (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z))
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))) :=
  sorry

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

**(a) Lisse in degree zero.** `𝓗⁰(Ri^! (Λ_X(c)[2c]))` is a locally constant sheaf on `Z_ét`. -/
theorem isLocallyConstantSheaf_homology_zero_rightDerivedUpperShriek_of_isRegularImmersion
    (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    Scheme.IsLocallyConstantSheaf ((_root_.DerivedCategory.homologyFunctor _ 0).obj
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))) :=
  sorry

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
          (ModuleCat.of Λ Λ)) :=
  sorry

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
        isRegularLocalRing_stalk_of_etale g hZ) :=
  sorry

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
theorem nonempty_iso_dualizingComplex_of_isRegularImmersion [Finite Λ] [HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k] [PerfectField k] (c n m : ℕ) (hm : m + c = n) (i : Z ⟶ X)
    [IsRegularImmersion c i] [HasCompactification i] (aX : X ⟶ Spec (.of k)) [IsSeparated aX]
    [SmoothOfRelativeDimension n aX] [HasCompactification aX]
    [SmoothOfRelativeDimension m (i ≫ aX)] [HasCompactification (i ≫ aX)]
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Z] :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) i ≅
      (twistShift Λ Z (-c : ℤ)).obj (constantComplex Λ Z)) :=
  sorry

end Etale

end AlgebraicGeometry
