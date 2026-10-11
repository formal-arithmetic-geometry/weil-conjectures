/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.ConstructibleSheaf.Restriction
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!
# The affine line, `𝔾ₘ`, and the model purity

The rank-one computation that the whole of smooth purity rests on. The base `Y` is separated
of finite type over a field `k`, the coefficient ring `Λ` is finite with exponent invertible
on `Y`, and `p : 𝔸¹_Y → Y` is the projection, `s : Y → 𝔸¹_Y` the zero section and
`j : 𝔾_{m,Y} → 𝔸¹_Y` the open complement:

* the affine line is acyclic, `Rp_* Λ ≅ Λ_Y`, and `Rπ_* Λ(1)` has `Λ_Y(1)` in degree zero,
  `Λ_Y` in degree one and nothing else (`sk-prop-a1-kummer`);
* consequently `Rs^! Λ(1)[2] ≅ Λ_Y`, the *fundamental class* of the zero section
  (`sk-prop-a1`);
* a complex on `𝔸¹_Y` that is a pullback is determined by its restriction to `t = 1`, so its
  fibres at `t = 0` and `t = 1` agree (`sk-prop-a1-inv`).

Iterating the one-dimensional case gives the model purity `Rz^! Λ(c)[2c] ≅ Λ_B` for the zero
section of `𝔸^c_B` (`sk-prop-an`), in
`WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace`.

The invertibility hypothesis is not decorative: for `Λ = ℤ/p` over a base of characteristic
`p` the Artin–Schreier sequence gives `H¹(𝔸¹_k, ℤ/p) = k[t]/(F − 1)k[t] ≠ 0`, so the affine
line is not acyclic and every statement below fails.

## Implementation notes

`𝔾_m` is not a Mathlib scheme, so the open complement of the zero section is carried as data:
a scheme `G` with an open immersion `j` whose range is the complement of the range of the
zero section. This is the same idiom as `AlgebraicGeometry.Etale.openClosedShortComplex`.

The statements that compare the twist with geometry, `R¹π_*Λ(1) ≅ Λ_Y`,
`R^mπ_*Λ(1) = 0` for `m ≥ 2` and `Rs^!Λ(1)[2] ≅ Λ_Y`, assume the twist datum normalized
(`AlgebraicGeometry.Etale.HasTateTwist.IsNormalized`); they are false for the untwisted datum
`Λ_X(m) = Λ_X` or the shifted datum `Λ_X(m) = Λ_X[-2m]` (for the latter
`R²π_*(Λ_G[-2]) = R⁰π_*Λ_G = Λ_Y ≠ 0`). The last is then the normalisation itself,
transported along the identification of the zero section with `V(t)`.

Two clauses of the blueprint are stated only in part, and are TODOs.

* `sk-prop-a1-kummer` is recorded as what the cohomology sheaves *are* rather than as a
  statement about the generator `κ(t)` of `R¹π_*Λ(1)`. Here `sk-prop-a1` records that
  `Rs^!Λ(1)[2] ≅ Λ_Y`; that the boundary `∂κ(t)` of the Kummer class
  (`AlgebraicGeometry.Etale.kummerBoundary`) is this isomorphism is the orientation
  `AlgebraicGeometry.Etale.affineLineOrientation` of
  `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation`.
* Of `sk-prop-a1-inv` (ii) only the uniqueness half is stated; the gluing half — that
  normalized local comparisons over an étale cover of `Y` glue — needs a formalisation of
  étale-local data on `Y` that this file does not set up.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_affineLine`
- `AlgebraicGeometry.Etale.nonempty_iso_homology_zero_multiplicativeGroup`,
  `AlgebraicGeometry.Etale.nonempty_iso_homology_one_multiplicativeGroup`,
  `AlgebraicGeometry.Etale.isZero_homology_multiplicativeGroup`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineLineZero`
- `AlgebraicGeometry.Etale.injective_upperStar_map_of_isFiniteLocallyConstantSheaf`,
  `AlgebraicGeometry.Etale.injective_upperStar_oneSection_map_of_isFiniteLocallyConstantSheaf`
- `AlgebraicGeometry.Etale.eq_of_leftDerivedUpperStar_oneSection_eq`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

section

variable {k : Type u} [Field k] {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsSeparated aY]
  [LocallyOfFiniteType aY] [HasInvertibleExponent Λ Y]

/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

*Acyclicity of the affine line*: for the projection `p : 𝔸¹_Y → Y` one has
`Rp_* Λ ≅ Λ_Y`, equivalently `R^m p_* Λ = 0` for `m > 0` and `R⁰p_*Λ = Λ_Y`. Being an
instance of smooth base change, it is compatible with base change on `Y`; on a geometric
fibre it is the vanishing `H^q(𝔸¹_k, μ_{ℓ^N}) = 0` for `q > 0`, which follows from the
Kummer sequence, the divisibility of `k^×` and `Pic(𝔸¹_k) = 0`. -/
theorem nonempty_iso_rightDerivedLowerStar_affineLine :
    Nonempty ((R((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
        (constantComplex Λ 𝔸(ULift.{u} (Fin 1); Y)) ≅ constantComplex Λ Y) :=
  sorry

variable {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Y)) [IsOpenImmersion j]

/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

*Degree zero.* Let `j : G ↪ 𝔸¹_Y` be the open complement of the zero section — so
`G = 𝔾_{m,Y}` — and let `π = p ∘ j`. Then `R⁰π_* Λ(1) ≅ Λ_Y(1)`; on a geometric fibre this is
the Kummer computation `H⁰(𝔾_{m,k}, μ_n) = μ_n(k)`. -/
theorem nonempty_iso_homology_zero_multiplicativeGroup
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ) :
    Nonempty ((_root_.DerivedCategory.homologyFunctor _ 0).obj
        ((R((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
          ((tateTwist Λ G 1).obj (constantComplex Λ G))) ≅
      (_root_.DerivedCategory.homologyFunctor _ 0).obj (tateObject Λ Y 1)) :=
  sorry

/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

*Degree one.* In the situation above `R¹π_* Λ(1) ≅ Λ_Y`, free of rank one; on a geometric
fibre this is `H¹(𝔾_{m,k}, μ_n) = ℤ/n`, generated by the class of the coordinate `t`. -/
theorem nonempty_iso_homology_one_multiplicativeGroup [HasTateTwist.IsNormalized Λ]
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ) :
    Nonempty ((_root_.DerivedCategory.homologyFunctor _ 1).obj
        ((R((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
          ((tateTwist Λ G 1).obj (constantComplex Λ G))) ≅
      (_root_.DerivedCategory.homologyFunctor _ 0).obj (constantComplex Λ Y)) :=
  sorry

/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

*Vanishing above degree one.* In the situation above `R^m π_* Λ(1) = 0` for `m ≥ 2`, by the
cohomological dimension of an affine curve. -/
theorem isZero_homology_multiplicativeGroup [HasTateTwist.IsNormalized Λ]
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ)
    (m : ℤ) (hm : 2 ≤ m) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ m).obj
      ((R((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
        ((tateTwist Λ G 1).obj (constantComplex Λ G)))) :=
  sorry

/-- Blueprint `sk-prop-a1`: Rank-one orientation: the fundamental class of the zero section

For the zero section `s : Y ↪ 𝔸¹_Y` the complex `Rs^! Λ(1)[2]` is concentrated in degree zero
with lisse rank-one `H⁰`; the *fundamental class* `pur_s : Λ_Y ⟶ Rs^! Λ(1)[2]` normalized to
`1` at every geometric point is therefore an isomorphism, and it is the boundary of the
Kummer class `κ(t)`.

For a normalized twist datum this is the normalisation itself
(`AlgebraicGeometry.Etale.HasKummerClass.IsNormalized`): the zero section is the closed
subscheme `V(t)` cut out by the coordinate
(`AlgebraicGeometry.AffineSpace.zeroSectionIsoZeroLocusSubscheme`), and the adjoint of the
Kummer boundary `∂κ(t)` is an isomorphism `Λ_{V(t)} ≅ Rs^! Λ(1)[2]`. The blueprint proves the
normalisation for the concrete twist by applying `Rp_*` to the localization triangle of the
closed–open pair `(s, j)` and reading off the long exact sequence with `sk-prop-a1-kummer`.

The orientation itself, `1 ↦ ∂κ(t)`, is `AlgebraicGeometry.Etale.affineLineOrientation`; that
it is an isomorphism is `AlgebraicGeometry.Etale.isIso_affineLineOrientation`, the
identification of `Hom(Λ_Y, Rs^! Λ(1)[2])` with `H²_{s(Y)}(𝔸¹_Y, Λ(1))` is
`AlgebraicGeometry.Etale.supportedClassMap_bijective`, and its uniqueness is
`AlgebraicGeometry.Etale.affineLineOrientation_hom_ext`. -/
theorem nonempty_iso_rightDerivedUpperShriek_affineLineZero [HasTateTwist.IsNormalized Λ] :
    Nonempty ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ)
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).obj
        ((twistShift Λ 𝔸(ULift.{u} (Fin 1); Y) 1).obj
          (constantComplex Λ 𝔸(ULift.{u} (Fin 1); Y))) ≅
      constantComplex Λ Y) := by
  obtain ⟨K, hK, hN⟩ := HasTateTwist.IsNormalized.exists_hasKummerClass (Λ := Λ)
  subst hK
  let := K
  -- the zero section is the closed subscheme `V(t)` cut out by the coordinate
  let e := AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) Y
    (s := {AffineSpace.coord Y (ULift.up 0)}) Set.range_unique
  let ι := 𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι {AffineSpace.coord Y (ULift.up 0)}
  have he : e.hom ≫ ι = AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y :=
    AffineSpace.zeroSectionIsoZeroLocusSubscheme_hom_zeroLocusSubschemeι _ _ _
  have : HasCompactification (e.hom ≫ ι) := .of_eq he.symm
  -- the normalisation: the Kummer boundary of `t` is a fundamental class `Λ_{V(t)} ≅ Rι^! Λ(1)[2]`
  have hφ := hN.isIso_supportedClassMap_kummerBoundary_coord Y
  obtain ⟨heq⟩ := nonempty_iso_rightDerivedUpperShriek_of_eq (ModuleCat.{u + 1} Λ) he.symm
  obtain ⟨comp⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ e.hom ι
  exact ⟨heq.app _ ≪≫ comp.app _ ≪≫ (rightDerivedUpperShriekIsoOfIso _ e).app _ ≪≫
    (L((e.hom)^*[ModuleCat.{u + 1} Λ])).mapIso ((R(ι)^![ModuleCat.{u + 1} Λ]).mapIso
      ((shiftFunctor _ (2 * 1 : ℤ)).mapIso (derivedTensorLeftUnitor _ _ _) ≪≫
        eqToIso (by rw [mul_one])) ≪≫ (@asIso _ _ _ _ _ hφ).symm) ≪≫
    leftDerivedUpperStarConstantComplexIso Λ e.hom⟩

set_option linter.unusedSectionVars false in
/-- Blueprint `sk-prop-a1-inv`: Weak `𝔸¹`-invariance

*Uniqueness for lisse sheaf maps on `𝔸¹_Y`.* Two morphisms between finite locally constant
sheaves on `𝔸¹_Y` that agree after restriction to the open complement `G = 𝔾_{m,Y}` of the
zero section agree everywhere: the internal Hom is again finite locally constant, a section of
a locally constant sheaf on a connected scheme is determined by one geometric stalk, and every
connected component of `𝔸¹_Y` meets `𝔾_{m,Y}`. -/
theorem injective_upperStar_map_of_isFiniteLocallyConstantSheaf
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ)
    (L M : Sheaf 𝔸(ULift.{u} (Fin 1); Y).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf L] [Scheme.IsFiniteLocallyConstantSheaf M] :
    Function.Injective fun φ : L ⟶ M ↦ ((j)^*[ModuleCat.{u + 1} Λ]).map φ :=
  upperStar_map_injective_of_isLocallyConstantSheaf j (by
    rw [hj]
    exact AffineSpace.dense_compl_range_zeroSection _ _)

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Blueprint `sk-prop-a1-inv`: Weak `𝔸¹`-invariance

*Uniqueness for lisse sheaf maps on `𝔾_{m,Y}`.* Two morphisms between finite locally constant
sheaves on `𝔾_{m,Y}` that agree after restriction along the unit section `i₁ : Y ⟶ 𝔾_{m,Y}`
agree everywhere. This is the second assertion of clause (i), and it is what `sk-thm-dnc`
Step 2 and `sk-prop-an` Step 3 use. -/
theorem injective_upperStar_oneSection_map_of_isFiniteLocallyConstantSheaf
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ)
    (i₁ : Y ⟶ G) (hi₁ : i₁ ≫ j = AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)
    (L M : Sheaf G.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf L] [Scheme.IsFiniteLocallyConstantSheaf M] :
    Function.Injective fun φ : L ⟶ M ↦ ((i₁)^*[ModuleCat.{u + 1} Λ]).map φ := by
  -- `i₁` is a section of the separated `G ⟶ Y`, hence a closed immersion
  have hp : i₁ ≫ j ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) = 𝟙 Y := by
    rw [reassoc_of% hi₁, AffineSpace.oneSection_comp_over]
  have : IsClosedImmersion (i₁ ≫ j ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)) := by
    rw [hp]
    infer_instance
  have : IsClosedImmersion i₁ :=
    IsClosedImmersion.of_comp i₁ (j ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))
  -- every fibre of `G ⟶ Y` is irreducible, being open in a fibre of `𝔸¹_Y ⟶ Y`
  refine upperStar_map_injective_of_isPreconnected i₁ fun g ↦ ?_
  let y := (𝔸(ULift.{u} (Fin 1); Y) ↘ Y).base (j.base g)
  refine ⟨j.base ⁻¹' ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y).base ⁻¹' {y}),
    ((((𝔸(ULift.{u} (Fin 1); Y) ↘ Y).isIrreducible_preimage
      (AffineSpace.isOpenMap_over (n := ULift.{u} (Fin 1)) Y)
      isIrreducible_singleton).isPreirreducible.preimage j.isOpenEmbedding).isPreconnected),
    rfl, i₁.base y, ?_, y, rfl⟩
  have := congrArg (fun f : Y ⟶ Y ↦ f.base y) hp
  simpa using this

set_option linter.unusedSectionVars false in
/-- Blueprint `sk-prop-a1-inv`: Weak `𝔸¹`-invariance

*Invariance along the line.* A comparison between an invertible complex `F` on `𝔸¹_Y` and a
pullback from `Y` is determined by its restriction to the unit section `t = 1`: two
isomorphisms `α, β : F ≅ Lp^* C` with `Li₁^* α = Li₁^* β` are equal. Consequently the
identifications `Li₀^* F ≅ C ≅ Li₁^* F` obtained from such a comparison are canonical, and the
invariant is *constant* along the `𝔸¹`-direction: its values at `t = 0` and at `t = 1` agree.

Invertibility of `F` is what puts the comparison inside the lisse rank-one world in which the
uniqueness statements above apply; it is the hypothesis `sk-prop-a1-inv` (ii) imposes, in the
weaker form available here (the blueprint asks that `F` be étale-locally a shift and twist of
a lisse rank-one sheaf). -/
theorem eq_of_leftDerivedUpperStar_oneSection_eq
    (F : _root_.DerivedCategory
      (Sheaf 𝔸(ULift.{u} (Fin 1); Y).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (C : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hF : DerivedCategory.isInvertible Λ 𝔸(ULift.{u} (Fin 1); Y) F)
    (α β : F ≅ (L(((𝔸(ULift.{u} (Fin 1); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).obj C)
    (h : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)^*[ModuleCat.{u + 1} Λ])).map α.hom =
      (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)^*[ModuleCat.{u + 1} Λ])).map β.hom) :
    α = β := by
  let π := 𝔸(ULift.{u} (Fin 1); Y) ↘ Y
  let i₁ := AffineSpace.oneSection (ULift.{u} (Fin 1)) Y
  -- the unit section is a closed immersion, being a section of the separated `𝔸¹_Y ⟶ Y`
  have hp : i₁ ≫ π = 𝟙 Y := AffineSpace.oneSection_comp_over _ _
  have : IsClosedImmersion (i₁ ≫ π) := by
    rw [hp]
    infer_instance
  have : IsClosedImmersion i₁ := IsClosedImmersion.of_comp i₁ π
  -- the fibres of `𝔸¹_Y ⟶ Y` are irreducible and meet the unit section
  have hi : ∀ x : 𝔸(ULift.{u} (Fin 1); Y), ∃ S : Set 𝔸(ULift.{u} (Fin 1); Y),
      _root_.IsPreconnected S ∧ x ∈ S ∧ (S ∩ Set.range i₁.base).Nonempty := fun x ↦
    ⟨π.base ⁻¹' {π.base x}, (π.isIrreducible_preimage
      (AffineSpace.isOpenMap_over (n := ULift.{u} (Fin 1)) Y)
      isIrreducible_singleton).isPreirreducible.isPreconnected, rfl, i₁.base (π.base x),
      by simpa using congrArg (fun f : Y ⟶ Y ↦ f.base (π.base x)) hp, π.base x, rfl⟩
  have hγ : (L((i₁)^*[ModuleCat.{u + 1} Λ])).map (α.hom ≫ β.inv) = 𝟙 _ := by
    rw [CategoryTheory.Functor.map_comp, h, ← CategoryTheory.Functor.map_comp, β.hom_inv_id,
      CategoryTheory.Functor.map_id]
  have := eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible i₁ hi hF _ hγ
  exact Iso.ext (by rw [← Category.comp_id α.hom, ← β.inv_hom_id, ← Category.assoc, this,
    Category.id_comp])

end

end Etale

end AlgebraicGeometry
