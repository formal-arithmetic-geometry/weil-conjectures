/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Concentrated

/-!
# DNC invariance of the section dualizing line

The deformation to the normal cone of a *section* transports the section invariant
`𝒞(g, s) = Ls^* ω_g` of a smooth morphism with a closed section to the section invariant of
its normal cone with the zero section. Together with the model purity for `𝔸ⁿ` this is what
computes `ω_f` in the smooth case.

Given a deformation datum `g̃ : 𝒟_s V ⟶ 𝔸¹_B` with section `s̃`
(`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData`), the *family object* is
`F = Ls̃^* ω_{g̃}`. The blueprint argument has three steps:

* `F` and `𝒞(g, s)` are shifts and twists of lisse rank-one sheaves;
* `F ≅ La^* 𝒞(g, s)` for the projection `a : 𝔸¹_B ⟶ B`, by gluing local standard models;
* restricting to `t = 0` gives `𝒞(g, s) ≅ 𝒞(π_N, 0_N)`, the fibres of `F` at `t = 1` and
  `t = 0` being the two section invariants by base change for the cohomologically smooth `g̃`.

## Implementation notes

The constancy `F ≅ La^* 𝒞(g, s)` is proved in the blueprint by gluing normalized local
comparisons over an étale cover of `B` on which the pair `(g, s)` has standard coordinates. The
coordinate charts (`sk-lem-geometry` (2), (4)) and the gluing half of `𝔸¹`-invariance
(`sk-prop-a1-inv`) are not available, so this step, and the shape of the section invariant, are
the `sorry`s of this file. Everything else is derived from them.

Since every isomorphism here is only known to exist, the compatibility of the comparison with
étale localization and base change in `B` (the last clause of the blueprint statements) cannot
be expressed: it is a statement about a chosen isomorphism. Likewise the normalization of the
DNC isomorphism "in coordinates" refers to coordinate charts that are not formalised. The
normalization at `t = 1` of the family comparison, and its uniqueness, are stated in
`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.existsUnique_familyObject_iso`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.familyObject`: the family object
  `F = Ls̃^* ω_{g̃}`.

## Main statements

- `AlgebraicGeometry.Etale.exists_nonempty_iso_sectionInvariant_twistShift`: a section
  invariant is a lisse rank-one sheaf, twisted and shifted.
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_sectionInvariant`: base change
  of section invariants.
- `AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.existsUnique_familyObject_iso`:
  the family is constant along `𝔸¹_B`, by a comparison that is unique once normalized at
  `t = 1` (existence is `nonempty_iso_familyObject_leftDerivedUpperStar`).
- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_normalCone`: DNC invariance.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

omit [Finite Λ] in
/-- Derived pullback preserves ⊗-invertibility: `Lf^*(K ⊗^L M) ≅ Lf^* K ⊗^L Lf^* M` and
`Lf^* Λ_Y ≅ Λ_X`. -/
theorem DerivedCategory.isInvertible_leftDerivedUpperStar_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.isInvertible Λ Y K) :
    DerivedCategory.isInvertible Λ X ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) := by
  obtain ⟨M, ⟨e⟩⟩ := hK
  exact ⟨_, ⟨(leftDerivedUpperStarTensorIso _ f K M).symm ≪≫
    (L((f)^*[ModuleCat.{u + 1} Λ])).mapIso e ≪≫ leftDerivedUpperStarConstantComplexIso Λ f⟩⟩

/-- Blueprint `prop-pur-dnc-family-constancy`: The deformation family is constant along the
affine line

*Base change of section invariants*, the input of the two fibre identifications
`i₁^* F ≅ 𝒞(g, s)` and `i₀^* F ≅ 𝒞(π_N, 0_N)` of `lem-pur-dnc-section-geometry` (1). In a
cartesian square with `f : X ⟶ Y` smooth and separated and sections `s` of `f` and `s'` of its
base change `f'` compatible with `g' : X' ⟶ X`, base change for the cohomologically smooth `f`
(`sk-prop-cohsm` (c)) gives `Lg^* 𝒞(f, s) ≅ 𝒞(f', s')`. -/
theorem nonempty_iso_leftDerivedUpperStar_sectionInvariant {X Y X' Y' : Scheme.{u}} {d : ℕ}
    (f : X ⟶ Y) [IsSeparated f] [SmoothOfRelativeDimension d f] [HasCompactification f]
    [HasInvertibleExponent Λ X] {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) [HasCompactification f'] (s : Y ⟶ X) (s' : Y' ⟶ X')
    (hs : s' ≫ g' = g ≫ s) :
    Nonempty ((L((g)^*[ModuleCat.{u + 1} Λ])).obj (sectionInvariant Λ f s) ≅
      sectionInvariant Λ f' s') := by
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek Λ (d := d) f sq
  exact ⟨((leftDerivedUpperStarComp _ g s).app _).symm ≪≫
    (leftDerivedUpperStarComp _ s' g' (g ≫ s) hs.symm).app _ ≪≫
    (L((s')^*[ModuleCat.{u + 1} Λ])).mapIso (e.app _ ≪≫
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f').mapIso
        (leftDerivedUpperStarConstantComplexIso Λ g))⟩

/-- Blueprint `prop-pur-dnc-family-constancy`: The deformation family is constant along the
affine line

*Clause (1), the section invariant is a shift of a lisse line.* For `g : V ⟶ B` smooth and
separated of pure relative dimension `d` with a section `s`, there is a finite locally constant
sheaf `L` on `B`, free of rank one at every geometric point, with

`𝒞(g, s) ≅ L(d)[2d]`.

Étale-locally on `B` the pair `(g, s)` has standard coordinates, in which `𝒞(g, s)` is
`Λ(d)[2d]` by the vector-bundle purity of `sk-prop-an`; the claim then follows from
`lem-pur-concentrated-complex-shift`. Neither the coordinate charts nor the local model are
available, see the module implementation notes. -/
theorem exists_nonempty_iso_sectionInvariant_twistShift {V B : Scheme.{u}} (d : ℕ) (g : V ⟶ B)
    [IsSeparated g] [SmoothOfRelativeDimension d g] [HasCompactification g] (s : B ⟶ V)
    (hs : s ≫ g = 𝟙 B) [HasInvertibleExponent Λ B] :
    ∃ L : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsFiniteLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ B),
        Nonempty ((pointSmallEtale x).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      Nonempty (sectionInvariant Λ g s ≅
        (twistShift Λ B d).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) :=
  sorry

end Etale

namespace Scheme.Hom.DeformationToNormalConeData

open _root_.AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {V B : Scheme.{u}} {d : ℕ}
  {g : V ⟶ B} {s : B ⟶ V} {N : NormalConeData d s} (D : DeformationToNormalConeData d g s N)

/-- Blueprint `def-pur-dnc-section-family`: Deformation space of a closed section

The *family object* `F = Ls̃^* ω_{g̃}` on `𝔸¹_B` of a deformation datum: the section invariant
of the deformation `g̃ : 𝒟_s V ⟶ 𝔸¹_B` and its section `s̃`. -/
noncomputable abbrev familyObject [HasCompactification D.proj] :
    _root_.DerivedCategory
      (Sheaf 𝔸(ULift.{u} (Fin 1); B).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  sectionInvariant Λ D.proj D.sect

variable [IsSeparated D.proj] [HasCompactification D.proj] [HasInvertibleExponent Λ B]

omit [Finite Λ] [HasTateTwist Λ] [IsSeparated D.proj] [HasCompactification D.proj] in
include D in
/-- The exponent of `Λ` is invertible on the deformation space as soon as it is on `B`. -/
theorem hasInvertibleExponent_scheme : HasInvertibleExponent Λ D.scheme :=
  HasInvertibleExponent.of_hom (D.proj ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)

/-- Blueprint `prop-pur-dnc-family-constancy`: The deformation family is constant along the
affine line

*Clause (1) for the family.* The family object is a shift of a lisse rank-one line,
`F ≅ L_F(d)[2d]`; this is `AlgebraicGeometry.Etale.exists_nonempty_iso_sectionInvariant_twistShift`
for the smooth separated deformation `g̃` and its section `s̃`. The same statement for
`𝒞(g, s)` is that lemma for `(g, s)`. -/
theorem exists_nonempty_iso_familyObject_twistShift :
    ∃ L : Sheaf 𝔸(ULift.{u} (Fin 1); B).smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsFiniteLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ 𝔸(ULift.{u} (Fin 1); B)),
        Nonempty ((pointSmallEtale x).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      Nonempty (D.familyObject Λ ≅ (twistShift Λ 𝔸(ULift.{u} (Fin 1); B) d).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) :=
  have := HasInvertibleExponent.of_hom (Λ := Λ) (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  exists_nonempty_iso_sectionInvariant_twistShift Λ d D.proj D.sect D.sect_comp_proj

/-- The family object is ⊗-invertible: `ω_{g̃}` is by cohomological smoothness of the smooth
separated `g̃` (`sk-prop-cohsm` (a)), and derived pullback along `s̃` preserves invertibility. -/
theorem isInvertible_familyObject :
    Etale.DerivedCategory.isInvertible Λ 𝔸(ULift.{u} (Fin 1); B) (D.familyObject Λ) :=
  have := D.hasInvertibleExponent_scheme Λ
  Etale.DerivedCategory.isInvertible_leftDerivedUpperStar_obj Λ D.sect
    (isInvertible_dualizingComplex Λ (d := d) D.proj)

variable [SmoothOfRelativeDimension d g] [HasCompactification g]

/-- Blueprint `prop-pur-dnc-family-constancy`: The deformation family is constant along the
affine line

*Clause (2), constancy along the affine line.* For the projection `a : 𝔸¹_B ⟶ B` there is an
isomorphism

`κ : F ≅ La^* 𝒞(g, s)`,

so that the family object is the pullback of its own fibre `𝒞(g, s)` at `t = 1`.

The blueprint proof glues, by `𝔸¹`-invariance (`prop-pur-a1-invariance`), the comparisons
`κ_i` supplied over an étale cover `{B_i ⟶ B}` carrying standard coordinates for `(g, s)` by
the vector-bundle Thom calculation. Neither the coordinate charts of `sk-lem-geometry` nor the
gluing half of `𝔸¹`-invariance are available, see the module implementation notes. -/
theorem nonempty_iso_familyObject_leftDerivedUpperStar :
    Nonempty (D.familyObject Λ ≅
      (L((𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).obj (sectionInvariant Λ g s)) :=
  sorry

/-- Blueprint `prop-pur-dnc-family-constancy`: The deformation family is constant along the
affine line

*Clause (3), normalization and uniqueness.* For every identification
`θ : i₁^* F ≅ 𝒞(g, s)` of the fibre of the family at `t = 1` (for instance the base change
identification of `lem-pur-dnc-section-geometry` (1), see
`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_sectionInvariant`) there is a unique
isomorphism `κ : F ≅ La^* 𝒞(g, s)` restricting to `θ` at `t = 1`, under `i₁^* a^* ≅ 𝟭`.

Existence: twist any comparison of clause (2) by the automorphism of `𝒞(g, s)` measuring its
failure to restrict to `θ`. Uniqueness: `F` is invertible, and a comparison between an
invertible complex on `𝔸¹_B` and a pullback from `B` is determined at `t = 1`
(`sk-prop-a1-inv`). -/
theorem existsUnique_familyObject_iso
    (θ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s) :
    ∃! κ : D.familyObject Λ ≅
        (L((𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).obj (sectionInvariant Λ g s),
      (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).map κ.hom ≫
        (leftDerivedUpperStarCompSectionIso _ _ _
          (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B)).hom.app _ = θ.hom := by
  obtain ⟨κ₀⟩ := D.nonempty_iso_familyObject_leftDerivedUpperStar Λ
  let ε := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) _ _
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B)
  let i₁ := L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])
  let a := L((𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])
  -- twisting a comparison by an automorphism `ψ` of `𝒞(g, s)` twists its restriction by `ψ`
  have key (κ : D.familyObject Λ ≅ a.obj (sectionInvariant Λ g s))
      (ψ : sectionInvariant Λ g s ≅ sectionInvariant Λ g s) :
      i₁.map (κ ≪≫ a.mapIso ψ).hom ≫ ε.hom.app _ = (i₁.map κ.hom ≫ ε.hom.app _) ≫ ψ.hom := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    congr 1
    exact ε.hom.naturality ψ.hom
  let ψ := (i₁.mapIso κ₀ ≪≫ ε.app _).symm ≪≫ θ
  have hψ : (i₁.map κ₀.hom ≫ ε.hom.app _) ≫ ψ.hom = θ.hom := by simp [ψ]
  refine ⟨κ₀ ≪≫ a.mapIso ψ, (key κ₀ ψ).trans hψ, fun κ hκ ↦ ?_⟩
  refine eq_of_leftDerivedUpperStar_oneSection_eq Λ _ _ (D.isInvertible_familyObject Λ) _ _ ?_
  rw [← cancel_mono (ε.hom.app _)]
  exact hκ.trans ((key κ₀ ψ).trans hψ).symm

end Scheme.Hom.DeformationToNormalConeData

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {V B : Scheme.{u}}

/-- Blueprint `sk-thm-dnc`: DNC invariance of the section dualizing line

Let `g : V ⟶ B` be smooth of pure relative dimension `d` with a closed section `s`, let
`N_s ⟶ B` be its normal cone with zero section `0_N`, and let `g̃ : 𝒟_s V ⟶ 𝔸¹_B` be a
deformation to the normal cone. There is an isomorphism

`𝒞(g, s) ≅ 𝒞(π_N, 0_N)`

between the two section invariants. It is `i₀^*` of the comparison `κ : F ≅ La^* 𝒞(g, s)` of
`prop-pur-dnc-family-constancy` (2), the fibre `i₀^* F` being `𝒞(π_N, 0_N)` by base change
(`lem-pur-dnc-section-geometry` (1)). This is also blueprint `thm-pur-dnc-invariance`. -/
-- TODO(unify): sk-thm-dnc — add the normalization in coordinates and the base-change clause.
theorem nonempty_iso_sectionInvariant_normalCone (d : ℕ) (g : V ⟶ B)
    [SmoothOfRelativeDimension d g] [HasCompactification g] (s : B ⟶ V) [IsClosedImmersion s]
    (N : Scheme.Hom.NormalConeData d s) [HasCompactification N.proj]
    (D : Scheme.Hom.DeformationToNormalConeData d g s N)
    [IsSeparated D.proj] [HasCompactification D.proj] [HasInvertibleExponent Λ B] :
    Nonempty (sectionInvariant Λ g s ≅ sectionInvariant Λ N.proj N.zeroSection) := by
  have := D.hasInvertibleExponent_scheme Λ
  obtain ⟨κ⟩ := D.nonempty_iso_familyObject_leftDerivedUpperStar Λ
  obtain ⟨e₀⟩ := nonempty_iso_leftDerivedUpperStar_sectionInvariant Λ (d := d) D.proj
    D.isPullback_zeroFibre D.sect N.zeroSection D.comp_zeroFibre
  exact ⟨((leftDerivedUpperStarCompSectionIso _ _ _
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) B)).app _).symm ≪≫
    (L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).mapIso κ.symm ≪≫
    e₀⟩

end Etale

end AlgebraicGeometry
