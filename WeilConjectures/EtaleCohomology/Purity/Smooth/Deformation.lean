/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.Derived.Concentrated
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal

/-!
# DNC invariance of the section dualizing line

The deformation to the normal cone of a *section* transports the section invariant
`𝒞(g, s) = Ls^* ω_g` of a smooth morphism with a closed section to the section invariant of
its normal cone with the zero section. Together with the model purity for `𝔸ⁿ` this is what
computes `ω_f` in the smooth case.

Given a deformation datum `g̃ : 𝒟_s V ⟶ 𝔸¹_B` with section `s̃`
(`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData`), the *family object* is
`F = Ls̃^* ω_{g̃}`. The blueprint argument has three steps:

* étale-locally on `B` the family is the standard family `a^* 𝒞(𝔸^d, 0)`, so `F` and `𝒞(g, s)`
  are shifts and twists of lisse rank-one sheaves (`lem-pur-concentrated-complex-shift`);
* the normalized local comparisons `F ≅ La^* 𝒞(g, s)` glue, by `𝔸¹`-invariance
  (`prop-pur-a1-invariance`), to a global one, for the projection `a : 𝔸¹_B ⟶ B`;
* restricting to `t = 0` gives `𝒞(g, s) ≅ 𝒞(π_N, 0_N)`, the fibres of `F` at `t = 1` and
  `t = 0` being the two section invariants by base change for the cohomologically smooth `g̃`.

## Implementation notes

The deformation space is carried as data, not constructed (see
`WeilConjectures.AlgebraicGeometry.DeformationToNormalCone`). Its étale-local coordinates
(`lem-pur-dnc-section-geometry` (2), (4), (5)) are a field of the datum; from them,
`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.exists_etale_nonempty_iso_familyObject`
computes the family object over an étale cover of `B` as the one of the standard pair
`(𝔸^d → B, 0)`, pulled back from the base. The sheaf-theoretic inputs are base change for the
smooth `g̃` and `Re^! ≅ e^*` for an étale `e` (`lem-pur-co-smooth-etale-locality`).

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

In the list below, `DeformationToNormalConeData` abbreviates
`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData`.

- `AlgebraicGeometry.Etale.exists_nonempty_iso_twistShift_of_leftDerivedUpperStar_iso`: an
  object which is étale-locally `Λ(m)[2m]` is a lisse rank-one sheaf, twisted and shifted.
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_sectionInvariant`: base change
  of section invariants.
- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_of_etale_chart`: section invariants
  through an étale chart to `𝔸^d`.
- `DeformationToNormalConeData.exists_etale_nonempty_iso_familyObject`: étale-locally the family
  is the standard family.
- `DeformationToNormalConeData.exists_nonempty_iso_familyObject_twistShift`,
  `DeformationToNormalConeData.exists_nonempty_iso_sectionInvariant_twistShift`:
  the family object and the section invariant are lisse rank-one sheaves, twisted and shifted.
- `DeformationToNormalConeData.nonempty_iso_familyObject_leftDerivedUpperStar`,
  `DeformationToNormalConeData.existsUnique_familyObject_iso`:
  the family is constant along `𝔸¹_B`, by a comparison that is unique once normalized at
  `t = 1`.
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
/-- Blueprint `lem-pur-concentrated-complex-shift`: Complexes with cohomology in a single degree

*Shifts and twists of lisse rank-one sheaves are detected on an étale cover.* Let
`u : U ⟶ T` be surjective and étale and `K ∈ D(T_ét, Λ)` with `Lu^* K ≅ Λ_U(m)[2m]`. Then
`K ≅ L(m)[2m]` for a finite locally constant sheaf `L` on `T`, free of rank one at every
geometric point.

Untwisting, `Lu^* (K(-m)[-2m]) ≅ Λ_U` is the constant sheaf in degree zero, so by the lemma
`K(-m)[-2m]` is its own `H⁰` placed in degree zero and `H⁰` is finite locally constant; its
stalks are those of `Λ_U`, a geometric point of `T` lifting to `U`. -/
theorem exists_nonempty_iso_twistShift_of_leftDerivedUpperStar_iso {U T : Scheme.{u}}
    (u : U ⟶ T) [Etale u] [Surjective u] (m : ℤ)
    (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (e : (L((u)^*[ModuleCat.{u + 1} Λ])).obj K ≅ (twistShift Λ U m).obj (constantComplex Λ U)) :
    ∃ L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsFiniteLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ T),
        Nonempty ((pointSmallEtale x).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      Nonempty (K ≅ (twistShift Λ T m).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) := by
  let K₀ := (twistShift Λ T (-m)).obj K
  -- untwisting, `Lu^* K₀` is the unit sheaf in degree zero
  let e₀ : (L((u)^*[ModuleCat.{u + 1} Λ])).obj K₀ ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj (𝟙_ _) :=
    leftDerivedUpperStarTwistShiftIso Λ u (-m) K ≪≫ (twistShift Λ U (-m)).mapIso e ≪≫
      twistShiftTwistShiftIso Λ U m (-m) _ ≪≫ twistShiftZeroIso Λ U (by ring) _ ≪≫
      constantComplexIsoSingleFunctor Λ U
  obtain ⟨c⟩ := _root_.DerivedCategory.nonempty_iso_singleFunctor_obj_homologyFunctor_obj K₀ 0
    (isZero_homology_of_leftDerivedUpperStar_iso Λ u e₀)
  refine ⟨_, isFiniteLocallyConstantSheaf_homology_of_leftDerivedUpperStar_iso Λ u e₀,
    fun Ω _ _ x ↦ ?_, ⟨(twistShiftZeroIso Λ T (by ring) K).symm ≪≫
      (twistShiftTwistShiftIso Λ T (-m) m K).symm ≪≫ (twistShift Λ T m).mapIso c⟩⟩
  -- the stalk at a lift `x'` of `x` is that of `u^* H⁰(K₀) ≅ H⁰(Lu^* K₀) ≅ Λ_U`
  obtain ⟨x', rfl⟩ := exists_comp_eq_of_etale_of_surjective u x
  exact ⟨((Etale.upperStarCompSheafFiberIso _ u x').app _).symm ≪≫
    (pointSmallEtale x').sheafFiber.mapIso
      (((leftDerivedUpperStarHomologyFunctorIso _ u 0).app K₀) ≪≫
        (_root_.DerivedCategory.homologyFunctor _ 0).mapIso e₀ ≪≫
        (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _) ≪≫
    ((pointSmallEtale x').uliftSheafFiberIso _).symm.app _ ≪≫ sheafFiberUnitIso _ x'⟩

/-- Blueprint `lem-pur-dnc-section-geometry`: Geometry of the deformation

*Base change of section invariants*, the input of the two fibre identifications
`i₁^* F ≅ 𝒞(g, s)` and `i₀^* F ≅ 𝒞(π_N, 0_N)` of clause (1). In a cartesian square with
`f : X ⟶ Y` smooth and separated and sections `s` of `f` and `s'` of its base change `f'`
compatible with `g' : X' ⟶ X`, base change for the cohomologically smooth `f`
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

/-- *Section invariants through an étale chart.* Let `g' : X ⟶ T` be compactifiable, `j : W ⟶ X`
a quasi-compact open immersion and `c : W ⟶ 𝔸^d_T` an étale map over `T`, with
`j ≫ g' = c ≫ π`, and let `σ : T ⟶ W` be a section carried by `c` to the zero section. If
`ω_π ≅ K` for some `K ∈ D^b_{ctf}`, then `𝒞(g', σ ≫ j) ≅ 𝒞(π, 0)`:

`Lσ^* Lj^* ω_{g'} ≅ Lσ^* Rj^! Rg'^! Λ ≅ Lσ^* R(j ≫ g')^! Λ = Lσ^* R(c ≫ π)^! Λ ≅ Lσ^* Rc^! ω_π
  ≅ Lσ^* Lc^* ω_π`,

by `Rj^! ≅ j^*` for the open immersion `j`, the composition of exceptional inverse images, and
`Rc^! ≅ Lc^*` on `D^b_{ctf}` for the étale `c` (`lem-pur-co-smooth-etale-locality`). -/
theorem nonempty_iso_sectionInvariant_of_etale_chart {X W T : Scheme.{u}} {d : ℕ}
    (g' : X ⟶ T) [HasCompactification g'] (j : W ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (c : W ⟶ 𝔸(ULift.{u} (Fin d); T)) [_root_.AlgebraicGeometry.Etale c]
    [HasCompactification c] [HasInvertibleExponent Λ W]
    (hjc : j ≫ g' = c ≫ 𝔸(ULift.{u} (Fin d); T) ↘ T) (σ : T ⟶ W)
    (hσc : σ ≫ c = AffineSpace.zeroSection (ULift.{u} (Fin d)) T)
    {K : _root_.DerivedCategory
      (Sheaf 𝔸(ULift.{u} (Fin d); T).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ _ K)
    (ω : dualizingComplex (ModuleCat.{u + 1} Λ) (𝔸(ULift.{u} (Fin d); T) ↘ T) ≅ K) :
    Nonempty (sectionInvariant Λ g' (σ ≫ j) ≅
      sectionInvariant Λ (𝔸(ULift.{u} (Fin d); T) ↘ T)
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) T)) := by
  have : HasCompactification j := (Compactification.ofIsOpenImmersion j).hasCompactification
  have : HasCompactification (j ≫ g') := .comp_of_isOpenImmersion g' j
  have : HasCompactification (c ≫ 𝔸(ULift.{u} (Fin d); T) ↘ T) := .of_eq hjc
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ j g'
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_of_eq (A := ModuleCat.{u + 1} Λ) hjc
  obtain ⟨e₃⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ c (𝔸(ULift.{u} (Fin d); T) ↘ T)
  obtain ⟨e₄⟩ := nonempty_iso_rightDerivedUpperShriek_obj_of_etale Λ c K hK
  exact ⟨(leftDerivedUpperStarComp _ σ j).app _ ≪≫
    (L((σ)^*[ModuleCat.{u + 1} Λ])).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ j).app _ ≪≫
        ((rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j).app _).symm ≪≫
        (e₁.app _).symm ≪≫ e₂.app _ ≪≫ e₃.app _ ≪≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) c).mapIso ω ≪≫ e₄ ≪≫
        (L((c)^*[ModuleCat.{u + 1} Λ])).mapIso ω.symm) ≪≫
    ((leftDerivedUpperStarComp _ σ c _ hσc.symm).app _).symm⟩

end Etale

namespace Scheme.Hom.DeformationToNormalConeData

open _root_.AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {V B : Scheme.{u}} {d : ℕ}
  {g : V ⟶ B} {s : B ⟶ V} {N : NormalConeData d s} (D : DeformationToNormalConeData d g s N)

/-- Blueprint `def-pur-dnc-section-family`: Deformation space of a closed section

The *family object* `F = Ls̃^* ω_{g̃}` on `𝔸¹_B` of a deformation datum: the section invariant
of the deformation `g̃ : 𝒟_s V ⟶ 𝔸¹_B` and its section `s̃`. -/
noncomputable abbrev familyObject :
    _root_.DerivedCategory
      (Sheaf 𝔸(ULift.{u} (Fin 1); B).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  sectionInvariant Λ D.proj D.sect

variable [HasInvertibleExponent Λ B]

omit [Finite Λ] [HasTateTwist Λ] in
include D in
/-- The exponent of `Λ` is invertible on the deformation space as soon as it is on `B`. -/
theorem hasInvertibleExponent_scheme : HasInvertibleExponent Λ D.scheme :=
  HasInvertibleExponent.of_hom (D.proj ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)

/-- The family object is ⊗-invertible: `ω_{g̃}` is by cohomological smoothness of the smooth
separated `g̃` (`sk-prop-cohsm` (a)), and derived pullback along `s̃` preserves invertibility. -/
theorem isInvertible_familyObject :
    Etale.DerivedCategory.isInvertible Λ 𝔸(ULift.{u} (Fin 1); B) (D.familyObject Λ) :=
  have := D.hasInvertibleExponent_scheme Λ
  Etale.DerivedCategory.isInvertible_leftDerivedUpperStar_obj Λ D.sect
    (isInvertible_dualizingComplex Λ (d := d) D.proj)

variable [HasCompactification g]

/-- The fibre of the family at `t = 1` is the section invariant of `(g, s)`
(`lem-pur-dnc-section-geometry` (1)): `Li₁^* F ≅ 𝒞(g, s)`, by base change for `g̃` along the
unit section. -/
theorem nonempty_iso_leftDerivedUpperStar_oneSection_familyObject :
    Nonempty ((L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s) :=
  have := D.hasInvertibleExponent_scheme Λ
  nonempty_iso_leftDerivedUpperStar_sectionInvariant Λ (d := d) D.proj D.isPullback_oneFibre
    D.sect s D.comp_oneFibre

variable {k : Type u} [Field k] (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]

omit [HasCompactification g] in
include aB in
/-- Blueprint `lem-pur-dnc-section-geometry`: Geometry of the deformation

*Clauses (2), (4) and (5): the family is étale-locally the standard family.* There is a
surjective étale `u : B' ⟶ B`, with `B'` separated of finite type over `k`, over which

`F|_{𝔸¹_{B'}} ≅ a'^* 𝒞(𝔸^d_{B'} → B', 0)`.

Take the étale coordinates of the datum (`exists_etale_coordinates`): over `u`, an open
`j : W ⟶ 𝒟'` of the base-changed deformation `g' : 𝒟' ⟶ 𝔸¹_{B'}` containing its section `σ`,
and an étale `c : W ⟶ 𝔸^d_{𝔸¹_{B'}}` over `𝔸¹_{B'}` carrying `σ` to the zero section. Then

`F|_{𝔸¹_{B'}} ≅ Lσ^* Lj^* ω_{g'} ≅ Lσ^* Rj^! ω_{g'} ≅ Lσ^* Rc^! ω_π ≅ Lσ^* Lc^* ω_π ≅ L0^* ω_π`,

by base change for `g̃` (`sk-prop-cohsm` (c)), `Rj^! ≅ j^*` for the open immersion `j`, the
composition of exceptional inverse images along `j ≫ g' = c ≫ π`, and `Rc^! ≅ c^*` for the étale
`c` (`lem-pur-co-smooth-etale-locality`). Both `L0^* ω_π` and `a'^* 𝒞(𝔸^d_{B'} → B', 0)` are
`Λ(d)[2d]` by affine-space purity (`sk-prop-an`). -/
theorem exists_etale_nonempty_iso_familyObject [HasTateTwist.IsNormalized Λ] :
    ∃ (B' : Scheme.{u}) (u : B' ⟶ B), _root_.AlgebraicGeometry.Etale u ∧ Surjective u ∧
      IsSeparated (u ≫ aB) ∧
      Nonempty ((L((AffineSpace.map (ULift.{u} (Fin 1)) u)^*[ModuleCat.{u + 1} Λ])).obj
          (D.familyObject Λ) ≅
        (L((𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).obj
          (sectionInvariant Λ (𝔸(ULift.{u} (Fin d); B') ↘ B')
            (AffineSpace.zeroSection (ULift.{u} (Fin d)) B'))) := by
  obtain ⟨B', v, W, j, c, σ, hv, hsurj, hsep, hj, hjqc, hc, hcc, hjc, hσj, hσc⟩ :=
    D.exists_etale_coordinates
  let T := 𝔸(ULift.{u} (Fin 1); B')
  let v₁ := AffineSpace.map (ULift.{u} (Fin 1)) v
  have := D.hasInvertibleExponent_scheme Λ
  have : HasInvertibleExponent Λ B' := .of_hom v
  have : HasInvertibleExponent Λ T := .of_hom (T ↘ B')
  have : HasInvertibleExponent Λ (pullback D.proj v₁) := .of_hom (pullback.fst D.proj v₁)
  have : HasInvertibleExponent Λ W := .of_hom j
  -- `Lv₁^* F ≅ 𝒞(g', σ ≫ j)`, by base change for `g̃` along `v₁`
  obtain ⟨e₁⟩ := nonempty_iso_leftDerivedUpperStar_sectionInvariant Λ (d := d) D.proj
    (IsPullback.of_hasPullback D.proj v₁) D.sect (σ ≫ j) ((Category.assoc _ _ _).trans hσj)
  -- `𝒞(g', σ ≫ j) ≅ 𝒞(𝔸^d_T → T, 0)` through the chart, with `ω_π ≅ Λ(d)[2d]` (`sk-prop-an`)
  obtain ⟨ω⟩ := nonempty_iso_dualizingComplex_affineSpace Λ d T (T ↘ B' ≫ v ≫ aB)
  obtain ⟨e₂⟩ := nonempty_iso_sectionInvariant_of_etale_chart Λ (pullback.snd D.proj v₁) j c hjc
    σ hσc ((boundedConstructibleFiniteTor_tateObject Λ _ d).shift (2 * d))
    (ω ≪≫ twistShiftConstantComplexIso Λ _ d)
  -- both standard section invariants are `Λ(d)[2d]`
  obtain ⟨c₁⟩ := nonempty_iso_sectionInvariant_affineSpace Λ d T (T ↘ B' ≫ v ≫ aB)
  obtain ⟨c₀⟩ := nonempty_iso_sectionInvariant_affineSpace Λ d B' (v ≫ aB)
  refine ⟨B', v, hv, hsurj, inferInstanceAs (IsSeparated (v ≫ aB)), ⟨?_⟩⟩
  exact e₁ ≪≫ e₂ ≪≫ c₁ ≪≫
    ((twistShift Λ T d).mapIso (leftDerivedUpperStarConstantComplexIso Λ (T ↘ B'))).symm ≪≫
    (leftDerivedUpperStarTwistShiftIso Λ _ d _).symm ≪≫
    (L((T ↘ B')^*[ModuleCat.{u + 1} Λ])).mapIso c₀.symm


variable [HasTateTwist.IsNormalized Λ]

include aB in
/-- The étale-local data of the family used by `prop-pur-dnc-family-constancy`: over the cover
`u : B' ⟶ B` of `lem-pur-dnc-section-geometry` (2), with `v₁ : 𝔸¹_{B'} ⟶ 𝔸¹_B` its base
change, the family is `Lv₁^* F ≅ La'^* 𝒞₀` for the standard section invariant
`𝒞₀ = 𝒞(𝔸^d_{B'} → B', 0) ≅ Λ_{B'}(d)[2d]` (`sk-prop-an`), and restricting at `t = 1` gives
`φ : Lu^* 𝒞(g, s) ≅ 𝒞₀`, related to the base change `θ : Li₁^* F ≅ 𝒞(g, s)` by
`Li₁'^* e = (Li₁'^* Lv₁^* F ≅ Lu^* Li₁^* F) ≫ Lu^* θ ≫ φ` up to `Li₁'^* La'^* ≅ 𝟭`. -/
theorem exists_etale_familyObject_data
    (θ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s) :
    ∃ (B' : Scheme.{u}) (u : B' ⟶ B), _root_.AlgebraicGeometry.Etale u ∧ Surjective u ∧
      IsSeparated (u ≫ aB) ∧
      Nonempty (sectionInvariant Λ (𝔸(ULift.{u} (Fin d); B') ↘ B')
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) B') ≅
          (twistShift Λ B' d).obj (constantComplex Λ B')) ∧
      ∃ (e : (L((AffineSpace.map (ULift.{u} (Fin 1)) u)^*[ModuleCat.{u + 1} Λ])).obj
          (D.familyObject Λ) ≅
        (L((𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).obj
          (sectionInvariant Λ (𝔸(ULift.{u} (Fin d); B') ↘ B')
            (AffineSpace.zeroSection (ULift.{u} (Fin d)) B')))
        (φ : (L((u)^*[ModuleCat.{u + 1} Λ])).obj (sectionInvariant Λ g s) ≅
          sectionInvariant Λ (𝔸(ULift.{u} (Fin d); B') ↘ B')
            (AffineSpace.zeroSection (ULift.{u} (Fin d)) B')),
        (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B')^*[ModuleCat.{u + 1} Λ])).map e.hom ≫
            (leftDerivedUpperStarCompSectionIso _ _ _
              (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B')).hom.app _ =
          (((leftDerivedUpperStarComp _ (AffineSpace.oneSection (ULift.{u} (Fin 1)) B')
              (AffineSpace.map (ULift.{u} (Fin 1)) u)).inv.app _ ≫
            (leftDerivedUpperStarComp _ u (AffineSpace.oneSection (ULift.{u} (Fin 1)) B) _
              (AffineSpace.oneSection_comp_map u)).hom.app _) ≫
            (L((u)^*[ModuleCat.{u + 1} Λ])).map θ.hom) ≫ φ.hom := by
  obtain ⟨B', u, hu, hsurj, hsep, ⟨e⟩⟩ := D.exists_etale_nonempty_iso_familyObject Λ aB
  have : HasInvertibleExponent Λ B' := .of_hom u
  obtain ⟨c⟩ := nonempty_iso_sectionInvariant_affineSpace Λ d B' (u ≫ aB)
  let i₁' := AffineSpace.oneSection (ULift.{u} (Fin 1)) B'
  let ε' := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) i₁' _
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B')
  let dF := ((leftDerivedUpperStarComp _ i₁' (AffineSpace.map (ULift.{u} (Fin 1)) u)).app
      (D.familyObject Λ)).symm ≪≫
    (leftDerivedUpperStarComp _ u (AffineSpace.oneSection (ULift.{u} (Fin 1)) B) _
      (AffineSpace.oneSection_comp_map u)).app (D.familyObject Λ)
  refine ⟨B', u, hu, hsurj, hsep, ⟨c⟩, e,
    (dF ≪≫ (L((u)^*[ModuleCat.{u + 1} Λ])).mapIso θ).symm ≪≫
      (L((i₁')^*[ModuleCat.{u + 1} Λ])).mapIso e ≪≫ ε'.app _, ?_⟩
  exact (Iso.hom_inv_id_assoc (dF ≪≫ (L((u)^*[ModuleCat.{u + 1} Λ])).mapIso θ) _).symm

include D aB in
/-- Blueprint `prop-pur-dnc-family-constancy`: The deformation family is constant along the
affine line

*Clause (1) for the section invariant.* There is a finite locally constant sheaf `L₁` on `B`,
free of rank one at every geometric point, with `𝒞(g, s) ≅ L₁(d)[2d]`: over the étale cover of
`lem-pur-dnc-section-geometry` (2) it is the standard section invariant `Λ(d)[2d]`
(`sk-prop-an`), and `lem-pur-concentrated-complex-shift` applies. -/
theorem exists_nonempty_iso_sectionInvariant_twistShift :
    ∃ L : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsFiniteLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ B),
        Nonempty ((pointSmallEtale x).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      Nonempty (sectionInvariant Λ g s ≅
        (twistShift Λ B d).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) := by
  obtain ⟨θ⟩ := D.nonempty_iso_leftDerivedUpperStar_oneSection_familyObject Λ
  obtain ⟨B', u, hu, hsurj, -, ⟨c⟩, -, φ, -⟩ := D.exists_etale_familyObject_data Λ aB θ
  exact exists_nonempty_iso_twistShift_of_leftDerivedUpperStar_iso Λ u d _ (φ ≪≫ c)

include aB in
/-- Blueprint `prop-pur-dnc-family-constancy`: The deformation family is constant along the
affine line

*Clause (1), the family is a shift of a lisse line.* There is a finite locally constant sheaf
`L_F` on `𝔸¹_B`, free of rank one at every geometric point, with `F ≅ L_F(d)[2d]`: over the
étale cover of `lem-pur-dnc-section-geometry` (2) the family is the pullback of the standard
section invariant `Λ(d)[2d]` (`sk-prop-an`), and `lem-pur-concentrated-complex-shift`
applies. The same statement for `𝒞(g, s)` is
`exists_nonempty_iso_sectionInvariant_twistShift`. -/
theorem exists_nonempty_iso_familyObject_twistShift :
    ∃ L : Sheaf 𝔸(ULift.{u} (Fin 1); B).smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsFiniteLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ 𝔸(ULift.{u} (Fin 1); B)),
        Nonempty ((pointSmallEtale x).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      Nonempty (D.familyObject Λ ≅ (twistShift Λ 𝔸(ULift.{u} (Fin 1); B) d).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) := by
  obtain ⟨θ⟩ := D.nonempty_iso_leftDerivedUpperStar_oneSection_familyObject Λ
  obtain ⟨B', u, hu, hsurj, -, ⟨c⟩, e, -⟩ := D.exists_etale_familyObject_data Λ aB θ
  have : _root_.AlgebraicGeometry.Etale (AffineSpace.map (ULift.{u} (Fin 1)) u) :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale)
      (AffineSpace.isPullback_map u).flip hu
  have : Surjective (AffineSpace.map (ULift.{u} (Fin 1)) u) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (AffineSpace.isPullback_map u).flip hsurj
  exact exists_nonempty_iso_twistShift_of_leftDerivedUpperStar_iso Λ
    (AffineSpace.map (ULift.{u} (Fin 1)) u) d _
    (e ≪≫ (L((𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).mapIso c ≪≫
      leftDerivedUpperStarTwistShiftIso Λ _ d _ ≪≫
      (twistShift Λ _ d).mapIso (leftDerivedUpperStarConstantComplexIso Λ _))

include aB in
/-- Blueprint `prop-pur-dnc-family-constancy`: The deformation family is constant along the
affine line

*Clause (2), constancy along the affine line.* For the projection `a : 𝔸¹_B ⟶ B` there is an
isomorphism

`κ : F ≅ La^* 𝒞(g, s)`,

so that the family object is the pullback of its own fibre `𝒞(g, s)` at `t = 1`.

Over the étale cover `u : B' ⟶ B` of `lem-pur-dnc-section-geometry` (2) the family is
`La'^* 𝒞₀` for the standard section invariant `𝒞₀ ≅ Λ(d)[2d]`, which gives the local shape
and, through the fibre `φ : Lu^* 𝒞(g, s) ≅ 𝒞₀` at `t = 1`, a comparison
`κ' : Lv₁^* F ≅ La'^* Lu^* 𝒞(g, s)` normalized at `t = 1`. These glue by `𝔸¹`-invariance
(`prop-pur-a1-invariance`). -/
theorem nonempty_iso_familyObject_leftDerivedUpperStar :
    Nonempty (D.familyObject Λ ≅
      (L((𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).obj (sectionInvariant Λ g s)) := by
  obtain ⟨θ⟩ := D.nonempty_iso_leftDerivedUpperStar_oneSection_familyObject Λ
  obtain ⟨B', u, hu, hsurj, hsep, ⟨c⟩, e, φ, h⟩ := D.exists_etale_familyObject_data Λ aB θ
  let a' := 𝔸(ULift.{u} (Fin 1); B') ↘ B'
  let ε' := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) _ a'
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B')
  -- the local shape: `Lv₁^* F ≅ La'^* Λ(d)[2d] ≅ Λ(d)[2d]`
  have hF : ∃ L : Sheaf 𝔸(ULift.{u} (Fin 1); B').smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsFiniteLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ 𝔸(ULift.{u} (Fin 1); B')),
        Nonempty ((pointSmallEtale x).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      ∃ m n : ℤ, Nonempty
        ((L((AffineSpace.map (ULift.{u} (Fin 1)) u)^*[ModuleCat.{u + 1} Λ])).obj
            (D.familyObject Λ) ≅
          ((tateTwist Λ _ m).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj L))⟦n⟧) :=
    ⟨𝟙_ _, inferInstance, fun Ω _ _ x ↦
      ⟨((pointSmallEtale x).uliftSheafFiberIso _).symm.app _ ≪≫ sheafFiberUnitIso _ x⟩, d,
      2 * d, ⟨e ≪≫ (L((a')^*[ModuleCat.{u + 1} Λ])).mapIso c ≪≫
        leftDerivedUpperStarTwistShiftIso Λ _ d _ ≪≫
        (twistShift Λ _ d).mapIso (leftDerivedUpperStarConstantComplexIso Λ _ ≪≫
          constantComplexIsoSingleFunctor Λ _)⟩⟩
  -- the normalized local comparison `κ' = e ≫ La'^* φ⁻¹`
  have := hu; have := hsurj; have := hsep
  obtain ⟨κ, -, -⟩ := existsUnique_iso_leftDerivedUpperStar_of_etale Λ aB (D.familyObject Λ)
    (sectionInvariant Λ g s) θ u hF (e ≪≫ (L((a')^*[ModuleCat.{u + 1} Λ])).mapIso φ.symm) (by
      have hn := ε'.hom.naturality φ.inv
      dsimp at hn
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp,
        Category.assoc]
      rw [hn, reassoc_of% h]
      simp)
  exact ⟨κ⟩

include aB in
/-- Blueprint `prop-pur-dnc-family-constancy`: The deformation family is constant along the
affine line

*Clause (3), normalization and uniqueness.* For every identification
`θ : i₁^* F ≅ 𝒞(g, s)` of the fibre of the family at `t = 1` (for instance the base change
identification of `lem-pur-dnc-section-geometry` (1), see
`nonempty_iso_leftDerivedUpperStar_oneSection_familyObject`)
there is a unique isomorphism `κ : F ≅ La^* 𝒞(g, s)` restricting to `θ` at `t = 1`, under
`i₁^* a^* ≅ 𝟭`.

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
  obtain ⟨κ₀⟩ := D.nonempty_iso_familyObject_leftDerivedUpperStar Λ aB
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

Let `g : V ⟶ B` be smooth of pure relative dimension `d` with a closed section `s`, over a base
`B` separated of finite type over a field, let `N_s ⟶ B` be its normal cone with zero section
`0_N`, and let `g̃ : 𝒟_s V ⟶ 𝔸¹_B` be a deformation to the normal cone (the situation of
`sk-lem-geometry`). There is an isomorphism

`𝒞(g, s) ≅ 𝒞(π_N, 0_N)`

between the two section invariants. It is `i₀^*` of the comparison `κ : F ≅ La^* 𝒞(g, s)` of
`prop-pur-dnc-family-constancy` (2), the fibre `i₀^* F` being `𝒞(π_N, 0_N)` by base change
(`lem-pur-dnc-section-geometry` (1)). This is also blueprint `thm-pur-dnc-invariance`. -/
-- TODO(unify): sk-thm-dnc — add the normalization in coordinates and the base-change clause.
theorem nonempty_iso_sectionInvariant_normalCone [HasTateTwist.IsNormalized Λ] (d : ℕ)
    (g : V ⟶ B) [SmoothOfRelativeDimension d g] [HasCompactification g] (s : B ⟶ V)
    (N : Scheme.Hom.NormalConeData d s) [HasCompactification N.proj]
    (D : Scheme.Hom.DeformationToNormalConeData d g s N) {k : Type u} [Field k]
    (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ B] :
    Nonempty (sectionInvariant Λ g s ≅ sectionInvariant Λ N.proj N.zeroSection) := by
  have := D.hasInvertibleExponent_scheme Λ
  obtain ⟨κ⟩ := D.nonempty_iso_familyObject_leftDerivedUpperStar Λ aB
  obtain ⟨e₀⟩ := nonempty_iso_leftDerivedUpperStar_sectionInvariant Λ (d := d) D.proj
    D.isPullback_zeroFibre D.sect N.zeroSection D.comp_zeroFibre
  exact ⟨((leftDerivedUpperStarCompSectionIso _ _ _
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) B)).app _).symm ≪≫
    (L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).mapIso κ.symm ≪≫
    e₀⟩

/-- Blueprint `sk-thm-dnc`: DNC invariance of the section dualizing line

*The comparison for an arbitrary normal cone datum*, `𝒞(g, s) ≅ 𝒞(π_N, 0_N)` for every
`N : NormalConeData d s`, without a deformation datum. This is the form smooth purity
(`sk-thm-smooth-purity`) uses as long as `AlgebraicGeometry.Scheme.Hom.NormalConeData` is not
tied to `s`: there `N` is the trivial bundle `𝔸^d`, for which no deformation datum need exist
(see `AlgebraicGeometry.Scheme.Hom.nonempty_deformationToNormalConeData`), so
`nonempty_iso_sectionInvariant_normalCone` does not apply.

It is stronger than the blueprint, which takes `N` to be the normal cone of `s`, but it is true:
both sides are `Λ_B(d)[2d]`, by smooth purity for `g` and for `π_N`. -/
-- TODO(unify): sk-thm-dnc — remove once `NormalConeData` is the normal cone of `s` (branch
-- `prove2/sk-thm-smooth-purity-2`); smooth purity then uses
-- `nonempty_iso_sectionInvariant_normalCone` with the datum of
-- `AlgebraicGeometry.Scheme.Hom.nonempty_deformationToNormalConeData`.
theorem nonempty_iso_sectionInvariant_normalConeData (d : ℕ) (g : V ⟶ B)
    [SmoothOfRelativeDimension d g] [HasCompactification g] (s : B ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 B) (N : Scheme.Hom.NormalConeData d s)
    [HasCompactification N.proj] [HasInvertibleExponent Λ B] :
    Nonempty (sectionInvariant Λ g s ≅ sectionInvariant Λ N.proj N.zeroSection) :=
  sorry

end Etale

end AlgebraicGeometry
