/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionSupports
public import WeilConjectures.SixFunctors.Etale.Derived.CoeffCompatibleMate

/-!
# The reduction of coefficients and the exceptional functors

Let `ρ : Λ →+* Λ'` be a surjective morphism of finite coefficient rings with principal kernel and
`Ψ = - ⊗ᴸ_Λ Λ'` the derived extension of scalars (`AlgebraicGeometry.Etale.derivedExtendScalars`),
left adjoint to the restriction of scalars `Res`. For `f : X ⟶ Y` admitting a compactification,
over a quasi-compact `Y`, `Res` commutes with `Rf_!`
(`AlgebraicGeometry.Etale.derivedRestrictScalarsCompRightDerivedLowerShriekIso`); this file
constructs:

* the comparison `β_f : Ψ_Y ∘ Rf_! ⟶ Rf_! ∘ Ψ_X`, the transpose under `Ψ ⊣ Res` of the
  commutation of `Res` with `Rf_!` (`AlgebraicGeometry.Etale.derivedExtendScalarsLowerShriekMap`);
* when `β_f` is an isomorphism, the comparison `c_f : Ψ_X ∘ Rf^! ⟶ Rf^! ∘ Ψ_Y`, the mate of `β_f⁻¹`
  under `Rf_! ⊣ Rf^!` (`AlgebraicGeometry.Etale.derivedExtendScalarsRightDerivedUpperShriekMap`).

For a closed immersion `i`, `β_i` is the isomorphism
`AlgebraicGeometry.Etale.derivedExtendScalarsLowerShriekIso` (built from the commutation of `Ψ`
with `Li^*` and `Ri_! ≅ Ri_*`), as soon as `Ri_! ≅ Ri_*` is compatible with the commutations of
`Res` (`AlgebraicGeometry.Etale.derivedExtendScalarsLowerShriekMap_eq`); hence `c_i` is
`AlgebraicGeometry.Etale.derivedExtendScalarsUpperShriekMap` (see
`WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionCanonical`).
The comparisons `c` are compatible with the composition isomorphisms of `R^!` conjugate to
those of `R_!`, with `R(𝟙)^! ≅ 𝟭` and with the base change maps of `R^!`; all of these are
deduced from the corresponding compatibilities of the commutations of `Res` with `R_!` by the
calculus of `WeilConjectures.SixFunctors.Etale.Derived.CoeffCompatibleMate`.

## Main definitions

- `AlgebraicGeometry.Etale.derivedExtendScalarsLowerShriekMap`: `Rf_! ⋙ Ψ ⟶ Ψ ⋙ Rf_!`.
- `AlgebraicGeometry.Etale.derivedExtendScalarsRightDerivedUpperShriekMap`: `Rf^! ⋙ Ψ ⟶ Ψ ⋙ Rf^!`.

## Main statements

- `AlgebraicGeometry.Etale.derivedExtendScalarsLowerShriekMap_eq`: for a closed immersion, `β`
  is `derivedExtendScalarsLowerShriekIso`.
- `map_conjugateIsoEquiv_comp_derivedExtendScalarsRightDerivedUpperShriekMap`: compatibility
  with composition.
- `AlgebraicGeometry.Etale.map_rightDerivedUpperShriekIdIso_hom_app`: compatibility with
  `R(𝟙)^! ≅ 𝟭`.
- `AlgebraicGeometry.Etale.derivedExtendScalarsRightDerivedUpperShriekMap_baseChange`:
  compatibility with the base change maps of `R^!`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})

section LowerShriek

variable [Finite Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]

/-- The comparison `β_f : Ψ_Y(Rf_! M) ⟶ Rf_!(Ψ_X M)` of the derived extension of scalars with the
compactly supported direct image: the transpose, under `Ψ ⊣ Res`, of the commutation
`Res ⋙ Rf_! ≅ Rf_! ⋙ Res`
(`AlgebraicGeometry.Etale.derivedRestrictScalarsCompRightDerivedLowerShriekIso`). -/
noncomputable abbrev derivedExtendScalarsLowerShriekMap :
    R(f)_![ModuleCat.{u + 1} Λ] ⋙ derivedExtendScalars hρ ha Y ⟶
      derivedExtendScalars hρ ha X ⋙ R(f)_![ModuleCat.{u + 1} Λ'] :=
  coeffMate (derivedExtendScalarsAdjunction hρ ha X) (derivedExtendScalarsAdjunction hρ ha Y)
    (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ f)

/-- The defining property of `AlgebraicGeometry.Etale.derivedExtendScalarsLowerShriekMap`: its
transpose is `Rf_!(M ⟶ Res Ψ M) ≫ (Rf_! Res ≅ Res Rf_!)`. -/
@[reassoc]
lemma unit_app_comp_map_derivedExtendScalarsLowerShriekMap_app (M : 𝐃(X, Λ)) :
    (derivedExtendScalarsAdjunction hρ ha Y).unit.app ((R(f)_![ModuleCat.{u + 1} Λ]).obj M) ≫
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ).map
          ((derivedExtendScalarsLowerShriekMap hρ ha f).app M) =
      (R(f)_![ModuleCat.{u + 1} Λ]).map ((derivedExtendScalarsAdjunction hρ ha X).unit.app M) ≫
        (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ f).hom.app
          ((derivedExtendScalars hρ ha X).obj M) :=
  unit_app_comp_map_coeffMate_app _ _ _ M

variable [Finite Λ'] [IsIso (derivedExtendScalarsLowerShriekMap hρ ha f)]

/-- The comparison `c_f : Ψ_X(Rf^! N) ⟶ Rf^!(Ψ_Y N)` of the derived extension of scalars with the
exceptional inverse image, when `β_f : Ψ ∘ Rf_! ⟶ Rf_! ∘ Ψ`
(`AlgebraicGeometry.Etale.derivedExtendScalarsLowerShriekMap`) is an isomorphism: the mate of
`β_f⁻¹` under the adjunctions `Rf_! ⊣ Rf^!`. -/
noncomputable def derivedExtendScalarsRightDerivedUpperShriekMap :
    R(f)^![Λ] ⋙ derivedExtendScalars hρ ha X ⟶ derivedExtendScalars hρ ha Y ⋙ R(f)^![Λ'] :=
  coeffUpperMate (derivedExtendScalarsAdjunction hρ ha X) (derivedExtendScalarsAdjunction hρ ha Y)
    (rightDerivedUpperShriekAdjunction Λ f) (rightDerivedUpperShriekAdjunction Λ' f)
    (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ f)

/-- The comparison `Ψ Rf^! ⟶ Rf^! Ψ` is compatible with the counits of `Rf_! ⊣ Rf^!`. -/
@[reassoc]
lemma map_derivedExtendScalarsRightDerivedUpperShriekMap_app_comp_counit (N : 𝐃(Y, Λ)) :
    (R(f)_![ModuleCat.{u + 1} Λ']).map
        ((derivedExtendScalarsRightDerivedUpperShriekMap hρ ha f).app N) ≫
      (rightDerivedUpperShriekAdjunction Λ' f).counit.app ((derivedExtendScalars hρ ha Y).obj N) =
    (inv (derivedExtendScalarsLowerShriekMap hρ ha f)).app ((R(f)^![Λ]).obj N) ≫
      (derivedExtendScalars hρ ha Y).map ((rightDerivedUpperShriekAdjunction Λ f).counit.app N) :=
  map_coeffUpperMate_app_comp_counit _ _ _ _ _ N

end LowerShriek

section ClosedImmersion

variable [Finite Λ] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

omit [Finite Λ] [IsClosedImmersion i] in
/-- The comparison `Ψ Ri_* ⟶ Ri_* Ψ` of a closed immersion, defined as the mate of the commutation
of `Ψ` with `Li^*`, is the transpose of the commutation of `Res` with `Ri_*`. -/
lemma derivedExtendScalarsLowerStarMap_eq_coeffMate (d : ℕ)
    (hd : ∀ (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((((i)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F)) :
    derivedExtendScalarsLowerStarMap hρ ha i =
      coeffMate (derivedExtendScalarsAdjunction hρ ha Z) (derivedExtendScalarsAdjunction hρ ha X)
        (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ i d hd) := by
  have : IsIso (coeffMate (derivedExtendScalarsAdjunction hρ ha X)
      (derivedExtendScalarsAdjunction hρ ha Z) (leftDerivedUpperStarRestrictScalarsIso ρ i)) :=
    isIso_derivedExtendScalarsPullbackMap hρ ha i
  exact coeffUpperMate_eq_coeffMate (derivedExtendScalarsAdjunction hρ ha X)
    (derivedExtendScalarsAdjunction hρ ha Z) (derivedUpperStarLowerStarAdjunction _ i)
    (derivedUpperStarLowerStarAdjunction _ i) (leftDerivedUpperStarRestrictScalarsIso ρ i)
    (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ i d hd)
    (mateEquiv_derivedUpperStarLowerStarAdjunction_leftDerivedUpperStarRestrictScalarsIso ρ i d hd)

variable [CompactSpace X]

/-- **For a closed immersion `i`, the comparison `β_i` is the commutation of `Ψ` with `Ri_!`
built from `Li^*`** (`AlgebraicGeometry.Etale.derivedExtendScalarsLowerShriekIso`), as soon as the
identification `Ri_! ≅ Ri_*` is compatible with the commutations of `Res` with `Ri_!` and `Ri_*`. -/
lemma derivedExtendScalarsLowerShriekMap_eq (d : ℕ)
    (hd : ∀ (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((((i)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    (hr : CoeffCompatible (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ i)
      (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ i d hd)
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i).hom
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ') i).hom) :
    derivedExtendScalarsLowerShriekMap hρ ha i =
      (derivedExtendScalarsLowerShriekIso hρ ha i).hom := by
  ext M
  have h := hr.map_app_comp_coeffMate_app (derivedExtendScalarsAdjunction hρ ha Z)
    (derivedExtendScalarsAdjunction hρ ha X) M
  rw [← derivedExtendScalarsLowerStarMap_eq_coeffMate hρ ha i d hd] at h
  rw [derivedExtendScalarsLowerShriekIso_hom, NatTrans.comp_app, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, reassoc_of% h, Iso.hom_inv_id_app,
    Category.comp_id]

end ClosedImmersion

section Coherence

variable [Finite Λ] [Finite Λ']

/-- **The comparisons `c` are compatible with composition.** For `f ≫ g = h`, if the composition
isomorphism `R(h)_! ≅ Rf_! ⋙ Rg_!` is compatible with the commutations of `Res` with the lower
shrieks, then the conjugate isomorphisms `Rg^! ⋙ Rf^! ≅ R(h)^!` intertwine `c_h` with the
composite of `c_f` and `c_g`. -/
lemma map_conjugateIsoEquiv_comp_derivedExtendScalarsRightDerivedUpperShriekMap
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (h : X ⟶ S) (w : f ≫ g = h)
    [HasCompactification f] [HasCompactification g] [HasCompactification h] [QuasiCompact h]
    [CompactSpace Y] [CompactSpace S] [IsIso (derivedExtendScalarsLowerShriekMap hρ ha f)]
    [IsIso (derivedExtendScalarsLowerShriekMap hρ ha g)]
    [IsIso (derivedExtendScalarsLowerShriekMap hρ ha h)]
    (he : CoeffCompatible (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ h)
      (pasteTwoSquaresIso (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ f)
        (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ g))
      (rightDerivedLowerShriekCompIsoOfEq Λ f g h w).hom
      (rightDerivedLowerShriekCompIsoOfEq Λ' f g h w).hom) (N : 𝐃(S, Λ)) :
    (derivedExtendScalars hρ ha X).map ((conjugateIsoEquiv
        ((rightDerivedUpperShriekAdjunction Λ f).comp (rightDerivedUpperShriekAdjunction Λ g))
        (rightDerivedUpperShriekAdjunction Λ h)
        (rightDerivedLowerShriekCompIsoOfEq Λ f g h w)).hom.app N) ≫
        (derivedExtendScalarsRightDerivedUpperShriekMap hρ ha h).app N =
      (derivedExtendScalarsRightDerivedUpperShriekMap hρ ha f).app ((R(g)^![Λ]).obj N) ≫
        (R(f)^![Λ']).map ((derivedExtendScalarsRightDerivedUpperShriekMap hρ ha g).app N) ≫
          (conjugateIsoEquiv
            ((rightDerivedUpperShriekAdjunction Λ' f).comp (rightDerivedUpperShriekAdjunction Λ' g))
            (rightDerivedUpperShriekAdjunction Λ' h)
            (rightDerivedLowerShriekCompIsoOfEq Λ' f g h w)).hom.app
              ((derivedExtendScalars hρ ha S).obj N) :=
  map_conjugateIsoEquiv_comp_coeffUpperMate (derivedExtendScalarsAdjunction hρ ha X)
    (derivedExtendScalarsAdjunction hρ ha Y) (derivedExtendScalarsAdjunction hρ ha S)
    (rightDerivedUpperShriekAdjunction Λ f) (rightDerivedUpperShriekAdjunction Λ' f)
    (rightDerivedUpperShriekAdjunction Λ g) (rightDerivedUpperShriekAdjunction Λ' g)
    (rightDerivedUpperShriekAdjunction Λ h) (rightDerivedUpperShriekAdjunction Λ' h)
    (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ f)
    (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ g)
    (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ h) he N

omit [Finite Λ'] in
/-- `R(𝟙 X)^! ≅ 𝟭` is, by definition, the right adjoint of `R(𝟙 X)_! ≅ 𝟭`. -/
lemma rightDerivedUpperShriekIdIso_eq (X : Scheme.{u}) :
    rightDerivedUpperShriekIdIso Λ X = (rightDerivedUpperShriekAdjunction Λ (𝟙 X)).rightAdjointUniq
      (Adjunction.id.ofNatIsoLeft (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X).symm) :=
  rfl

/-- **The comparison `c` is compatible with `R(𝟙)^! ≅ 𝟭`**, as soon as `R(𝟙)_! ≅ 𝟭` is compatible
with the commutation of `Res` with `R(𝟙)_!`. -/
lemma map_rightDerivedUpperShriekIdIso_hom_app (X : Scheme.{u}) [CompactSpace X]
    [IsIso (derivedExtendScalarsLowerShriekMap hρ ha (𝟙 X))]
    (hδ : CoeffCompatible (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ (𝟙 X))
      (Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)
      (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X).hom
      (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ') X).hom) (N : 𝐃(X, Λ)) :
    (derivedExtendScalars hρ ha X).map ((rightDerivedUpperShriekIdIso Λ X).hom.app N) =
      (derivedExtendScalarsRightDerivedUpperShriekMap hρ ha (𝟙 X)).app N ≫
        (rightDerivedUpperShriekIdIso Λ' X).hom.app ((derivedExtendScalars hρ ha X).obj N) := by
  rw [rightDerivedUpperShriekIdIso_eq, rightDerivedUpperShriekIdIso_eq]
  exact map_rightAdjointUniq_hom_app_eq (derivedExtendScalarsAdjunction hρ ha X)
    (rightDerivedUpperShriekAdjunction Λ (𝟙 X)) (rightDerivedUpperShriekAdjunction Λ' (𝟙 X))
    (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ (𝟙 X)) hδ N

/-- **The comparisons `c` are compatible with the base change maps of `R^!`.** For a cartesian
square `g' ≫ f = f' ≫ g`, the base change maps `Lg'^* Rf^! ⟶ Rf'^! Lg^*`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`) over `Λ` and `Λ'` are
intertwined by `c_f`, `c_{f'}` and the commutations of `Ψ` with `Lg^*`, `Lg'^*`. -/
lemma derivedExtendScalarsRightDerivedUpperShriekMap_baseChange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f'] [CompactSpace Y]
    [CompactSpace Y'] [IsIso (derivedExtendScalarsLowerShriekMap hρ ha f)]
    [IsIso (derivedExtendScalarsLowerShriekMap hρ ha f')] (sq : IsPullback g' f' f g)
    (N : 𝐃(Y, Λ)) :
    (derivedExtendScalarsPullbackMap hρ ha g').app ((R(f)^![Λ]).obj N) ≫
        (L((g')^*[ModuleCat.{u + 1} Λ'])).map
          ((derivedExtendScalarsRightDerivedUpperShriekMap hρ ha f).app N) ≫
          (rightDerivedUpperShriekBaseChangeMap Λ' sq).app ((derivedExtendScalars hρ ha Y).obj N) =
      (derivedExtendScalars hρ ha X').map ((rightDerivedUpperShriekBaseChangeMap Λ sq).app N) ≫
        (derivedExtendScalarsRightDerivedUpperShriekMap hρ ha f').app
          ((L((g)^*[ModuleCat.{u + 1} Λ])).obj N) ≫
          (R(f')^![Λ']).map ((derivedExtendScalarsPullbackMap hρ ha g).app N) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ' sq
  exact coeffMate_app_comp_map_coeffUpperMate_app_comp _ _ _ _ _ _ _ _ _ _
    (leftDerivedUpperStarRestrictScalarsIso ρ g') (leftDerivedUpperStarRestrictScalarsIso ρ g) _ _
    (coeffCompatible_rightDerivedLowerShriekBaseChangeMap ρ sq) N

end Coherence

end Etale

end AlgebraicGeometry
