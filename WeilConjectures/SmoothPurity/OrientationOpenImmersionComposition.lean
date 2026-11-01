/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekCompositionIntegral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionOpenImmersion
public import WeilConjectures.SmoothPurity.OrientationFinite
public import WeilConjectures.SmoothPurity.OrientationOpenImmersionCompositionPasting

/-!
# Integral orientations and composition with an open immersion

Let `f : X ⟶ Y` be smooth of pure relative dimension `d` and `j : Y ⟶ Z` an open immersion of
separated `k`-schemes of finite type, and `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` with ring of
integers `𝒪_E`. This file builds the integral counterpart of the orientation of `f ≫ j` induced
by an orientation of `f`:

- `ProEtale.CondensedRing.boundedConstructibleUpperShriekComp_padicIntegers`: the composition
  isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` on bounded constructible `𝒪_E`-complexes, the conjugate
  of the composition isomorphism of the lower shriek
  (`boundedConstructibleLowerShriekComp_padicIntegers`).
- `ProEtale.CondensedRing.boundedConstructibleUpperShriekUnitIso_padicIntegers`: purity for an
  open immersion, `Rj^! 𝒪_{E,Z} ≅ 𝒪_{E,Y}`.
- `ProEtale.CondensedRing.integralCompOpenImmersionOrientation`: for
  `ψ : 𝒪_{E,X}(d)[2d] ⟶ Rf^! 𝒪_{E,Y}`, the morphism
  `𝒪_{E,X}(d)[2d] ⟶ Rf^! 𝒪_{E,Y} ≅ Rf^! Rj^! 𝒪_{E,Z} ≅ R(f ≫ j)^! 𝒪_{E,Z}`.

## Unproved steps

The following steps are stated and `sorry`ed:

- `ProEtale.CondensedRing.isIntegralSmoothOrientation_integralCompOpenImmersionOrientation`:
  if `ψ` lifts the canonical finite orientations of `f`, then the induced morphism lifts those of
  `f ≫ j`. This is the finite statement that the orientation of the diagonal argument is
  compatible with composition with an open immersion, together with the compatibility of the
  reduction comparisons `etaleReductionUpperShriekIso` with the composition isomorphisms.
- `ProEtale.CondensedRing.integersToPadicAlgClUpperShriekUnitIso_comp_openImmersion`: the
  coefficient comparison `T(Rf^! 𝒪_E) ≅ Rf^! ℚ̄_ℓ` (`integersToPadicAlgClUpperShriekUnitIso`) is
  compatible with the composition isomorphisms and with purity for the open immersion `j`.
  It follows from the pasting lemma `CategoryTheory.map_map_comp_comp_exchange_eq'` applied to
  `boundedConstructibleUpperShriekExtendScalars_comp_app`,
  `boundedConstructibleUpperShriekToPadicAlgCl_comp_app` (proved from the two lower-shriek
  compatibilities below) and
  `extendScalars_map_upperShriekUnit_comp_integersToPadicAlgClUpperShriekUnitIso`, but the
  instantiation does not elaborate yet: the unit objects of the two presentations of the
  `E`-complexes (`PadicSubfieldConstructible` and `Dᵇc(-)⟦E⟧`) occurring in
  `integersToPadicAlgClUpperShriekUnitIso` exceed the recursion depth when unified.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekExtendScalarsIso_comp` and
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekToPadicAlgClIso_comp`: the coefficient
  comparisons of `Rf_!` are compatible with the composition isomorphisms.
- `extendScalars_map_upperShriekUnit_comp_integersToPadicAlgClUpperShriekUnitIso`
  (moved here from `OrientationOpenImmersion`): the coefficient comparison of `Rj^!` and the units.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Composition

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]
  (f : X ⟶ Y) (g : Y ⟶ S)

/-- The composition isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` for the exceptional inverse image on
bounded constructible `𝒪_E`-complexes: the conjugate of
`boundedConstructibleLowerShriekComp_padicIntegers` under the adjunctions
`R(f ≫ g)_! ⊣ R(f ≫ g)^!` and `Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`. -/
noncomputable def boundedConstructibleUpperShriekComp_padicIntegers :
    PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E (f ≫ g) ≅
      PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E g ⋙
        PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E f :=
  conjugateIsoEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E (f ≫ g))
    ((PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f).comp
      (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E g))
    (boundedConstructibleLowerShriekComp_padicIntegers ℓ E f g).symm

end Composition

section OpenImmersion

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {U X : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- **Purity for an open immersion**, `Rj^! 𝒪_{E,X} ≅ 𝒪_{E,U}`, on bounded constructible
`𝒪_E`-complexes: the isomorphism `Rj^! ≅ j^*` of
`boundedConstructibleUpperShriekIsoUpperStar_padicIntegers` at the unit, followed by the unit
isomorphism of the monoidal functor `j^*`. -/
noncomputable def boundedConstructibleUpperShriekUnitIso_padicIntegers :
    (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E j).obj
        (𝟙_ (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧)) ≅
      𝟙_ (Dᵇc(U.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :=
  (boundedConstructibleUpperShriekIsoUpperStar_padicIntegers ℓ E j).app _ ≪≫
    (Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ j)).symm

end OpenImmersion

section ExchangeComposition

variable (E : PadicAlgCl.FiniteIntermediateField ℓ) {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]
  (f : X ⟶ Y) (g : Y ⟶ S)

/-- **(Shriek) for `𝒪_E ⟶ E` is compatible with composition**: the coefficient comparison
`R(f ≫ g)_! ⋙ T ≅ T ⋙ R(f ≫ g)_!` (`boundedConstructibleLowerShriekExtendScalarsIso`) is
the comparisons of `f` and `g` pasted along the composition isomorphisms
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` (`boundedConstructibleLowerShriekComp_padicIntegers`,
`boundedConstructibleLowerShriekComp`). -/
theorem boundedConstructibleLowerShriekExtendScalarsIso_comp
    (M : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    (boundedConstructibleLowerShriekExtendScalarsIso ℓ E (f ≫ g)).hom.app M ≫
        (boundedConstructibleLowerShriekComp ℓ E f g).hom.app
          ((boundedConstructibleExtendScalars X.left ℓ E).obj M) =
      (boundedConstructibleExtendScalars S.left ℓ E).map
          ((boundedConstructibleLowerShriekComp_padicIntegers ℓ E.1 f g).hom.app M) ≫
        (boundedConstructibleLowerShriekExtendScalarsIso ℓ E g).hom.app
          ((PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 f).obj M) ≫
        (ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E g).map
          ((boundedConstructibleLowerShriekExtendScalarsIso ℓ E f).hom.app M) :=
  sorry

/-- **(Shriek) for `E ⟶ ℚ̄_ℓ` is compatible with composition**: the coefficient comparison
`R(f ≫ g)_! ⋙ T ≅ T ⋙ R(f ≫ g)_!` (`boundedConstructibleLowerShriekToPadicAlgClIso`) is the
comparisons of `f` and `g` pasted along the composition isomorphisms
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` (`boundedConstructibleLowerShriekComp`,
`boundedConstructibleLowerShriekComp_padicAlgCl`). -/
theorem boundedConstructibleLowerShriekToPadicAlgClIso_comp
    (M : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E (f ≫ g)).hom.app M ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app
          ((boundedConstructibleToPadicAlgCl X.left ℓ E).obj M) =
      (boundedConstructibleToPadicAlgCl S.left ℓ E).map
          ((boundedConstructibleLowerShriekComp ℓ E f g).hom.app M) ≫
        (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E g).hom.app
          ((ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E f).obj M) ≫
        (boundedConstructibleLowerShriek ℓ g).map
          ((boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f).hom.app M) :=
  sorry

/-- The exchange for `f^!` along `𝒪_E ⟶ E` (`boundedConstructibleUpperShriekExtendScalars`) is
compatible with the composition isomorphisms `Rg^! ⋙ Rf^! ≅ R(f ≫ g)^!`: the mate of
`boundedConstructibleLowerShriekExtendScalarsIso_comp`. -/
theorem boundedConstructibleUpperShriekExtendScalars_comp_app
    (N : Dᵇc(S.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    (boundedConstructibleExtendScalars X.left ℓ E).map
        ((boundedConstructibleUpperShriekComp_padicIntegers ℓ E.1 f g).inv.app N) ≫
      (boundedConstructibleUpperShriekExtendScalars ℓ E (f ≫ g)).app N =
    (boundedConstructibleUpperShriekExtendScalars ℓ E f).app
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 g).obj N) ≫
      (ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E f).map
        ((boundedConstructibleUpperShriekExtendScalars ℓ E g).app N) ≫
      (boundedConstructibleUpperShriekComp ℓ E f g).inv.app
        ((boundedConstructibleExtendScalars S.left ℓ E).obj N) := by
  have h := exchange_conjugateIsoEquiv_comp_app
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 f)
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 g)
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 (f ≫ g))
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E g)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E (f ≫ g))
    (boundedConstructibleLowerShriekExtendScalarsIso ℓ E f)
    (boundedConstructibleLowerShriekExtendScalarsIso ℓ E g)
    (boundedConstructibleLowerShriekExtendScalarsIso ℓ E (f ≫ g))
    (boundedConstructibleLowerShriekComp_padicIntegers ℓ E.1 f g)
    (boundedConstructibleLowerShriekComp ℓ E f g)
    (boundedConstructibleLowerShriekExtendScalarsIso_comp ℓ E f g) N
  simp only [← boundedConstructibleUpperShriekExtendScalars_eq_mateEquiv] at h
  have e₀ : (boundedConstructibleUpperShriekComp_padicIntegers ℓ E.1 f g).inv =
      (conjugateIsoEquiv
        ((PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 f).comp
        (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 g))
        (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 (f ≫ g))
        (boundedConstructibleLowerShriekComp_padicIntegers ℓ E.1 f g)).hom := rfl
  have e₁ : (boundedConstructibleUpperShriekComp ℓ E f g).inv =
      (conjugateIsoEquiv
        ((ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f).comp
        (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E g))
        (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E (f ≫ g))
        (boundedConstructibleLowerShriekComp ℓ E f g)).hom := rfl
  simp only [← e₀, ← e₁] at h
  with_reducible exact h

/-- The exchange for `f^!` along `E ⟶ ℚ̄_ℓ` (`boundedConstructibleUpperShriekToPadicAlgCl`) is
compatible with the composition isomorphisms `Rg^! ⋙ Rf^! ≅ R(f ≫ g)^!`: the mate of
`boundedConstructibleLowerShriekToPadicAlgClIso_comp`. -/
theorem boundedConstructibleUpperShriekToPadicAlgCl_comp_app
    (N : Dᵇc(S.left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleToPadicAlgCl X.left ℓ E).map
        ((boundedConstructibleUpperShriekComp ℓ E f g).inv.app N) ≫
      (boundedConstructibleUpperShriekToPadicAlgCl ℓ E (f ≫ g)).app N =
    (boundedConstructibleUpperShriekToPadicAlgCl ℓ E f).app
        ((ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E g).obj N) ≫
      (boundedConstructibleUpperShriek ℓ f).map
        ((boundedConstructibleUpperShriekToPadicAlgCl ℓ E g).app N) ≫
      (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f g).inv.app
        ((boundedConstructibleToPadicAlgCl S.left ℓ E).obj N) := by
  have h := exchange_conjugateIsoEquiv_comp_app
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E g)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E (f ≫ g))
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleUpperShriekAdjunction ℓ g)
    (boundedConstructibleUpperShriekAdjunction ℓ (f ≫ g))
    (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f)
    (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E g)
    (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E (f ≫ g))
    (boundedConstructibleLowerShriekComp ℓ E f g)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g)
    (boundedConstructibleLowerShriekToPadicAlgClIso_comp ℓ E f g) N
  simp only [← boundedConstructibleUpperShriekToPadicAlgCl_eq_mateEquiv] at h
  have e₁ : (boundedConstructibleUpperShriekComp ℓ E f g).inv =
      (conjugateIsoEquiv
        ((ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f).comp
        (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E g))
        (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E (f ≫ g))
        (boundedConstructibleLowerShriekComp ℓ E f g)).hom := rfl
  have e₂ : (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f g).inv =
      (conjugateIsoEquiv
        ((boundedConstructibleUpperShriekAdjunction ℓ f).comp
        (boundedConstructibleUpperShriekAdjunction ℓ g))
        (boundedConstructibleUpperShriekAdjunction ℓ (f ≫ g))
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g)).hom := rfl
  simp only [← e₁, ← e₂] at h
  with_reducible exact h

/-- The coefficient comparison `T(Rf^! 𝒪_E) ≅ Rf^! ℚ̄_ℓ` as a composite of the exchanges for `f^!`
and of the unit comparisons. -/
lemma integersToPadicAlgClUpperShriekUnitIso_hom :
    (integersToPadicAlgClUpperShriekUnitIso ℓ E f).hom =
      (constructibleToPadicAlgCl X.left ℓ E).map
          ((boundedConstructibleUpperShriekExtendScalars ℓ E f).app (𝟙_ _) ≫
            (ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E f).map
              (Functor.Monoidal.εIso (boundedConstructibleExtendScalars Y.left ℓ E)).inv) ≫
        (boundedConstructibleUpperShriekToPadicAlgCl ℓ E f).app (𝟙_ _) ≫
        (boundedConstructibleUpperShriek ℓ f).map
          (Functor.Monoidal.εIso (constructibleToPadicAlgCl Y.left ℓ E)).inv := by
  unfold integersToPadicAlgClUpperShriekUnitIso
  have e : (boundedConstructibleUpperShriekExtendScalarsIso ℓ E f).hom =
    boundedConstructibleUpperShriekExtendScalars ℓ E f := rfl
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, asIso_hom, Iso.symm_hom, e]

end ExchangeComposition

section OpenImmersionUnit

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (j : X ⟶ Y) [IsOpenImmersion j.left] (E : PadicAlgCl.FiniteIntermediateField ℓ) [NeZero (ℓ : k)]

/-- The unit comparison `𝟙 ≅ T 𝟙` of the extension of scalars `T` along `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`, for
the monoidal functors `boundedConstructibleExtendScalars` and `constructibleToPadicAlgCl`. -/
noncomputable def integersToPadicAlgClUnitIso (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] [IsSeparated T.hom] :
    𝟙_ (Dᵇc(T.left)⟦Profinite.padicAlgClRingObj ℓ⟧) ≅
      (boundedConstructibleExtendScalars T.left ℓ E ⋙ constructibleToPadicAlgCl T.left ℓ E).obj
        (𝟙_ _) :=
  Functor.Monoidal.εIso (constructibleToPadicAlgCl T.left ℓ E) ≪≫
    (constructibleToPadicAlgCl T.left ℓ E).mapIso
      (Functor.Monoidal.εIso (boundedConstructibleExtendScalars T.left ℓ E))

/-- The coefficient comparison `T(Rj^! 𝒪_{E,Y}) ≅ Rj^! ℚ̄_ℓ,Y`
(`integersToPadicAlgClUpperShriekUnitIso`) of an open immersion `j` is compatible with the
identifications `Rj^! 𝒪_{E,Y} ≅ j^* 𝒪_{E,Y} ≅ 𝒪_{E,X}` and `Rj^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X`
(`boundedConstructibleUpperShriekUnitIso_padicAlgCl`) and with the unit comparison of `T`. -/
theorem extendScalars_map_upperShriekUnit_comp_integersToPadicAlgClUpperShriekUnitIso :
    (boundedConstructibleExtendScalars X.left ℓ E ⋙ constructibleToPadicAlgCl X.left ℓ E).map
        ((Functor.Monoidal.εIso
          (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ j)).hom ≫
          ((boundedConstructibleUpperShriekIsoUpperStar_padicIntegers ℓ E.1 j).app _).inv) ≫
      (integersToPadicAlgClUpperShriekUnitIso ℓ E j).hom =
    (integersToPadicAlgClUnitIso ℓ E X).inv ≫
      (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv :=
  sorry

end OpenImmersionUnit

variable {X Y Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]
  (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y) (j : Y ⟶ Z) [IsOpenImmersion j.left]
  (d : ℕ) [NeZero (ℓ : k)]

/-- The **integral orientation of `f ≫ j`**, for an open immersion `j`, induced by a morphism
`ψ : 𝒪_{E,X}(d)[2d] ⟶ Rf^! 𝒪_{E,Y}`: `ψ` followed by `Rf^! 𝒪_{E,Y} ≅ Rf^! Rj^! 𝒪_{E,Z}` (purity
for `j`, `boundedConstructibleUpperShriekUnitIso_padicIntegers`) and the composition isomorphism
`Rf^! Rj^! ≅ R(f ≫ j)^!` (`boundedConstructibleUpperShriekComp_padicIntegers`). -/
noncomputable def integralCompOpenImmersionOrientation
    (ψ : (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)) :
    (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 (f ≫ j)).obj (𝟙_ _) :=
  ψ ≫ (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).map
      (boundedConstructibleUpperShriekUnitIso_padicIntegers ℓ E.1 j).inv ≫
    (boundedConstructibleUpperShriekComp_padicIntegers ℓ E.1 f j).inv.app _

/-- The coefficient comparison `T(Rf^! 𝒪_{E,Y}) ≅ Rf^! ℚ̄_ℓ,Y`
(`integersToPadicAlgClUpperShriekUnitIso`) is compatible with composition with an open immersion
`j`: transported along `Rf^! 𝒪_{E,Y} ≅ Rf^! Rj^! 𝒪_{E,Z} ≅ R(f ≫ j)^! 𝒪_{E,Z}` and its
`ℚ̄_ℓ`-counterpart, it is the coefficient comparison of `f ≫ j`. -/
theorem integersToPadicAlgClUpperShriekUnitIso_comp_openImmersion :
    (boundedConstructibleExtendScalars X.left ℓ E ⋙ constructibleToPadicAlgCl X.left ℓ E).map
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).map
          (boundedConstructibleUpperShriekUnitIso_padicIntegers ℓ E.1 j).inv ≫
        (boundedConstructibleUpperShriekComp_padicIntegers ℓ E.1 f j).inv.app _) ≫
      (integersToPadicAlgClUpperShriekUnitIso ℓ E (f ≫ j)).hom =
    (integersToPadicAlgClUpperShriekUnitIso ℓ E f).hom ≫
      (boundedConstructibleUpperShriek ℓ f).map
        (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv ≫
      (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f j).inv.app _ :=
  sorry

/-- The extension of scalars to `ℚ̄_ℓ` of the integral orientation of `f ≫ j` induced by `ψ` is
the orientation of `f ≫ j` induced by the extension of scalars of `ψ`. -/
theorem extendScalarsIntegralOrientation_integralCompOpenImmersionOrientation
    (ψ : (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)) :
    extendScalarsIntegralOrientation ℓ E (f ≫ j) d
        (integralCompOpenImmersionOrientation ℓ E f j d ψ) =
      extendScalarsIntegralOrientation ℓ E f d ψ ≫
        (boundedConstructibleUpperShriek ℓ f).map
          (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv ≫
        (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f j).inv.app _ := by
  rw [extendScalarsIntegralOrientation, extendScalarsIntegralOrientation,
    integralCompOpenImmersionOrientation]
  have h := integersToPadicAlgClUpperShriekUnitIso_comp_openImmersion ℓ E f j
  simp only [Functor.map_comp, Category.assoc] at h ⊢
  simp only [h]

variable [SmoothOfRelativeDimension d f.left]
  [SmoothOfRelativeDimension d (f ≫ j).left]

/-- If `ψ` lifts the canonical finite orientations of `f`, the induced integral orientation of
`f ≫ j` lifts the canonical finite orientations of `f ≫ j`: modulo `ℓⁿ`, the orientation of the
diagonal argument for `f ≫ j` is that of `f` followed by `Rf^! Λ ≅ Rf^! Rj^! Λ ≅ R(f ≫ j)^! Λ`. -/
theorem isIntegralSmoothOrientation_integralCompOpenImmersionOrientation
    (ψ : (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _))
    (hψ : IsIntegralSmoothOrientation ℓ E f d ψ) :
    IsIntegralSmoothOrientation ℓ E (f ≫ j) d (integralCompOpenImmersionOrientation ℓ E f j d ψ) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
