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
