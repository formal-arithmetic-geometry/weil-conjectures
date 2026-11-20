/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralUpperShriekCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClCompatibility
public import WeilConjectures.SmoothPurity.IntegralTateTwistExtendScalars
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth purity with coefficients in a finite extension `E` of `ℚ_ℓ`

Let `ℓ` be a prime, `k` a field of characteristic `p ≠ ℓ`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ`,
and `f : X ⟶ Y` a morphism of separated `k`-schemes of finite type which is smooth of pure
relative dimension `d`. This file proves blueprint `proposition-sp-rational`: the lower shriek
`Rf_{!,E} : Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧` is left adjoint to the twisted pullback
`K ↦ f_E^* K (d)[2d]`
(`ProEtale.CondensedRing.ContinuousMapRingObj.nonempty_adjunction_lowerShriek_twistedUpperStar`).

## The twists

The integral Tate twist `𝒪_{E,X}(d)` is `ProEtale.integralTateTwistBoundedConstructible`, and
`E_X(d)[n]` is its extension of scalars along `𝒪_E ⟶ E`, that is `𝒪_{E,X}(d)[n]` with `ℓ`
inverted (blueprint `definition-tate-twists--6`):
`ProEtale.CondensedRing.ContinuousMapRingObj.boundedConstructibleTateTwist`. For a complex `K`,
`K(d)[2d]` is `K ⊗ᴸ Λ_X(d)[2d]` (blueprint `definition-tate-twists--13`); the twisted pullbacks
`K ↦ f^* K ⊗ᴸ Λ_X(d)[2d]` are `PadicIntegersRingObj.twistedUpperStar` and
`ContinuousMapRingObj.twistedUpperStar`.

## The proof

As in the blueprint, the adjunction over `E` is obtained by inverting `ℓ` in the integral one.
The extension of scalars `T : Dᵇc(-)⟦𝒪̲_E⟧ ⥤ Dᵇc(-)⟦E̲⟧` is a localization functor
(`ProEtale.isLocalization_boundedConstructibleExtendScalars`, blueprint
`proposition-inverting-ell--2`). It commutes with `Rf^!`
(`ProEtale.CondensedRing.boundedConstructibleUpperShriekExtendScalarsIso`), with `Lf^*`
(`ProEtale.CondensedRing.boundedConstructibleUpperStarExtendScalarsIso`) and with the tensor
product (it is strong monoidal), hence with the twisted pullbacks
(`ContinuousMapRingObj.twistedUpperStarExtendScalarsIso`). The integral purity isomorphism
`f^*_{𝒪_E}(-)(d)[2d] ≅ f^!_{𝒪_E}` (blueprint
`theorem-smooth-purity-all-admissible-coefficients--2`,
`PadicIntegersRingObj.nonempty_twistedUpperStarIsoUpperShriek`) therefore gives an isomorphism
`T ⋙ f^*_E(-)(d)[2d] ≅ T ⋙ f^!_E`, which descends along the localization `T` to an isomorphism
`f^*_E(-)(d)[2d] ≅ f^!_E`. Composing the adjunction `Rf_{!,E} ⊣ Rf^!_E` with it gives the
adjunction.

The integral purity isomorphism is the only `sorry` used: it is constructed in the blueprint from
the adjunction on constructible towers (blueprint `proposition-sp-tower-geometric`) and the
integral right adjoint built from towers (blueprint `proposition-sp-integral-adjunction`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)] (E : PadicAlgCl.FiniteIntermediateField ℓ)

namespace PadicIntegersRingObj

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

variable (X) in
/-- The shifted integral Tate twist `𝒪_{E,X}(d)[n]`, as a bounded constructible complex. -/
noncomputable def boundedConstructibleTateTwist (d : ℕ) (n : ℤ) :
    Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧ :=
  (shiftFunctor _ n).obj (integralTateTwistBoundedConstructible ℓ E.1 X.hom d)

/-- The integral twisted pullback `K ↦ f^* K (d)[2d] = f^* K ⊗ᴸ 𝒪_{E,X}(d)[2d]` on bounded
constructible complexes (blueprint `definition-tate-twists--13`). -/
noncomputable def twistedUpperStar (f : X ⟶ Y) (d : ℕ) :
    Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧ ⥤
      Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧ :=
  boundedConstructibleUpperStar _ ℓ f ⋙ tensorRight (boundedConstructibleTateTwist ℓ E X d (2 * d))

/-- Blueprint `theorem-smooth-purity-all-admissible-coefficients--2`: **smooth purity with
coefficients in `𝒪_E`**. For `f` smooth of pure relative dimension `d` there is an isomorphism,
natural in `K ∈ Dᵇc(Y)⟦𝒪̲_E⟧`, `γ_{f,𝒪_E}(K) : f^*_{𝒪_E} K (d)[2d] ≅ f^!_{𝒪_E} K`.
In the blueprint it is the derived limit of the isomorphism on constructible towers (9.19),
through the integral right adjoint built from towers (`proposition-sp-integral-adjunction`). -/
theorem nonempty_twistedUpperStarIsoUpperShriek (f : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d f.left] :
    Nonempty (twistedUpperStar ℓ E f d ≅ boundedConstructibleUpperShriek ℓ E.1 f) := by
  sorry

end PadicIntegersRingObj

namespace ContinuousMapRingObj

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

variable (X) in
/-- The shifted Tate twist `E_X(d)[n] = 𝒪_{E,X}(d)[n] [1/ℓ]` (blueprint
`definition-tate-twists--6`), as a bounded constructible complex: the extension of scalars along
`𝒪_E ⟶ E` of the integral Tate twist. -/
noncomputable def boundedConstructibleTateTwist (d : ℕ) (n : ℤ) :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj E.1⟧ :=
  (boundedConstructibleExtendScalars X.left ℓ E).obj
    (PadicIntegersRingObj.boundedConstructibleTateTwist ℓ E X d n)

/-- The twisted pullback `K ↦ f_E^* K (d)[2d] = f_E^* K ⊗ᴸ E_X(d)[2d]` on bounded constructible
complexes with coefficients in `E` (blueprint `definition-tate-twists--13`). -/
noncomputable def twistedUpperStar (f : X ⟶ Y) (d : ℕ) :
    Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E.1⟧ ⥤
      Dᵇc(X.left)⟦Profinite.continuousMapRingObj E.1⟧ :=
  boundedConstructibleUpperStar _ ℓ f ⋙ tensorRight (boundedConstructibleTateTwist ℓ E X d (2 * d))

/-- The extension of scalars along `𝒪_E ⟶ E` commutes with the twisted pullbacks:
`f^*_{𝒪_E}(-)(d)[2d] ⋙ T_X ≅ T_Y ⋙ f^*_E(-)(d)[2d]`, from the commutation with `Lf^*`
(`boundedConstructibleUpperStarExtendScalarsIso`) and the monoidal structure of `T_X`. -/
noncomputable def twistedUpperStarExtendScalarsIso (f : X ⟶ Y) (d : ℕ) :
    PadicIntegersRingObj.twistedUpperStar ℓ E f d ⋙ boundedConstructibleExtendScalars X.left ℓ E ≅
      boundedConstructibleExtendScalars Y.left ℓ E ⋙ twistedUpperStar ℓ E f d :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.Monoidal.commTensorRight (boundedConstructibleExtendScalars X.left ℓ E) _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (boundedConstructibleUpperStarExtendScalarsIso ℓ E f) _ ≪≫
    Functor.associator _ _ _

/-- Blueprint `proposition-sp-rational`, as an isomorphism of right adjoints: for `f` smooth of
pure relative dimension `d`, `f_E^* K (d)[2d] ≅ f^!_E K`, naturally in `K ∈ Dᵇc(Y)⟦E̲⟧`. It is
the integral purity isomorphism with `ℓ` inverted: both functors commute with the extension of
scalars `T` along `𝒪_E ⟶ E`, and isomorphisms descend along the localization `T`. -/
theorem nonempty_twistedUpperStarIsoUpperShriek (f : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d f.left] :
    Nonempty (twistedUpperStar ℓ E f d ≅ boundedConstructibleUpperShriek ℓ E f) := by
  have := noetherianSpace_left_of_over Y
  obtain ⟨γ⟩ := PadicIntegersRingObj.nonempty_twistedUpperStarIsoUpperShriek ℓ E f d
  exact ⟨(Localization.whiskeringLeftFunctor' (boundedConstructibleExtendScalars Y.left ℓ E)
    (Rationalization.W (Submonoid.powers (ℓ : ℤ))
      (Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)) _).preimageIso
    ((twistedUpperStarExtendScalarsIso ℓ E f d).symm ≪≫ Functor.isoWhiskerRight γ _ ≪≫
      boundedConstructibleUpperShriekExtendScalarsIso ℓ E f)⟩

/-- Blueprint `proposition-sp-rational` (and its clause `proposition-sp-rational--1`): **smooth
purity with coefficients in `E`**. For `E/ℚ_ℓ` finite and `f` smooth of pure relative dimension
`d`, `Rf_{!,E} ⊣ (K ↦ f_E^* K (d)[2d])` as functors between `Dᵇc(X)⟦E̲⟧` and `Dᵇc(Y)⟦E̲⟧`. -/
theorem nonempty_adjunction_lowerShriek_twistedUpperStar (f : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d f.left] :
    Nonempty (boundedConstructibleLowerShriek ℓ E f ⊣ twistedUpperStar ℓ E f d) :=
  (nonempty_twistedUpperStarIsoUpperShriek ℓ E f d).map fun γ ↦
    (boundedConstructibleUpperShriekAdjunction ℓ E f).ofNatIsoRight γ.symm

end ContinuousMapRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
