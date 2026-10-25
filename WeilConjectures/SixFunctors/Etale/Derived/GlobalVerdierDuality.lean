/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom

/-!
# Global Verdier duality

Let `a_X : X ⟶ S` admit a compactification and satisfy the projection formula (for instance at
a finite coefficient ring). Global Verdier duality is the canonical isomorphism

`RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`,

natural in `K`: the inverse of the tensor–Hom exchange
`Ra_{X*} RHom(K, Ra_X^! N) ≅ RHom(Ra_{X!} K, N)` at `N = Λ_S`. This is blueprint
`thm-pod-global-verdier-duality` (in the étale setting, written in `D(S_ét)` with `Ra_{X!}` and
`Ra_{X*}`; over `S = Spec k` applying `RΓ(S, -)` gives the displayed form).

## Main definitions

- `AlgebraicGeometry.Etale.globalVerdierDualityNatIso`: `(Ra_{X!} -)^∨ ≅ Ra_{X*} 𝔻_X(-)`.
- `AlgebraicGeometry.Etale.globalVerdierDualityIso`: its component at `K`.
- `AlgebraicGeometry.Etale.globalVerdierDualityUnitIso`: the case `K = Λ_X`,
  `RΓ_c(X, Λ_X)^∨ ≅ RΓ(X, ω_X)`.

## Main statements

- `AlgebraicGeometry.Etale.globalVerdierDualityIso_hom_naturality`: naturality in `K`.
- `AlgebraicGeometry.Etale.globalVerdierDualityIso_inv_comp_mateEquiv`: compatibility with
  changes of coefficients (finite reduction, scalar extension) compatible with the projection
  map.

The construction uses only the tensor–Hom adjunction, the projection formula and the
adjunctions `La^* ⊣ Ra_*`, `Ra_! ⊣ Ra^!`; no properness and no global Poincaré duality.
-/

@[expose] public section

universe u' u'' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X S : Scheme.{u}} (aX : X ⟶ S) [HasCompactification aX]
  [IsIso (projectionMap A aX)]

/-- Blueprint `thm-pod-global-verdier-duality`: Global Verdier duality at the point.

For `a_X : X ⟶ S` admitting a compactification and satisfying the projection formula (which
holds at every finite coefficient ring, `AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`),
the canonical isomorphism `RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`, written in `D(S_ét)` as
`(Ra_{X!} K)^∨ ≅ Ra_{X*}(𝔻_X K)`. It is the inverse of the tensor–Hom exchange
`Ra_{X*} RHom(K, Ra_X^! N) ≅ RHom(Ra_{X!} K, N)`
(`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso`, built from the adjunctions and
the projection formula only) at `N = Λ_S`. -/
noncomputable def globalVerdierDualityIso
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) S).obj (op ((R(aX)_![ModuleCat.{u + 1}
        Λ]).obj K)) ≅
      (R((aX)_*[ModuleCat.{u + 1} Λ])).obj ((verdierDual Λ aX).obj (op K)) :=
  (((derivedHomRightDerivedLowerShriekIso Λ aX).app (op K)).app (𝟙_ _)).symm

omit [HasSmallSiteSheafify (ModuleCat.{u + 1} Λ)] in
lemma globalVerdierDualityIso_eq
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    globalVerdierDualityIso Λ aX K =
      (((derivedHomRightDerivedLowerShriekIso Λ aX).app (op K)).app (𝟙_ _)).symm :=
  rfl

-- A proof by `rfl` (or by `simp`/`rw` closing with `rfl`) makes the kernel reduce the
-- projections of `derivedHomRightDerivedLowerShriekIso`, which times out.
omit [HasSmallSiteSheafify (ModuleCat.{u + 1} Λ)] in
lemma globalVerdierDualityIso_inv
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (globalVerdierDualityIso Λ aX K).inv =
      ((derivedHomRightDerivedLowerShriekIso Λ aX).app (op K)).hom.app (𝟙_ _) :=
  (congrArg Iso.inv (globalVerdierDualityIso_eq Λ aX K)).trans
    ((Iso.symm_inv _).trans (Iso.app_hom _ _))

omit [HasSmallSiteSheafify (ModuleCat.{u + 1} Λ)] in
/-- Blueprint `thm-pod-global-verdier-duality`: Global Verdier duality at the point,
naturality in `K`. -/
lemma globalVerdierDualityIso_hom_naturality
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (g : K ⟶ K')
        :
    (DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) S).map ((R(aX)_![ModuleCat.{u + 1}
        Λ]).map g).op ≫
        (globalVerdierDualityIso Λ aX K).hom =
      (globalVerdierDualityIso Λ aX K').hom ≫ (R((aX)_*[ModuleCat.{u + 1} Λ])).map ((verdierDual Λ
          aX).map g.op) :=
  NatTrans.congr_app ((derivedHomRightDerivedLowerShriekIso Λ aX).inv.naturality g.op) (𝟙_ _)

/-- Blueprint `thm-pod-global-verdier-duality`: Global Verdier duality at the point, natural
form: `AlgebraicGeometry.Etale.globalVerdierDualityIso` as a natural isomorphism
`(Ra_{X!} -)^∨ ≅ Ra_{X*} 𝔻_X(-)` of functors `D(X_ét)ᵒᵖ ⥤ D(S_ét)`. -/
noncomputable def globalVerdierDualityNatIso :
    (R(aX)_![ModuleCat.{u + 1} Λ]).op ⋙ DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) S ≅
      verdierDual Λ aX ⋙ R((aX)_*[ModuleCat.{u + 1} Λ]) :=
  NatIso.ofComponents (fun K ↦ globalVerdierDualityIso Λ aX K.unop)
    (fun g ↦ globalVerdierDualityIso_hom_naturality Λ aX g.unop)

/-- Blueprint `thm-pod-global-verdier-duality`: Global Verdier duality at the point, the case
`K = Λ_X`.

At `K = Λ_X` global Verdier duality identifies `RΓ_c(X, Λ_X)^∨` with `RΓ(X, ω_X)`: it is
`AlgebraicGeometry.Etale.globalVerdierDualityIso` followed by `𝔻_X Λ_X = RHom(Λ_X, ω_X) ≅ ω_X`,
the evaluation at the unit object. -/
noncomputable def globalVerdierDualityUnitIso :
    (DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) S).obj (op ((R(aX)_![ModuleCat.{u + 1}
        Λ]).obj (𝟙_ _))) ≅
      (R((aX)_*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ aX) :=
  globalVerdierDualityIso Λ aX (𝟙_ _) ≪≫
    (R((aX)_*[ModuleCat.{u + 1} Λ])).mapIso (MonoidalClosed.unitNatIso.app (dualizingComplex Λ
        aX)).symm

section CoefficientChange

open TwoSquare

variable (A' : Type u'') [Category.{u + 1} A'] [Abelian A'] [IsGrothendieckAbelian.{u + 1} A']
  [MonoidalCategory A'] [MonoidalPreadditive A'] [SymmetricCategory A'] [MonoidalClosed A']
  [Abelian.HasFunctorialFlatResolution A']
  {FA' : A' → A' → Type (u + 1)} {CA' : A' → Type (u + 1)}
  [∀ X Y, FunLike (FA' X Y) (CA' X) (CA' Y)] [ConcreteCategory.{u + 1} A' FA']
  [Etale.UpperStarPreservesFlat A']
  [(CategoryTheory.forget A').ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A')]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A')]
  [(R(aX)_![A']).IsLeftAdjoint] [IsIso (projectionMap A' aX)]

omit [HasSmallSiteSheafify A] in
/-- Blueprint `thm-pod-global-verdier-duality`: Global Verdier duality at the point,
compatibility with finite coefficient reduction and scalar extension.

(ModuleCat.{u + 1} Λ) change of coefficients `(ModuleCat.{u + 1} Λ) → A'` (the finite reduction
`A_{E,n} → A_{E,m}`, or a scalar
extension) is given by functors `T_X`, `T_S` on the derived categories and comparison maps
`σ`, `μ`, `ρ`, `ν` for the left adjoints `La_X^*`, `K ⊗ᴸ -`, `Ra_{X!}` and `Ra_{X!} K ⊗ᴸ -`,
as in `AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso_hom_app_comp_mateEquiv`;
the comparison maps of the right adjoints `Ra_{X*}`, `RHom(K, -)`, `Ra_X^!` and of the dual are
their mates. If the change of coefficients is compatible with the projection map, then the
inverse of the global Verdier-duality isomorphism is compatible with it: the square
```
T_S Ra_{X*} 𝔻_X K ------ T_S(iso⁻¹) -----> T_S (Ra_{X!} K)^∨
       |                                         |
       | comparison                              | comparison
       v                                         v
Ra_{X*} RHom(K', Ra_X^! T_S Λ) --- iso⁻¹ ---> RHom(Ra_{X!} K', T_S Λ)
```
commutes. Composing with a comparison `T_S Λ_S ⟶ Λ'_S` of the units (and the compatibility of
the dualizing complexes `T_X ω_X ≅ ω'_X` with the smooth orientation, blueprint
`thm-pur-finite-reduction-of-purity`) gives the comparison with the duality over `A'`. -/
theorem globalVerdierDualityIso_inv_comp_mateEquiv
    (TX : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A'))
    (TS : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf S.smallEtaleTopology A'))
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A'))
    (σ : TwoSquare TS L((aX)^*[ModuleCat.{u + 1} Λ]) L((aX)^*[A']) TX)
    (μ : TwoSquare TX ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K) ((-⊗ᴸ-(X)[A']).obj K') TX)
    (ρ : TwoSquare TX R(aX)_![ModuleCat.{u + 1} Λ] R(aX)_![A'] TS)
    (ν : TwoSquare TS ((-⊗ᴸ-(S)[ModuleCat.{u + 1} Λ]).obj ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K))
      ((-⊗ᴸ-(S)[A']).obj ((R(aX)_![A']).obj K')) TS)
    (h : ν.whiskerLeft ((projectionMap (ModuleCat.{u + 1} Λ) aX).app K) =
      (σ ≫ᵥ μ ≫ᵥ ρ).whiskerRight ((projectionMap A' aX).app K')) :
    TS.map (globalVerdierDualityIso Λ aX K).inv ≫
        (mateEquiv (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) ((R(aX)_![ModuleCat.{u + 1}
            Λ]).obj K))
          (derivedTensorHomAdjunction A' ((R(aX)_![A']).obj K')) ν).app (𝟙_ _) =
      (mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) aX)
          (derivedUpperStarLowerStarAdjunction A' aX) σ).app _ ≫
        R((aX)_*[A']).map ((mateEquiv (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) K)
          (derivedTensorHomAdjunction A' K') μ).app _) ≫
        R((aX)_*[A']).map (((RHom(X)[A']).obj (op K')).map
          ((mateEquiv (rightDerivedUpperShriekAdjunction Λ aX)
            (rightDerivedUpperShriekAdjunction Λ' aX) ρ).app (𝟙_ _))) ≫
        ((derivedHomRightDerivedLowerShriekIso Λ' aX).app (op K')).hom.app (TS.obj (𝟙_ _)) := by
  rw [globalVerdierDualityIso_inv]
  exact derivedHomRightDerivedLowerShriekIso_hom_app_comp_mateEquiv Λ aX A' TX TS K K' σ μ ρ ν h
    (𝟙_ _)

end CoefficientChange

end General

end Etale

end AlgebraicGeometry
