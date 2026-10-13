/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.RestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicSystem

/-!
# Compatible systems of Frobenius coefficient morphisms and their realizations

A *compatible system of Frobenius coefficient morphisms* on a normalized adic system
`L_• = (L_n)` (`AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem`, blueprint
`prop-trf-adic-coefficient-morphism-systems`) is a family `ψ_n : LΦ^* L_n ⟶ L_n` of Frobenius
coefficient morphisms reducing to each other along the transitions of `L_•`. A compatible tower
of Weil pairs (strict Weil structures at every level) is the case where every `ψ_n` is invertible
(`AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.IsWeil`).

For such a system, the global Frobenius operators `F_{c,m}(ψ_n)` on `RΓ_c(X, L_n)` and the
stalk Frobenius endomorphisms `(ψ_{n,m})_x̄` at points fixed by `Φ_m` form compatible families of
endomorphisms of the normalized towers of perfect complexes of
`WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicSystem`
(`prop-trf-adic-coefficient-morphism-systems` (3)); hence they lift to the realizations over
`R`, and the traces of the lifts are the limits of the levelwise traces
(`prop-trf-adic-coefficient-morphism-systems` (4), `sk-prop-trace-adic` (ii)).

## Main definitions

- `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem`: a compatible system of Frobenius
  coefficient morphisms.
- `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.weilComplex`: the Weil complex
  `(L_n, ψ_n)` at level `n`.
- `AlgebraicGeometry.ProEtale.IsProperPullbackCompatible`: compatibility of a compact-support
  coefficient change with the proper pullbacks of two operation packages.

## Main results

- `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.coeffIterate_comp_map`: the iterates
  `ψ_{n,m}` form a compatible system.
- `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.isCompatible_stalkFrobenius`,
  `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.isCompatible_globalOperator`:
  blueprint `prop-trf-adic-coefficient-morphism-systems` (3).

## Implementation notes

The compatibility of `ψ_{n+1}` with `ψ_n` is read through the identification
`LΦ^* ∘ Res ≅ Res ∘ LΦ^*` of the derived pullback with restriction of scalars
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso`); in terms of derived base
change, `ψ_{n+1} ⊗ᴸ A_n` corresponds to `ψ_n` under `ν_n`.

The global Frobenius operator of a level is built from the operation package of that level, and
the packages at different levels are independent data of the formalism
(`AlgebraicGeometry.ProEtale.GeometricOperations`). Their compatibility with the coefficient
change is therefore a hypothesis (`AlgebraicGeometry.ProEtale.IsProperPullbackCompatible`): the
coefficient comparison of compact support intertwines the proper pullbacks of the two packages,
as the comparison of the six operations does (blueprint
`lem-fix-compact-support-coefficient-change`: it is compatible with pullback and with the
counits). The stalk Frobenius endomorphisms involve no package.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated MonoidalCategory

namespace AlgebraicGeometry.ProEtale

namespace AdicSystem

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} {X : Scheme.{u}} (S : AdicSystem I X)
  {s : Scheme.{u}} {aX : X ⟶ s}

/-- Blueprint `prop-trf-adic-coefficient-morphism-systems`: a *compatible system of Frobenius
coefficient morphisms* on a normalized adic system `L_•`, for an endomorphism `Φ` of `X` over
`s`: Frobenius coefficient morphisms `ψ_n : LΦ^* L_n ⟶ L_n` at every level such that
`ψ_{n+1}` followed by the transition `ν_n : L_{n+1} ⟶ Res L_n` is `LΦ^* ν_n` followed by the
identification `LΦ^* Res L_n ≅ Res LΦ^* L_n` and `Res ψ_n`. No invertibility is assumed. -/
structure FrobeniusSystem (Φ : X ⟶ X) (hΦ : Φ ≫ aX = aX) where
  /-- The Frobenius coefficient morphism `ψ_n : LΦ^* L_n ⟶ L_n`. -/
  coeff (n : ℕ) :
    ((upperStar (ModuleCat.{u + 1} (R ⧸ I ^ n)) Φ).leftDerivedFunctor).obj (S.obj n) ⟶ S.obj n
  /-- `ψ_{n+1}` reduces to `ψ_n`. -/
  comm (n : ℕ) : coeff (n + 1) ≫ S.map n =
    ((upperStar (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) Φ).leftDerivedFunctor).map (S.map n) ≫
      (leftDerivedUpperStarRestrictScalarsIso
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) n.le_succ)) Φ).hom.app (S.obj n) ≫
      (levelTransitionRestrictScalars X I n.le_succ).map (coeff n)

namespace FrobeniusSystem

variable {S} {Φ : X ⟶ X} {hΦ : Φ ≫ aX = aX} (F : S.FrobeniusSystem Φ hΦ)

/-- A compatible system of Frobenius coefficient morphisms is a *compatible tower of Weil
pairs* if every `ψ_n` is invertible: a strict Weil structure at every level, compatible with the
transitions (blueprint `def-trf-adic-system`, `sk-prop-trace-adic` (ii)). -/
def IsWeil : Prop := ∀ n, IsIso (F.coeff n)

/-- The Weil complex `(L_n, ψ_n)` at level `n`. -/
@[simps]
def weilComplex (n : ℕ) : WeilComplex (A := ModuleCat.{u + 1} (R ⧸ I ^ n)) aX where
  frobenius := Φ
  frobenius_comp := hΦ
  obj := S.obj n
  coeff := F.coeff n

end FrobeniusSystem

end AdicSystem

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

namespace AdicSystem

namespace FrobeniusSystem

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} {X : Scheme.{u}} {S : AdicSystem I X}
  {s : Scheme.{u}} {aX : X ⟶ s} {Φ : X ⟶ X} {hΦ : Φ ≫ aX = aX} (F : S.FrobeniusSystem Φ hΦ)

end FrobeniusSystem

end AdicSystem

section Generic

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X s : Scheme.{u}}
  {aX : X ⟶ s} (Φ : X ⟶ X) (hΦ : Φ ≫ aX = aX)
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
  {K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ'))}
  (ψ : ((upperStar (ModuleCat.{u + 1} Λ) Φ).leftDerivedFunctor).obj K ⟶ K)
  (ψ' : ((upperStar (ModuleCat.{u + 1} Λ') Φ).leftDerivedFunctor).obj K' ⟶ K')
  (t : K ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ).obj K')

/-- The iterate `Φ^m` of an endomorphism `Φ` of `X`, as a morphism. -/
abbrev endPow (Φ : X ⟶ X) (m : ℕ) : X ⟶ X := (show End X from Φ) ^ m

lemma endPow_succ (Φ : X ⟶ X) (m : ℕ) : endPow Φ (m + 1) = Φ ≫ endPow Φ m :=
  (pow_succ (M := End X) Φ m).trans (End.mul_def _ _)

variable {Λ₀ : Type (u + 1)} [CommRing Λ₀] in
/-- The iterates `ψ_m : L(Φ^m)^* K ⟶ K` of a Frobenius coefficient morphism `ψ`, by the same
recursion as `AlgebraicGeometry.ProEtale.WeilComplex.coeffIterate`. -/
noncomputable def iterCoeff (Φ : X ⟶ X)
    {K₀ : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ₀))}
    (ψ₀ : ((upperStar (ModuleCat.{u + 1} Λ₀) Φ).leftDerivedFunctor).obj K₀ ⟶ K₀) :
    (m : ℕ) → ((upperStar (ModuleCat.{u + 1} Λ₀) (endPow Φ m)).leftDerivedFunctor).obj K₀ ⟶ K₀
  | 0 => (leftDerivedUpperStarId _ X).hom.app K₀
  | m + 1 =>
    (leftDerivedUpperStarCongr _ (endPow_succ Φ m)).hom.app K₀ ≫
      (leftDerivedUpperStarComp _ Φ (endPow Φ m)).hom.app K₀ ≫
      ((upperStar _ Φ).leftDerivedFunctor).map (iterCoeff Φ ψ₀ m) ≫ ψ₀

variable {Λ₀ : Type (u + 1)} [CommRing Λ₀] in
lemma coeffIterate_mk_eq_iterCoeff
    {K₀ : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ₀))}
    (ψ₀ : ((upperStar (ModuleCat.{u + 1} Λ₀) Φ).leftDerivedFunctor).obj K₀ ⟶ K₀) (m : ℕ) :
    (WeilComplex.mk (aX := aX) Φ hΦ K₀ ψ₀).coeffIterate m = iterCoeff Φ ψ₀ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [WeilComplex.coeffIterate_succ, iterCoeff, ← ih]
    rfl

include ρ in
/-- If two Frobenius coefficient morphisms `ψ` over `Λ` and `ψ'` over `Λ'` are compatible along
`t : K ⟶ Res K'`, so are their iterates. -/
theorem iterCoeff_comp_eq
    (h : ψ ≫ t = ((upperStar (ModuleCat.{u + 1} Λ) Φ).leftDerivedFunctor).map t ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ Φ).hom.app K' ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ).map ψ') (m : ℕ) :
    iterCoeff Φ ψ m ≫ t =
      ((upperStar (ModuleCat.{u + 1} Λ) (endPow Φ m)).leftDerivedFunctor).map t ≫
        (leftDerivedUpperStarRestrictScalarsIso ρ (endPow Φ m)).hom.app K' ≫
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ).map (iterCoeff Φ ψ' m) := by
  induction m with
  | zero =>
    simp only [iterCoeff]
    erw [leftDerivedUpperStarRestrictScalarsIso_id_hom_app]
    exact ((leftDerivedUpperStarId _ X).hom.naturality t).symm
  | succ m ih =>
    simp only [iterCoeff, Category.assoc, Functor.map_comp]
    rw [h, ← Functor.map_comp_assoc, ih]
    simp only [Functor.map_comp, Category.assoc]
    have h1 := (leftDerivedUpperStarRestrictScalarsIso ρ Φ).hom.naturality (iterCoeff Φ ψ' m)
    have h2 := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) Φ (endPow Φ m)).hom.naturality t
    have h3 := leftDerivedUpperStarRestrictScalarsIso_comp_hom_app ρ Φ (endPow Φ m) K'
    have h4 := (leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) (endPow_succ Φ m)).hom.naturality t
    have h5 := leftDerivedUpperStarRestrictScalarsIso_congr_hom_app ρ (endPow_succ Φ m) K'
    simp only [Functor.comp_map] at h1 h2 h4
    rw [reassoc_of% h1, ← reassoc_of% h2, ← reassoc_of% h3, ← reassoc_of% h4, ← reassoc_of% h5]

include ρ in
/-- If two Frobenius coefficient morphisms are compatible along `t : K ⟶ Res K'`, then so are the
stalk endomorphisms `(ψ_m)_x̄` at a point `x̄` fixed by `Φ^m`: `L x̄^* t`, read through
`Lx̄^* Res ≅ Res Lx̄^*`, intertwines them. -/
theorem iterStalk_comp_eq
    (h : ψ ≫ t = ((upperStar (ModuleCat.{u + 1} Λ) Φ).leftDerivedFunctor).map t ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ Φ).hom.app K' ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ).map ψ') (m : ℕ)
    (x y : s ⟶ X) (hx : x ≫ endPow Φ m = y) :
    ((leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) hx).inv.app K ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) x (endPow Φ m)).hom.app K ≫
        ((upperStar (ModuleCat.{u + 1} Λ) x).leftDerivedFunctor).map (iterCoeff Φ ψ m)) ≫
      ((upperStar (ModuleCat.{u + 1} Λ) x).leftDerivedFunctor).map t ≫
        (leftDerivedUpperStarRestrictScalarsIso ρ x).hom.app K' =
    ((upperStar (ModuleCat.{u + 1} Λ) y).leftDerivedFunctor).map t ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ y).hom.app K' ≫
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology s) ρ).map
          ((leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ') hx).inv.app K' ≫
            (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ') x (endPow Φ m)).hom.app K' ≫
            ((upperStar (ModuleCat.{u + 1} Λ') x).leftDerivedFunctor).map (iterCoeff Φ ψ' m)) := by
  have hi := iterCoeff_comp_eq ρ Φ ψ ψ' t h m
  have h1 := (leftDerivedUpperStarRestrictScalarsIso ρ x).hom.naturality (iterCoeff Φ ψ' m)
  have h2 := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) x (endPow Φ m)).hom.naturality t
  have h3 := leftDerivedUpperStarRestrictScalarsIso_comp_hom_app ρ x (endPow Φ m) K'
  have h4 := (leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) hx).inv.naturality t
  have h5' : (leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) hx).inv.app
        ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ).obj K') ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ (x ≫ endPow Φ m)).hom.app K' =
      (leftDerivedUpperStarRestrictScalarsIso ρ y).hom.app K' ≫
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology s) ρ).map
          ((leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ') hx).inv.app K') := by
    subst hx
    simp
  simp only [Functor.comp_map] at h1 h2 h4
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, hi]
  simp only [Functor.map_comp, Category.assoc]
  rw [h1, ← reassoc_of% h2, ← reassoc_of% h3, ← reassoc_of% h4, reassoc_of% h5']

variable (αs : Sheaf.derivedRestrictScalars (Scheme.ProEt.topology s) ρ ⋙
    rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s ≅
  rightDerivedGlobalSections (ModuleCat.{u + 1} Λ') s ⋙ ModuleCat.derivedRestrictScalars ρ)

/-- If two Frobenius coefficient morphisms are compatible along `t : K ⟶ Res K'`, then the
geometric stalks of `t` at a point `x̄` fixed by `Φ^m`, read through a comparison
`Res ∘ (-)_x̄ ≅ (-)_x̄ ∘ Res` (`AlgebraicGeometry.ProEtale.stalkCoefficientIso`), intertwine the
stalk endomorphisms `(ψ_m)_x̄` and `(ψ'_m)_x̄` (blueprint
`prop-trf-adic-coefficient-morphism-systems` (3)). -/
theorem geometricStalk_map_comp_stalkCoefficientIso
    (h : ψ ≫ t = ((upperStar (ModuleCat.{u + 1} Λ) Φ).leftDerivedFunctor).map t ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ Φ).hom.app K' ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ).map ψ') (m : ℕ)
    (x : s ⟶ X) (hx : x ≫ endPow Φ m = x) :
    (geometricStalk Λ x).map t ≫ (stalkCoefficientIso ρ x αs).hom.app K' ≫
        (ModuleCat.derivedRestrictScalars ρ).map ((rightDerivedGlobalSections _ s).map
          ((leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ') hx).inv.app K' ≫
            (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ') x (endPow Φ m)).hom.app K' ≫
            ((upperStar (ModuleCat.{u + 1} Λ') x).leftDerivedFunctor).map (iterCoeff Φ ψ' m))) =
      (rightDerivedGlobalSections _ s).map
          ((leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) hx).inv.app K ≫
            (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) x (endPow Φ m)).hom.app K ≫
            ((upperStar (ModuleCat.{u + 1} Λ) x).leftDerivedFunctor).map (iterCoeff Φ ψ m)) ≫
        (geometricStalk Λ x).map t ≫ (stalkCoefficientIso ρ x αs).hom.app K' := by
  have hα := αs.hom.naturality ((leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ') hx).inv.app K' ≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ') x (endPow Φ m)).hom.app K' ≫
    ((upperStar (ModuleCat.{u + 1} Λ') x).leftDerivedFunctor).map (iterCoeff Φ ψ' m))
  have hs := congrArg (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s).map
    (iterStalk_comp_eq ρ Φ ψ ψ' t h m x x hx)
  simp only [Functor.comp_map] at hα
  simp only [Functor.map_comp, Category.assoc] at hs
  simp only [stalkCoefficientIso_hom_app, Functor.comp_map, Category.assoc]
  rw [← hα]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hs]

end Generic

namespace AdicSystem

namespace FrobeniusSystem

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} {X : Scheme.{u}} {S : AdicSystem I X}
  {s : Scheme.{u}} {aX : X ⟶ s} {Φ : X ⟶ X} {hΦ : Φ ≫ aX = aX} (F : S.FrobeniusSystem Φ hΦ)

/-- The iterates of the Frobenius coefficient morphism of the Weil complex at level `n` are the
iterates `ψ_{n,m}` of `ψ_n`. -/
lemma weilComplex_coeffIterate (n m : ℕ) :
    (F.weilComplex n).coeffIterate m = iterCoeff Φ (F.coeff n) m :=
  coeffIterate_mk_eq_iterCoeff Φ hΦ (F.coeff n) m

/-- Blueprint `prop-trf-adic-coefficient-morphism-systems` (3), iterates: the iterates
`ψ_{n,m}` form a compatible system: `ψ_{n+1,m}` followed by the transition `ν_n` is
`L(Φ^m)^* ν_n` followed by `L(Φ^m)^* Res ≅ Res L(Φ^m)^*` and `Res ψ_{n,m}`. -/
theorem coeffIterate_comp_map (n m : ℕ) :
    (F.weilComplex (n + 1)).coeffIterate m ≫ S.map n =
      ((upperStar (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) (endPow Φ m)).leftDerivedFunctor).map
          (S.map n) ≫
        (leftDerivedUpperStarRestrictScalarsIso
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) n.le_succ))
          (endPow Φ m)).hom.app (S.obj n) ≫
        (levelTransitionRestrictScalars X I n.le_succ).map ((F.weilComplex n).coeffIterate m) := by
  rw [weilComplex_coeffIterate, weilComplex_coeffIterate]
  exact iterCoeff_comp_eq _ Φ _ _ _ (F.comm n) m

end FrobeniusSystem

end AdicSystem

end AlgebraicGeometry.ProEtale
