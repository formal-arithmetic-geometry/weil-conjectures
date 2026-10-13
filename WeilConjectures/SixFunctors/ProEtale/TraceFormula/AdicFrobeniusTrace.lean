/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobenius
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.GlobalOperator

/-!
# Global Frobenius operators of compatible systems and their adic traces

For a compatible system of Frobenius coefficient morphisms `ψ_n` on a normalized adic system
`L_•` (`AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem`), the global Frobenius operators
`F_{c,m}(ψ_n) = T_{c_m}(ψ_{n,m})` on `P_n = RΓ_c(X, L_n)` form a compatible family on the
normalized tower of compact cohomology (blueprint `prop-trf-adic-coefficient-morphism-systems`
(3)), provided the operation packages of the levels are compatible with the coefficient
comparison of compact support. Together with the compatibility of the stalk Frobenius
endomorphisms (`AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.isCompatible_stalkFrobenius`)
this gives the lifts of both families to the realizations over `R` and the well-definedness of
their traces (`prop-trf-adic-coefficient-morphism-systems` (4), `sk-prop-trace-adic` (ii)).

## Main definitions

- `AlgebraicGeometry.ProEtale.IsProperPullbackCompatible`: compatibility of a compact-support
  coefficient comparison with the proper pullbacks of two operation packages.

## Main results

- `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.isCompatible_globalOperator`: blueprint
  `prop-trf-adic-coefficient-morphism-systems` (3), global operators.
- `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.exists_isLift_globalOperator`,
  `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.exists_isLift_stalkFrobenius`: the
  families lift to endomorphisms of the realizations (`sk-prop-trace-adic` (ii)).
- `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.trace_eq_of_isLift_globalOperator`,
  `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.trace_eq_of_isLift_stalkFrobenius`
  and the `exists_trace_eq_of_isLift_*` versions: the traces of the lifts are well defined and
  reduce to the levelwise traces (`prop-trf-adic-coefficient-morphism-systems` (4)).

## Implementation notes

The global Frobenius operator of a level is built from the operation package of that level, and
the packages at different levels are independent data of the formalism
(`AlgebraicGeometry.ProEtale.GeometricOperations`). Their compatibility with the coefficient
change is therefore a hypothesis (`AlgebraicGeometry.ProEtale.IsProperPullbackCompatible`): the
coefficient comparison of compact support intertwines the proper pullbacks of the two packages,
as the comparison of the six operations does (blueprint
`lem-fix-compact-support-coefficient-change`: it is compatible with pullback). Since the
restriction of scalars of an object of `Dᵇctf(X, A_n)` is in general not of finite Tor amplitude
over `A_{n+1}`, the compatibility is phrased along maps `η : K ⟶ Res K'`.

The condition `V ≫ pr_n = pr_n ≫ Res (f n)` of a lift
(`ModuleCat.NormalizedPerfectTower.IsLift`) is the statement that the realization isomorphisms
`P_𝒪 ⊗ᴸ A_n ≅ P_n` intertwine `V ⊗ᴸ A_n` with `f n`, which is the equivariance of
`sk-prop-trace-adic` (ii).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated MonoidalCategory

namespace AlgebraicGeometry.ProEtale

section Generic

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] [Finite Λ] [Finite Λ'] (ρ : Λ →+* Λ')
  [Abelian.HasFunctorialFlatResolution (ModuleCat.{u + 1} Λ)]
  [Abelian.HasFunctorialFlatResolution (ModuleCat.{u + 1} Λ')]
  [DerivedBraiding (ModuleCat.{u + 1} Λ)] [DerivedBraiding (ModuleCat.{u + 1} Λ')]
  {s X X' : Scheme.{u}} {aX : X ⟶ s} {aX' : X' ⟶ s} [IsGeometric aX] [IsGeometric aX']
  [HasCompactification aX] [HasCompactification aX']
  (G : GeometricOperations (ModuleCat.{u + 1} Λ) s)
  (G' : GeometricOperations (ModuleCat.{u + 1} Λ') s)

/-- Blueprint `lem-fix-compact-support-coefficient-change` (compatibility with pullback): the
coefficient comparisons `δ : Res ∘ Ra_{X!} ≅ Ra_{X!} ∘ Res` and `δ'` (for `X'`) are
*compatible with the proper pullbacks* along a proper `h : X' ⟶ X` of the operation packages
`G` over `Λ` and `G'` over `Λ'`: for `K ∈ Dᵇctf(X, Λ)`, `K' ∈ Dᵇctf(X, Λ')` and
`η : K ⟶ Res K'`, the square

```
  Ra_{X!} K ───────h^*────────▶ Ra_{X'!} Lh^* K
     │                                 │ Ra_{X'!}(Lh^* η), Lh^* Res ≅ Res Lh^*, δ'
     │ Ra_{X!} η, δ                    ▼
     ▼                          Res Ra_{X'!} Lh^* K'
  Res Ra_{X!} K' ──Res h^*──▶          ‖
```

commutes, where `h^*` is the proper pullback
(`AlgebraicGeometry.ProEtale.GeometricOperations.properPullback`). -/
def IsProperPullbackCompatible
    (δ : Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) aX ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} Λ') aX ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology s) ρ)
    (δ' : Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X') ρ ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) aX' ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} Λ') aX' ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology s) ρ)
    (h : X' ⟶ X) [IsProper h] (hh : h ≫ aX = aX') : Prop :=
  ∀ ⦃K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))⦄
    ⦃K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ'))⦄
    (hK : G.ctf X K) (hK' : G'.ctf X K')
    (η : K ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ).obj K'),
    G.properPullback h hh hK ≫ (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) aX').map
        (((upperStar (ModuleCat.{u + 1} Λ) h).leftDerivedFunctor).map η ≫
          (leftDerivedUpperStarRestrictScalarsIso ρ h).hom.app K') ≫
      δ'.hom.app (((upperStar (ModuleCat.{u + 1} Λ') h).leftDerivedFunctor).obj K') =
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) aX).map η ≫ δ.hom.app K' ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology s) ρ).map (G'.properPullback h hh hK')

/-- The iterates `Φ^m` of an endomorphism over `s` are endomorphisms over `s`. -/
lemma endPow_comp {Φ : X ⟶ X} (hΦ : Φ ≫ aX = aX) (m : ℕ) : endPow Φ m ≫ aX = aX := by
  induction m with
  | zero => exact Category.id_comp aX
  | succ m ih => rw [endPow_succ, Category.assoc, ih, hΦ]

omit [IsGeometric aX'] [HasCompactification aX'] in
include ρ in
/-- If two Frobenius coefficient morphisms are compatible along `t : K ⟶ Res K'` and the
compact-support comparison `δ` is compatible with the proper pullbacks along `Φ^m`, then
`Ra_{X!} t` read through `δ` intertwines the global operators
`Ra_{X!}(ψ_m) ∘ (Φ^m)^*` and `Ra_{X!}(ψ'_m) ∘ (Φ^m)^*`. -/
theorem properPullback_comp_map_iterCoeff {Φ : X ⟶ X} (hΦ : Φ ≫ aX = aX) (m : ℕ)
    [IsProper (endPow Φ m)]
    (δ : Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) aX ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} Λ') aX ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology s) ρ)
    (hδ : IsProperPullbackCompatible ρ G G' δ δ (endPow Φ m) (endPow_comp hΦ m))
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    {K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ'))}
    (hK : G.ctf X K) (hK' : G'.ctf X K')
    (ψ : ((upperStar (ModuleCat.{u + 1} Λ) Φ).leftDerivedFunctor).obj K ⟶ K)
    (ψ' : ((upperStar (ModuleCat.{u + 1} Λ') Φ).leftDerivedFunctor).obj K' ⟶ K')
    (t : K ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ).obj K')
    (h : ψ ≫ t = ((upperStar (ModuleCat.{u + 1} Λ) Φ).leftDerivedFunctor).map t ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ Φ).hom.app K' ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ).map ψ') :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) aX).map t ≫ δ.hom.app K' ≫
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology s) ρ).map
          (G'.properPullback (endPow Φ m) (endPow_comp hΦ m) hK' ≫
            (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ') aX).map (iterCoeff Φ ψ' m)) =
      (G.properPullback (endPow Φ m) (endPow_comp hΦ m) hK ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) aX).map (iterCoeff Φ ψ m)) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) aX).map t ≫ δ.hom.app K' := by
  have hn := δ.hom.naturality (iterCoeff Φ ψ' m)
  simp only [Functor.comp_map] at hn
  rw [Functor.map_comp, ← reassoc_of% (hδ hK hK' t), ← hn, Category.assoc,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
    ← iterCoeff_comp_eq ρ Φ ψ ψ' t h m, Functor.map_comp_assoc]

omit [IsGeometric aX'] [HasCompactification aX'] in
include ρ in
/-- The version of `AlgebraicGeometry.ProEtale.properPullback_comp_map_iterCoeff` for compact
cohomology `RΓ_c(X, -) = RΓ(s, Ra_{X!} -)`, read through the comparison
`AlgebraicGeometry.ProEtale.compactCoefficientIso` built from `δ` and a natural point
identification `αs`. -/
theorem compactlySupportedGlobalSections_map_comp_properPullback {Φ : X ⟶ X}
    (hΦ : Φ ≫ aX = aX) (m : ℕ) [IsProper (endPow Φ m)]
    (δ : Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) aX ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} Λ') aX ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology s) ρ)
    (αs : Sheaf.derivedRestrictScalars (Scheme.ProEt.topology s) ρ ⋙
        rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s ≅
      rightDerivedGlobalSections (ModuleCat.{u + 1} Λ') s ⋙ ModuleCat.derivedRestrictScalars ρ)
    (hδ : IsProperPullbackCompatible ρ G G' δ δ (endPow Φ m) (endPow_comp hΦ m))
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    {K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ'))}
    (hK : G.ctf X K) (hK' : G'.ctf X K')
    (ψ : ((upperStar (ModuleCat.{u + 1} Λ) Φ).leftDerivedFunctor).obj K ⟶ K)
    (ψ' : ((upperStar (ModuleCat.{u + 1} Λ') Φ).leftDerivedFunctor).obj K' ⟶ K')
    (t : K ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ).obj K')
    (h : ψ ≫ t = ((upperStar (ModuleCat.{u + 1} Λ) Φ).leftDerivedFunctor).map t ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ Φ).hom.app K' ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ).map ψ') :
    (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).map t ≫
        (compactCoefficientIso ρ aX δ αs).hom.app K' ≫
        (ModuleCat.derivedRestrictScalars ρ).map ((rightDerivedGlobalSections _ s).map
          (G'.properPullback (endPow Φ m) (endPow_comp hΦ m) hK' ≫
            (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ') aX).map (iterCoeff Φ ψ' m))) =
      (rightDerivedGlobalSections _ s).map
          (G.properPullback (endPow Φ m) (endPow_comp hΦ m) hK ≫
            (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) aX).map (iterCoeff Φ ψ m)) ≫
        (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).map t ≫
        (compactCoefficientIso ρ aX δ αs).hom.app K' := by
  have hα := αs.hom.naturality (G'.properPullback (endPow Φ m) (endPow_comp hΦ m) hK' ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ') aX).map (iterCoeff Φ ψ' m))
  have hs := congrArg (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s).map
    (properPullback_comp_map_iterCoeff ρ G G' hΦ m δ hδ hK hK' ψ ψ' t h)
  simp only [Functor.comp_map] at hα
  simp only [Functor.map_comp, Category.assoc] at hs
  simp only [compactCoefficientIso_hom_app, compactlySupportedGlobalSections, Functor.comp_map,
    Category.assoc]
  rw [← hα]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hs]

end Generic

end AlgebraicGeometry.ProEtale
