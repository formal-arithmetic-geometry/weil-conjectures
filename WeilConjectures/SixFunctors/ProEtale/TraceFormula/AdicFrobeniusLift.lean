/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusTrace

/-!
# Frobenius operators on the adic realization and their traces

Let `ψ_•` be a compatible system of Frobenius coefficient morphisms on a normalized adic system
`L_•` over a geometric scheme `a_X : X ⟶ Spec k`
(`AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem`). This file proves items (3) and (4)
of blueprint `prop-trf-adic-coefficient-morphism-systems` and the equivariance clause of
`sk-prop-trace-adic` (ii):

* the stalk Frobenius endomorphisms `(ψ_{n,m})_x̄` at a point `x̄` fixed by `Φ^m` form a
  compatible family on the normalized tower of perfect complexes `(L_n)_x̄`, and the global
  Frobenius operators `F_{c,m}(ψ_n) = T_{c_m}(ψ_{n,m})` form a compatible family on the
  normalized tower `RΓ_c(X, L_n)`;
* both families lift to endomorphisms of the realizations over `R`
  (the realization isomorphisms `P_𝒪 ⊗ᴸ A_n ≅ P_n` intertwine the lift with the levelwise
  operators: this is the equivariance of `sk-prop-trace-adic` (ii));
* the categorical trace of a lift is well defined, and reduces modulo `Iⁿ` to the levelwise
  traces.

## Main results

- `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.isCompatible_stalkFrobeniusFamily`,
  `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.isCompatible_globalOperatorFamily`:
  blueprint `prop-trf-adic-coefficient-morphism-systems` (3).
- `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.exists_isLift_stalkFrobeniusFamily`,
  `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.exists_isLift_globalOperatorFamily`:
  lifts to the realizations (`prop-trf-adic-coefficient-morphism-systems` (2),
  `sk-prop-trace-adic` (ii)).
- `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.exists_trace_eq_stalkFrobeniusFamily`,
  `AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem.exists_trace_eq_globalOperatorFamily`
  and the `trace_eq_of_isLift_*` statements: blueprint
  `prop-trf-adic-coefficient-morphism-systems` (4).

## Implementation notes

The towers are those of `WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicSystem`, built
from coefficient identifications of the form `AlgebraicGeometry.ProEtale.stalkCoefficientIso`
and `AlgebraicGeometry.ProEtale.compactCoefficientIso`, as produced by
`AlgebraicGeometry.ProEtale.exists_isCoefficientChange_stalk` and
`AlgebraicGeometry.ProEtale.exists_isCoefficientChange_compactlySupportedGlobalSections`.
The global operators of the levels are built from operation packages `G n` of the levels, whose
compatibility with the coefficient comparisons of compact support is the hypothesis
`AlgebraicGeometry.ProEtale.IsProperPullbackCompatible` (see
`WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusTrace`).

The level `n` of the towers of perfect complexes is the level `n + 1` of the adic system (the
rings `R ⧸ Iⁿ⁺¹`), so that the families below are indexed accordingly.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated MonoidalCategory

namespace AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} {X : Scheme.{u}} {S : AdicSystem I X}
  {k : Type u} [Field k] [IsSepClosed k] {aX : X ⟶ Spec (.of k)} [IsGeometric aX]
  [HasCompactification aX] [∀ n, Finite (R ⧸ I ^ n)]
  [∀ n, HasInvertibleExponent (R ⧸ I ^ n) (Spec (.of k))]
  {Φ : X ⟶ X} {hΦ : Φ ≫ aX = aX} (F : S.FrobeniusSystem Φ hΦ)

/-- The stalk Frobenius of the Weil complex `(L_n, ψ_n)` is computed from the iterates
`ψ_{n,m}`. -/
lemma weilComplex_stalkFrobenius (n m : ℕ) (x : Spec (.of k) ⟶ X)
    (hx : x ≫ endPow Φ m = x) :
    (F.weilComplex n).stalkFrobenius m x hx =
      (leftDerivedUpperStarCongr (ModuleCat.{u + 1} (R ⧸ I ^ n)) hx).inv.app (S.obj n) ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} (R ⧸ I ^ n)) x (endPow Φ m)).hom.app
          (S.obj n) ≫
        ((upperStar (ModuleCat.{u + 1} (R ⧸ I ^ n)) x).leftDerivedFunctor).map
          (iterCoeff Φ (F.coeff n) m) := by
  rw [WeilComplex.stalkFrobenius, weilComplex_coeffIterate]
  rfl

section Stalk

variable (x : Spec (.of k) ⟶ X) (hx : x ≫ aX = 𝟙 _) (m : ℕ) (hxm : x ≫ endPow Φ m = x)
  (αs : ∀ n : ℕ, Sheaf.derivedRestrictScalars (Scheme.ProEt.topology (Spec (.of k)))
      (levelρ I n) ⋙ rightDerivedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1)))
        (Spec (.of k)) ≅
    rightDerivedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) (Spec (.of k)) ⋙
      ModuleCat.derivedRestrictScalars (levelρ I n))
  (hα : ∀ n : ℕ, IsCoefficientChange (levelρ I n) _ _ (stalkCoefficientIso (levelρ I n) x (αs n)))

/-- The stalk Frobenius endomorphisms `RΓ(s, (ψ_{n+1,m})_x̄)` of the levels `(L_{n+1})_x̄` of the
stalk tower, at a point `x̄` fixed by `Φ^m` (blueprint
`prop-trf-adic-coefficient-morphism-systems` (3)). -/
noncomputable def stalkFrobeniusFamily (n : ℕ) :
    (S.stalkTower aX x hx (fun n ↦ stalkCoefficientIso (levelρ I n) x (αs n)) hα).obj n ⟶
      (S.stalkTower aX x hx (fun n ↦ stalkCoefficientIso (levelρ I n) x (αs n)) hα).obj n :=
  (rightDerivedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) (Spec (.of k))).map
    ((F.weilComplex (n + 1)).stalkFrobenius m x hxm)

/-- Blueprint `prop-trf-adic-coefficient-morphism-systems` (3), stalks: the stalk Frobenius
endomorphisms `(ψ_{n,m})_x̄` at a point `x̄` fixed by `Φ^m` form a compatible family on the
normalized tower of perfect complexes `(L_n)_x̄`. -/
theorem isCompatible_stalkFrobeniusFamily :
    (S.stalkTower aX x hx (fun n ↦ stalkCoefficientIso (levelρ I n) x (αs n)) hα).IsCompatible
      (F.stalkFrobeniusFamily x hx m hxm αs hα) := by
  intro n
  simp only [stalkFrobeniusFamily, stalkTower, weilComplex_stalkFrobenius, Category.assoc]
  exact geometricStalk_map_comp_stalkCoefficientIso (levelρ I n) Φ (F.coeff (n + 1 + 1))
    (F.coeff (n + 1)) (S.map (n + 1)) (αs n) (F.comm (n + 1)) m x hxm

end Stalk

section Global

variable [∀ n, Abelian.HasFunctorialFlatResolution (ModuleCat.{u + 1} (R ⧸ I ^ n))]
  [∀ n, DerivedBraiding (ModuleCat.{u + 1} (R ⧸ I ^ n))]
  (G : ∀ n, GeometricOperations (ModuleCat.{u + 1} (R ⧸ I ^ n)) (Spec (.of k)))
  (m : ℕ) [IsProper (endPow Φ m)]
  (δ : ∀ n : ℕ, Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) (levelρ I n) ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX ≅
    rightDerivedLowerShriek (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX ⋙
      Sheaf.derivedRestrictScalars (Scheme.ProEt.topology (Spec (.of k))) (levelρ I n))
  (αs : ∀ n : ℕ, Sheaf.derivedRestrictScalars (Scheme.ProEt.topology (Spec (.of k)))
      (levelρ I n) ⋙ rightDerivedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1)))
        (Spec (.of k)) ≅
    rightDerivedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) (Spec (.of k)) ⋙
      ModuleCat.derivedRestrictScalars (levelρ I n))
  (hα : ∀ n : ℕ, IsCoefficientChange (levelρ I n) _ _
    (compactCoefficientIso (levelρ I n) aX (δ n) (αs n)))

/-- The global Frobenius operator `F_{c,m}(ψ_n) = T_{c_m}(ψ_{n,m})` of the Weil complex
`(L_n, ψ_n)`, the global operator of its graph correspondence `c_m = (𝟙, Φ^m)`, is the proper
pullback along `Φ^m` followed by `Ra_{X!} ψ_{n,m}`. -/
lemma globalOperator_weilComplex_graph (n : ℕ) :
    haveI : IsProper ((F.weilComplex n).frobeniusIterate m) := ‹IsProper (endPow Φ m)›
    Correspondence.globalOperator (G n)
        ((F.weilComplex n).graph (G n) (S.constructibleFiniteTor n) m)
        (S.constructibleFiniteTor n) =
      (G n).properPullback (endPow Φ m) (endPow_comp hΦ m) (S.constructibleFiniteTor n) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} (R ⧸ I ^ n)) aX).map
          (iterCoeff Φ (F.coeff n) m) := by
  rw [Correspondence.globalOperator_ofGraph, weilComplex_coeffIterate]
  rfl

/-- The global Frobenius operators `RΓ(s, F_{c,m}(ψ_{n+1}))` on the levels `RΓ_c(X, L_{n+1})` of
the compact-support tower (blueprint `prop-trf-adic-coefficient-morphism-systems` (3)). -/
noncomputable def globalOperatorFamily (n : ℕ) :
    (S.compactSupportTower aX (fun n ↦ compactCoefficientIso (levelρ I n) aX (δ n) (αs n))
        hα).obj n ⟶
      (S.compactSupportTower aX (fun n ↦ compactCoefficientIso (levelρ I n) aX (δ n) (αs n))
        hα).obj n :=
  haveI : IsProper ((F.weilComplex (n + 1)).frobeniusIterate m) := ‹IsProper (endPow Φ m)›
  (rightDerivedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) (Spec (.of k))).map
    (Correspondence.globalOperator (G (n + 1))
      ((F.weilComplex (n + 1)).graph (G (n + 1)) (S.constructibleFiniteTor (n + 1)) m)
      (S.constructibleFiniteTor (n + 1)))

/-- Blueprint `prop-trf-adic-coefficient-morphism-systems` (3), global operators: if the
compact-support comparisons `δ n` are compatible with the proper pullbacks along `Φ^m` of the
operation packages of the levels, the global Frobenius operators `F_{c,m}(ψ_n)` form a
compatible family on the normalized tower of perfect complexes `RΓ_c(X, L_n)`. -/
theorem isCompatible_globalOperatorFamily
    (hδ : ∀ n : ℕ, IsProperPullbackCompatible (levelρ I n) (G (n + 1 + 1)) (G (n + 1)) (δ n)
      (δ n) (endPow Φ m) (endPow_comp hΦ m)) :
    (S.compactSupportTower aX (fun n ↦ compactCoefficientIso (levelρ I n) aX (δ n) (αs n))
        hα).IsCompatible (F.globalOperatorFamily G m δ αs hα) := by
  intro n
  simp only [globalOperatorFamily, compactSupportTower, globalOperator_weilComplex_graph,
    Category.assoc]
  exact compactlySupportedGlobalSections_map_comp_properPullback (levelρ I n) (G (n + 1 + 1))
    (G (n + 1)) hΦ m (δ n) (αs n) (hδ n) (S.constructibleFiniteTor (n + 1 + 1))
    (S.constructibleFiniteTor (n + 1)) (F.coeff (n + 1 + 1)) (F.coeff (n + 1)) (S.map (n + 1))
    (F.comm (n + 1))

end Global

end AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem

/-! ### Lifts to the realization and their traces -/

namespace AlgebraicGeometry.ProEtale

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} [IsLocalRing R] [IsAdicComplete I R]
  {ϖ : R} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal R) (hI : I = Ideal.span {ϖ})
  (T : ModuleCat.NormalizedPerfectTower (levelπ I) (levelρ I) (levelπ_eq I))
  {c : Cone T.restrict} (hc : IsHomotopyLimit c)

include hϖ in
lemma isLocalRing_quotient_pow_of_mem (hI : I = Ideal.span {ϖ}) (n : ℕ) :
    IsLocalRing (R ⧸ I ^ (n + 1)) :=
  isLocalRing_quotient_pow (by rw [hI, Ideal.span_le, Set.singleton_subset_iff]; exact hϖ) n

include hϖ hI hc in
/-- Blueprint `prop-trf-adic-coefficient-morphism-systems` (2), lifts, for the towers over the
rings `R ⧸ Iⁿ⁺¹` of a complete local ring `R` with `I = (ϖ)`: every compatible family of
endomorphisms of the levels lifts to an endomorphism `V` of the realization, i.e. the
realization isomorphisms `P ⊗ᴸ_R R ⧸ Iⁿ⁺¹ ≅ P_n` intertwine `V ⊗ᴸ R ⧸ Iⁿ⁺¹` with the levelwise
endomorphisms. -/
theorem exists_isLift_of_isCompatible {f : ∀ n, T.obj n ⟶ T.obj n} (hf : T.IsCompatible f) :
    ∃ V : c.pt ⟶ c.pt, T.IsLift c f V :=
  have := isLocalRing_quotient_pow_of_mem hϖ hI
  T.exists_isLift levelπ_surjective (ker_levelπ hI) exists_levelπ_eq
    eq_zero_of_forall_levelπ_eq_zero hc hf

section Trace

variable [Abelian.HasFunctorialFlatResolution (ModuleCat.{u + 1} R)]
  [∀ n, Abelian.HasFunctorialFlatResolution (ModuleCat.{u + 1} (R ⧸ I ^ n))]
  [BraidedCategory (DerivedCategory (ModuleCat.{u + 1} R))]
  [∀ n, BraidedCategory (DerivedCategory (ModuleCat.{u + 1} (R ⧸ I ^ n)))]
  (hβ : (β_ ((𝟙_ (DerivedCategory (ModuleCat.{u + 1} R)))⟦(1 : ℤ)⟧)
    ((𝟙_ (DerivedCategory (ModuleCat.{u + 1} R)))⟦(1 : ℤ)⟧)).hom = -𝟙 _)
  (hβA : ∀ n, (β_ ((𝟙_ (DerivedCategory (ModuleCat.{u + 1} (R ⧸ I ^ n))))⟦(1 : ℤ)⟧)
    ((𝟙_ (DerivedCategory (ModuleCat.{u + 1} (R ⧸ I ^ n))))⟦(1 : ℤ)⟧)).hom = -𝟙 _)
  [HasRightDual c.pt] [∀ n, HasRightDual (T.obj n)]

include hϖ hI hc hβ hβA in
/-- Blueprint `prop-trf-adic-coefficient-morphism-systems` (4): the categorical trace
`tr_R(V ∣ P)` of a lift `V` of a compatible family `f` reduces modulo `Iⁿ⁺¹` to the traces
`tr_{R ⧸ Iⁿ⁺¹}(f n ∣ P_n)`, so that it is the element `(tr(f n ∣ P_n))_n` of
`lim_n R ⧸ Iⁿ⁺¹ = R`. -/
theorem exists_trace_eq_of_isLift_of_isCompatible {f : ∀ n, T.obj n ⟶ T.obj n}
    (hf : T.IsCompatible f) {V : c.pt ⟶ c.pt} (hV : T.IsLift c f V) :
    ∃ r : R,
      MonoidalCategory.trace V = algebraMap R (End (𝟙_ (DerivedCategory (ModuleCat.{u + 1} R)))) r ∧
      ∀ n, MonoidalCategory.trace (f n) =
        algebraMap (R ⧸ I ^ (n + 1))
          (End (𝟙_ (DerivedCategory (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1)))))) (levelπ I n r) :=
  have := isLocalRing_quotient_pow_of_mem hϖ hI
  T.exists_trace_eq_of_isLift levelπ_surjective (ker_levelπ hI) exists_levelπ_eq
    eq_zero_of_forall_levelπ_eq_zero hc hβ (fun n ↦ hβA (n + 1)) hf hV

include hϖ hI hc hβ hβA in
/-- Blueprint `prop-trf-adic-coefficient-morphism-systems` (4): the categorical trace of a lift
of a compatible family does not depend on the lift. -/
theorem trace_eq_of_isLift_of_isCompatible {f : ∀ n, T.obj n ⟶ T.obj n}
    (hf : T.IsCompatible f) {V V' : c.pt ⟶ c.pt} (hV : T.IsLift c f V)
    (hV' : T.IsLift c f V') :
    MonoidalCategory.trace V = MonoidalCategory.trace V' :=
  have := isLocalRing_quotient_pow_of_mem hϖ hI
  T.trace_eq_of_isLift levelπ_surjective (ker_levelπ hI) exists_levelπ_eq
    eq_zero_of_forall_levelπ_eq_zero hc hβ (fun n ↦ hβA (n + 1)) hf hV hV'

end Trace

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} {X : Scheme.{u}} {S : AdicSystem I X}
  {k : Type u} [Field k] [IsSepClosed k] {aX : X ⟶ Spec (.of k)} [IsGeometric aX]
  [HasCompactification aX] [∀ n, Finite (R ⧸ I ^ n)]
  [∀ n, HasInvertibleExponent (R ⧸ I ^ n) (Spec (.of k))]
  {Φ : X ⟶ X} {hΦ : Φ ≫ aX = aX} (F : S.FrobeniusSystem Φ hΦ)
  [IsLocalRing R] [IsAdicComplete I R] {ϖ : R} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal R)
  (hI : I = Ideal.span {ϖ})

section Stalk

variable (x : Spec (.of k) ⟶ X) (hx : x ≫ aX = 𝟙 _) (m : ℕ) (hxm : x ≫ endPow Φ m = x)
  (αs : ∀ n : ℕ, Sheaf.derivedRestrictScalars (Scheme.ProEt.topology (Spec (.of k)))
      (levelρ I n) ⋙ rightDerivedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1)))
        (Spec (.of k)) ≅
    rightDerivedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) (Spec (.of k)) ⋙
      ModuleCat.derivedRestrictScalars (levelρ I n))
  (hα : ∀ n : ℕ, IsCoefficientChange (levelρ I n) _ _ (stalkCoefficientIso (levelρ I n) x (αs n)))
  {c : Cone (S.stalkTower aX x hx (fun n ↦ stalkCoefficientIso (levelρ I n) x (αs n))
    hα).restrict} (hc : IsHomotopyLimit c)

include hϖ hI hc in
/-- Blueprint `sk-prop-trace-adic` (ii), equivariance at a geometric stalk: the stalk Frobenius
endomorphisms `(ψ_{n,m})_x̄` of the levels lift to an endomorphism `V` of the realization
`P_{x̄, 𝒪} = R lim_n (L_n)_x̄`, intertwined with them by the realization isomorphisms
`P_{x̄, 𝒪} ⊗ᴸ A_n ≅ (L_n)_x̄`. -/
theorem exists_isLift_stalkFrobeniusFamily :
    ∃ V : c.pt ⟶ c.pt,
      (S.stalkTower aX x hx (fun n ↦ stalkCoefficientIso (levelρ I n) x (αs n)) hα).IsLift c
        (F.stalkFrobeniusFamily x hx m hxm αs hα) V :=
  exists_isLift_of_isCompatible hϖ hI _ hc (F.isCompatible_stalkFrobeniusFamily x hx m hxm αs hα)

end Stalk

section Global

variable [∀ n, Abelian.HasFunctorialFlatResolution (ModuleCat.{u + 1} (R ⧸ I ^ n))]
  [∀ n, DerivedBraiding (ModuleCat.{u + 1} (R ⧸ I ^ n))]
  (G : ∀ n, GeometricOperations (ModuleCat.{u + 1} (R ⧸ I ^ n)) (Spec (.of k)))
  (m : ℕ) [IsProper (endPow Φ m)]
  (δ : ∀ n : ℕ, Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) (levelρ I n) ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX ≅
    rightDerivedLowerShriek (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX ⋙
      Sheaf.derivedRestrictScalars (Scheme.ProEt.topology (Spec (.of k))) (levelρ I n))
  (αs : ∀ n : ℕ, Sheaf.derivedRestrictScalars (Scheme.ProEt.topology (Spec (.of k)))
      (levelρ I n) ⋙ rightDerivedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1)))
        (Spec (.of k)) ≅
    rightDerivedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) (Spec (.of k)) ⋙
      ModuleCat.derivedRestrictScalars (levelρ I n))
  (hα : ∀ n : ℕ, IsCoefficientChange (levelρ I n) _ _
    (compactCoefficientIso (levelρ I n) aX (δ n) (αs n)))
  (hδ : ∀ n : ℕ, IsProperPullbackCompatible (levelρ I n) (G (n + 1 + 1)) (G (n + 1)) (δ n)
      (δ n) (endPow Φ m) (endPow_comp hΦ m))
  {c : Cone (S.compactSupportTower aX
    (fun n ↦ compactCoefficientIso (levelρ I n) aX (δ n) (αs n)) hα).restrict}
  (hc : IsHomotopyLimit c)

include hϖ hI hc hδ in
/-- Blueprint `sk-prop-trace-adic` (ii), equivariance for compact cohomology: the global
Frobenius operators `F_{c,m}(ψ_n)` of the levels lift to an endomorphism `V` of the realization
`P_𝒪 = R lim_n RΓ_c(X, L_n)`, intertwined with them by the realization isomorphisms
`P_𝒪 ⊗ᴸ A_n ≅ RΓ_c(X, L_n)`. -/
theorem exists_isLift_globalOperatorFamily :
    ∃ V : c.pt ⟶ c.pt,
      (S.compactSupportTower aX (fun n ↦ compactCoefficientIso (levelρ I n) aX (δ n) (αs n))
        hα).IsLift c (F.globalOperatorFamily G m δ αs hα) V :=
  exists_isLift_of_isCompatible hϖ hI _ hc (F.isCompatible_globalOperatorFamily G m δ αs hα hδ)

end Global

end AlgebraicGeometry.ProEtale.AdicSystem.FrobeniusSystem
