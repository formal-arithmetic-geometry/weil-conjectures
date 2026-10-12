/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem
public import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.Mathlib.Data.Nat.Factorization.Induction

/-!
# Derived smooth base change

Fix a commutative ring `Λ` and a Cartesian square of schemes

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `p` smooth and `g` quasi-compact and quasi-separated. The smooth base change theorem
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth` says that the degreewise
base-change maps `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` are isomorphisms for every sheaf `F` which is
torsion of orders invertible on `S`. This file deduces the derived forms of the theorem: the
derived base-change map

`BC(K) : p^*(Rg_* K) ⟶ Rh_*(e^* K)`

of `AlgebraicGeometry.Etale.baseChange` is an isomorphism for every bounded below complex `K`
whose cohomology sheaves are torsion of orders invertible on `S`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChange_app_of_isGE_of_isLE`: the finite-range comparison
  (blueprint `sbc-lem-finite-range-comparison`).
- `AlgebraicGeometry.Etale.isIso_homologyFunctor_map_rightDerivedFunctorPlus_map_truncLEι_app`
  and its companions: the bounded-below truncation criterion (blueprint
  `sbc-lem-bounded-below-truncation-criterion`).
- `AlgebraicGeometry.Etale.isIso_baseChange_app_of_bounded_of_smooth`: bounded complexes with
  allowable torsion (blueprint `sbc-thm-bounded-allowable-torsion`).
- `AlgebraicGeometry.Etale.isIso_baseChange_app_of_smooth`: bounded below complexes with allowable
  torsion (blueprint `sbc-thm-bounded-below-derived-smooth-base-change`).
- `AlgebraicGeometry.Etale.isIso_baseChange_app_of_boundedConstructible_of_smooth`: bounded
  constructible complexes of sheaves of modules over a ring killed by an integer invertible on
  `S` (blueprint `sbc-thm-bounded-derived-smooth-base-change`).

## Implementation notes

The blueprint compares the hypercohomology spectral sequences of the two sides. Here the
comparison is made by dévissage along the truncation triangles
(`DerivedCategory.Plus.isIso_app_of_isGE_of_isLE`), using that the derived base-change map
commutes with the shifts (`AlgebraicGeometry.Etale.commShift_baseChange`); for bounded below
complexes, `Hⁿ` of both sides only depends on `τ_{≤ n} K`
(`DerivedCategory.Plus.isIso_homologyFunctor_map_map_truncLEι_app`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

open DerivedCategory.Plus.TStructure (t)

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The set of primes invertible on a scheme `S`. -/
def Scheme.invertiblePrimes (S : Scheme.{u}) : Set ℕ :=
  {p | p.Prime ∧ IsUnit (p : Γ(S, ⊤))}

/-- A sheaf which is torsion with prime divisors invertible on `S` is torsion of orders
invertible on `S`. -/
lemma Scheme.IsTorsionModuleSheafOfInvertibleOrder.of_isTorsionSheafOfPrimes {S T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheafOfPrimes S.invertiblePrimes F] : IsTorsionModuleSheafOfInvertibleOrder S F where
  exists_isUnit_nsmul_eq_zero Ω _ _ s x := by
    obtain ⟨n, hn, hP, hx⟩ :=
      IsTorsionModuleSheafOfPrimes.exists_nsmul_eq_zero (P := S.invertiblePrimes) Ω s x
    exact ⟨n, hn, isUnit_natCast_of_forall_mem_primeFactors n hn fun p hp ↦ (hP p hp).2, hx⟩

/-- Being torsion of orders invertible on `S` is invariant under isomorphisms of sheaves. -/
lemma Scheme.IsTorsionModuleSheafOfInvertibleOrder.of_iso {S T : Scheme.{u}}
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ≅ G)
    [IsTorsionModuleSheafOfInvertibleOrder S F] : IsTorsionModuleSheafOfInvertibleOrder S G where
  exists_isUnit_nsmul_eq_zero Ω _ _ s x := by
    let ψ := (pointSmallEtale s).sheafFiber.mapIso φ
    obtain ⟨n, hn, hu, hx⟩ :=
      IsTorsionModuleSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero (S := S) (F := F) Ω s
        (ψ.inv.hom x)
    refine ⟨n, hn, hu, ?_⟩
    have : ψ.hom.hom (ψ.inv.hom x) = x := by
      rw [← ModuleCat.comp_apply, ψ.inv_hom_id, ModuleCat.id_apply]
    rw [← this, ← map_nsmul, hx, map_zero]

/-- The property of being torsion of orders invertible on `S`, as a property of sheaves. -/
def Scheme.isTorsionSheafOfInvertibleOrder (S : Scheme.{u}) (T : Scheme.{u}) :
    ObjectProperty (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fun F ↦ IsTorsionModuleSheafOfInvertibleOrder S F

instance (S T : Scheme.{u}) :
    (isTorsionSheafOfInvertibleOrder Λ S T).IsClosedUnderIsomorphisms where
  of_iso φ h := by
    have : IsTorsionModuleSheafOfInvertibleOrder S _ := h
    exact IsTorsionModuleSheafOfInvertibleOrder.of_iso Λ φ

variable {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- The derived base-change map is an isomorphism at a sheaf `F` placed in degree `0` if and only
if all the degreewise base-change maps at `F` are isomorphisms. -/
lemma Etale.isIso_baseChange_app_singleFunctor_obj_iff (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ↔
      ∀ q, IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  rw [DerivedCategory.Plus.isIso_iff]
  simp only [Etale.isIso_baseChangeHomologyMap_iff]

/-- The source `p^* ∘ Rg_*` of the derived base-change map does not lower the cohomological
degree. -/
lemma Etale.isZero_homologyFunctor_baseChangeSource_obj (p : X ⟶ S) (g : T ⟶ S)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    [K.IsGE n] (q : ℤ) (hq : q < n) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((R+((g)_*[ModuleCat.{u + 1} Λ]) ⋙ D+((p)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  refine IsZero.of_iso ?_ (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso
    q |>.app _).symm
  exact Functor.map_isZero (p)^*[ModuleCat.{u + 1} Λ]
    (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ K n hq)

/-- The target `Rh_* ∘ e^*` of the derived base-change map does not lower the cohomological
degree. -/
lemma Etale.isZero_homologyFunctor_baseChangeTarget_obj (e : Y ⟶ T) (h : Y ⟶ X)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    [K.IsGE n] (q : ℤ) (hq : q < n) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((D+((e)^*[ModuleCat.{u + 1} Λ]) ⋙ R+((h)_*[ModuleCat.{u + 1} Λ])).obj K)) := by
  have : (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K).IsGE n := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
    intro i hi
    refine IsZero.of_iso ?_ (((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso
      i |>.app _).symm
    exact Functor.map_isZero (e)^*[ModuleCat.{u + 1} Λ]
      (DerivedCategory.Plus.isZero_homology_of_isGE K n i hi)
  exact Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ _ n hq

/-- Blueprint `sbc-lem-bounded-below-truncation-criterion`: for `K ∈ D⁺(T_ét)`, only the
cohomology sheaves of `K` in degrees `≤ n` contribute to `Hⁿ(Rg_* K)`: the map
`Hⁿ(Rg_* τ_{≤ n} K) ⟶ Hⁿ(Rg_* K)` is an isomorphism. -/
lemma Etale.isIso_homologyFunctor_map_rightDerivedFunctorPlus_map_truncLEι_app (g : T ⟶ S)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      (R+((g)_*[ModuleCat.{u + 1} Λ]).map ((t.truncLEι n).app K))) :=
  DerivedCategory.Plus.isIso_homologyFunctor_map_map_truncLEι_app _
    (fun K n _ _ hq ↦ Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ K n hq)
    K n

/-- Blueprint `sbc-lem-bounded-below-truncation-criterion`, after pullback: the map
`Hⁿ(p^* Rg_* τ_{≤ n} K) ⟶ Hⁿ(p^* Rg_* K)` is an isomorphism. -/
lemma Etale.isIso_homologyFunctor_map_baseChangeSource_map_truncLEι_app (p : X ⟶ S) (g : T ⟶ S)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((R+((g)_*[ModuleCat.{u + 1} Λ]) ⋙ D+((p)^*[ModuleCat.{u + 1} Λ])).map
        ((t.truncLEι n).app K))) :=
  DerivedCategory.Plus.isIso_homologyFunctor_map_map_truncLEι_app _
    (fun K n _ q hq ↦ Etale.isZero_homologyFunctor_baseChangeSource_obj Λ p g K n q hq) K n

/-- Blueprint `sbc-lem-bounded-below-truncation-criterion`, for `h_*`: the map
`Hⁿ(Rh_* e^* τ_{≤ n} K) ⟶ Hⁿ(Rh_* e^* K)` is an isomorphism. -/
lemma Etale.isIso_homologyFunctor_map_baseChangeTarget_map_truncLEι_app (e : Y ⟶ T) (h : Y ⟶ X)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((D+((e)^*[ModuleCat.{u + 1} Λ]) ⋙ R+((h)_*[ModuleCat.{u + 1} Λ])).map
        ((t.truncLEι n).app K))) :=
  DerivedCategory.Plus.isIso_homologyFunctor_map_map_truncLEι_app _
    (fun K n _ q hq ↦ Etale.isZero_homologyFunctor_baseChangeTarget_obj Λ e h K n q hq) K n

/-- Blueprint `sbc-lem-finite-range-comparison`: let `K ∈ D⁺(T_ét)` have cohomology sheaves
concentrated in `[a, b]`. If the comparison of the two hypercohomology spectral sequences is an
isomorphism on every `E₂`-term, i.e. the base-change map
`p⁻¹ R^i g_* Hʲ(K) ⟶ R^i h_* e⁻¹ Hʲ(K)` is an isomorphism for all `i` and `j`, then the derived
base-change map `BC(K)` is an isomorphism. -/
theorem Etale.isIso_baseChange_app_of_isGE_of_isLE (sq : IsPullback e h g p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a b : ℤ)
    [K.IsGE a] [K.IsLE b]
    (hK : ∀ i j, IsIso (Etale.baseChangeHomologyMap Λ sq i
      ((DerivedCategory.Plus.homologyFunctor _ j).obj K))) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
  let P : ObjectProperty (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := fun F ↦
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
  have : P.IsClosedUnderIsomorphisms := ⟨fun φ h ↦
    (NatTrans.isIso_app_iff_of_iso _ ((DerivedCategory.Plus.singleFunctor _ 0).mapIso φ)).1 h⟩
  exact DerivedCategory.Plus.isIso_app_of_bounded _ P (fun _ hF ↦ hF) K a b fun j ↦
    (Etale.isIso_baseChange_app_singleFunctor_obj_iff Λ sq _).2 fun i ↦ hK i j

variable (p) in
/-- The derived base-change map of a smooth base change square is an isomorphism at a sheaf which
is torsion of orders invertible on `S`, placed in degree `0`. -/
lemma Etale.isIso_baseChange_app_singleFunctor_obj_of_smooth [Smooth p] [QuasiCompact g]
    [QuasiSeparated g] (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheafOfInvertibleOrder S F] :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  (Etale.isIso_baseChange_app_singleFunctor_obj_iff Λ sq F).2 fun q ↦
    Etale.isIso_baseChangeHomologyMap_of_smooth Λ p g e h sq q F

variable (p) in
/-- The derived base-change map of a smooth base change square is an isomorphism at every bounded
below complex whose cohomology sheaves are torsion of orders invertible on `S`. -/
theorem Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder [Smooth p]
    [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ j, IsTorsionModuleSheafOfInvertibleOrder S
      ((DerivedCategory.Plus.homologyFunctor _ j).obj K)) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
  DerivedCategory.Plus.isIso_app_of_forall_homology _ (isTorsionSheafOfInvertibleOrder Λ S T)
    (fun F hF ↦ have : IsTorsionModuleSheafOfInvertibleOrder S F := hF
      Etale.isIso_baseChange_app_singleFunctor_obj_of_smooth Λ p sq F)
    (fun K n _ q hq ↦ Etale.isZero_homologyFunctor_baseChangeSource_obj Λ p g K n q hq)
    (fun K n _ q hq ↦ Etale.isZero_homologyFunctor_baseChangeTarget_obj Λ e h K n q hq) K hK

/-- Blueprint `sbc-def-derived-categories-with-allowable-torsion`, bounded version: the objects of
`D^b_P-tor(X_ét)`, the bounded complexes of `D⁺(X_ét, Λ)` whose cohomology sheaves have
`P`-torsion geometric stalks, for a set `P` of primes. The bounded below version is
`AlgebraicGeometry.Etale.DerivedCategory.Plus.moduleTorsionHomologyOfPrimes`. -/
noncomputable def Etale.DerivedCategory.Plus.boundedTorsionHomologyOfPrimes (X : Scheme.{u})
    (P : Set ℕ) :
    ObjectProperty (DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  t.bounded ⊓ Etale.DerivedCategory.Plus.moduleTorsionHomologyOfPrimes Λ X P

variable (p) in
/-- Blueprint `sbc-thm-bounded-allowable-torsion`: for a Cartesian square with `p` smooth and
`g` quasi-compact and quasi-separated, and `P` the set of primes invertible on `S`, the derived
base-change map `BC(K) : p^*(Rg_* K) ⟶ Rh_*(e^* K)` is an isomorphism for every
`K ∈ D^b_P-tor(T_ét)`. Both sides are then bounded below; the comparison is made in
`D⁺(X_ét, Λ)`. -/
theorem Etale.isIso_baseChange_app_of_bounded_of_smooth [Smooth p] [QuasiCompact g]
    [QuasiSeparated g] (sq : IsPullback e h g p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.Plus.boundedTorsionHomologyOfPrimes Λ T S.invertiblePrimes K) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hK⟩ := hK
  exact DerivedCategory.Plus.isIso_app_of_bounded _ (isTorsionSheafOfInvertibleOrder Λ S T)
    (fun F hF ↦ have : IsTorsionModuleSheafOfInvertibleOrder S F := hF
      Etale.isIso_baseChange_app_singleFunctor_obj_of_smooth Λ p sq F) K a b fun j ↦
    have := hK j
    IsTorsionModuleSheafOfInvertibleOrder.of_isTorsionSheafOfPrimes Λ _

variable (p) in
/-- Blueprint `sbc-thm-bounded-below-derived-smooth-base-change`: for a Cartesian square with `p`
smooth and `g` quasi-compact and quasi-separated, and a bounded below complex
`K ∈ D⁺_P-tor(T_ét)` whose cohomology sheaves are torsion with prime divisors invertible on `S`,
the derived base-change map `BC(K) : p^*(Rg_* K) ⟶ Rh_*(e^* K)` is an isomorphism. -/
theorem Etale.isIso_baseChange_app_of_smooth [Smooth p] [QuasiCompact g] [QuasiSeparated g]
    (sq : IsPullback e h g p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.Plus.moduleTorsionHomologyOfPrimes Λ T S.invertiblePrimes K) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
  Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder Λ p sq K fun j ↦
    have := hK j
    IsTorsionModuleSheafOfInvertibleOrder.of_isTorsionSheafOfPrimes Λ _

/-- If a nonzero integer `N` kills the coefficient ring `Λ` and is invertible on `S`, then every
sheaf of `Λ`-modules is torsion of orders invertible on `S`. -/
lemma Scheme.IsTorsionModuleSheafOfInvertibleOrder.of_natCast_eq_zero {S T : Scheme.{u}} (N : ℕ)
    (hN₀ : N ≠ 0) (hN : (N : Λ) = 0) (hNS : IsUnit (N : Γ(S, ⊤)))
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsTorsionModuleSheafOfInvertibleOrder S F where
  exists_isUnit_nsmul_eq_zero Ω _ _ s x :=
    ⟨N, Nat.pos_of_ne_zero hN₀, hNS, by rw [← Nat.cast_smul_eq_nsmul Λ, hN, zero_smul]⟩

variable (p) in
/-- Blueprint `sbc-thm-bounded-derived-smooth-base-change`: for a Cartesian square with `p`
smooth and `g` quasi-compact and quasi-separated, and a coefficient ring `Λ` killed by a nonzero
integer `N` invertible on `S`, the derived base-change map
`BC(K) : p^*(Rg_* K) ⟶ Rh_*(e^* K)` is an isomorphism for every `K ∈ D^b_c(T_ét, Λ)`. Since
`K` is bounded and `p^*` is exact, `BC(K)` is computed in the bounded below derived
categories. -/
theorem Etale.isIso_baseChange_app_of_boundedConstructible_of_smooth [Smooth p]
    [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g p) (N : ℕ) (hN₀ : N ≠ 0)
    (hN : (N : Λ) = 0) (hNS : IsUnit (N : Γ(S, ⊤)))
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T K) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app ⟨K, hK.1.1⟩) :=
  Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder Λ p sq _ fun _ ↦
    IsTorsionModuleSheafOfInvertibleOrder.of_natCast_eq_zero Λ N hN₀ hN hNS _

end AlgebraicGeometry
