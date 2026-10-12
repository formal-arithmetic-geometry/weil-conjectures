/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage

/-!
# Reduction of base change for torsion complexes to prime-torsion sheaves

For a cartesian square of schemes

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `g` quasi-compact and quasi-separated, this file shows that the derived base change map
`p^* Rg_* K ⟶ Rh_* e^* K` (`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`) is an
isomorphism at every `K ∈ D⁺(T_ét, Λ)` with torsion cohomology sheaves as soon as the
degreewise base change maps `p⁻¹ Rᵠg_* E ⟶ Rᵠh_* e⁻¹ E` are isomorphisms at every sheaf `E`
killed by a prime.

The proof has two steps:

- from sheaves killed by a prime to all torsion sheaves: the coefficient dévissage
  `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isTorsionSheaf`;
- from torsion sheaves to bounded below complexes with torsion cohomology: both sides of the
  derived base change map do not lower the cohomological degree, so `Hⁿ` of both sides only
  depends on the truncation `τ_{≤ n} K`, which is reached from its cohomology sheaves by
  finitely many distinguished triangles (`DerivedCategory.Plus.isIso_app_of_forall_homology`).

## Main statements

- `AlgebraicGeometry.Scheme.IsTorsionSheaf.of_nsmul_id_eq_zero`: a sheaf killed by a positive
  integer is torsion.
- `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_app_of_forall_isTorsionSheaf`: the
  passage from torsion sheaves to complexes with torsion cohomology.
- `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_app_of_prime`: the passage from
  prime-torsion sheaves to complexes with torsion cohomology.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- A sheaf of `Λ`-modules killed by a positive integer `n` is torsion: every geometric stalk
is killed by `n`, the stalk functor being additive. -/
lemma Scheme.IsTorsionSheaf.of_nsmul_id_eq_zero {X : Scheme.{u}}
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {n : ℕ} (hn : 0 < n)
    (hF : n • 𝟙 F = 0) : IsTorsionSheaf F where
  isTorsion_sheafFiber Ω _ _ s x := by
    have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
      hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
    have :=
      ((pointSmallEtale s).skyscraperSheafAdjunction (A := ModuleCat.{u + 1} Λ)).isLeftAdjoint
    have := (pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
    have h := (pointSmallEtale s).sheafFiber.map_nsmul (f := 𝟙 F) (n := n)
    rw [hF, Functor.map_zero, CategoryTheory.Functor.map_id] at h
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
    have := congrArg (fun φ ↦ φ.hom x) h
    simpa using this.symm

/-- Being torsion, as a property of sheaves of `Λ`-modules on `X_ét`. -/
def Scheme.isTorsionSheaf (X : Scheme.{u}) :
    ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fun F ↦ IsTorsionSheaf F

instance (X : Scheme.{u}) : (Scheme.isTorsionSheaf Λ X).IsClosedUnderIsomorphisms where
  of_iso φ h := by
    have : IsTorsionSheaf _ := h
    exact IsTorsionSheaf.of_epi φ.hom

variable {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- The derived base change map is an isomorphism at a sheaf `F` placed in degree `0` if and
only if all the degreewise base change maps `p⁻¹ Rᵠg_* F ⟶ Rᵠh_* e⁻¹ F` are isomorphisms. -/
lemma Etale.isIso_derivedBaseChangeMapPlus_app_singleFunctor_obj_iff (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ↔
      ∀ q, IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  rw [DerivedCategory.Plus.isIso_iff, ← Etale.baseChange_eq_derivedBaseChangeMapPlus]
  rfl

/-- The source `p^* ∘ Rg_*` of the derived base change map does not lower the cohomological
degree. -/
lemma Etale.isZero_homologyFunctor_derivedBaseChangeSource_obj (p : X ⟶ S) (g : T ⟶ S)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    [K.IsGE n] (q : ℤ) (hq : q < n) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((R+((g)_*[ModuleCat.{u + 1} Λ]) ⋙ D+((p)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  refine IsZero.of_iso ?_ (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso
    q |>.app _).symm
  exact Functor.map_isZero (p)^*[ModuleCat.{u + 1} Λ]
    (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ K n hq)

/-- The target `Rh_* ∘ e^*` of the derived base change map does not lower the cohomological
degree. -/
lemma Etale.isZero_homologyFunctor_derivedBaseChangeTarget_obj (e : Y ⟶ T) (h : Y ⟶ X)
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

/-- **From torsion sheaves to complexes with torsion cohomology.** If the degreewise base change
maps `p⁻¹ Rᵠg_* F ⟶ Rᵠh_* e⁻¹ F` are isomorphisms at every torsion sheaf `F`, then the
derived base change map `p^* Rg_* K ⟶ Rh_* e^* K` is an isomorphism at every
`K ∈ D⁺(T_ét, Λ)` all of whose cohomology sheaves are torsion. Both sides do not lower the
cohomological degree, so `Hⁿ` of both sides only depends on `τ_{≤ n} K`, which is an iterated
extension of its shifted cohomology sheaves. -/
theorem Etale.isIso_derivedBaseChangeMapPlus_app_of_forall_isTorsionSheaf
    (sq : IsPullback e h g p)
    (hF : ∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsTorsionSheaf F →
      ∀ q, IsIso (Etale.baseChangeHomologyMap Λ sq q F))
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.Plus.torsionHomology Λ T K) :
    IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
  DerivedCategory.Plus.isIso_app_of_forall_homology _ (Scheme.isTorsionSheaf Λ T)
    (fun F hF' ↦ (Etale.isIso_derivedBaseChangeMapPlus_app_singleFunctor_obj_iff Λ sq F).2
      (hF F hF'))
    (fun K n _ q hq ↦ Etale.isZero_homologyFunctor_derivedBaseChangeSource_obj Λ p g K n q hq)
    (fun K n _ q hq ↦ Etale.isZero_homologyFunctor_derivedBaseChangeTarget_obj Λ e h K n q hq)
    K hK

/-- **From prime-torsion sheaves to complexes with torsion cohomology.** Let `g` be
quasi-compact and quasi-separated. If the degreewise base change maps
`p⁻¹ Rᵠg_* E ⟶ Rᵠh_* e⁻¹ E` are isomorphisms at every sheaf `E` killed by a prime, then the
derived base change map is an isomorphism at every `K ∈ D⁺(T_ét, Λ)` with torsion cohomology:
combine the coefficient dévissage
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isTorsionSheaf` with
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_app_of_forall_isTorsionSheaf`. -/
theorem Etale.isIso_derivedBaseChangeMapPlus_app_of_prime (sq : IsPullback e h g p)
    [QuasiCompact g] [QuasiSeparated g]
    (hprime : ∀ r : ℕ, r.Prime → ∀ E : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      r • 𝟙 E = 0 → ∀ q, IsIso (Etale.baseChangeHomologyMap Λ sq q E))
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.Plus.torsionHomology Λ T K) :
    IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
  Etale.isIso_derivedBaseChangeMapPlus_app_of_forall_isTorsionSheaf Λ sq
    (fun F _ q ↦ Etale.isIso_baseChangeHomologyMap_of_isTorsionSheaf Λ sq hprime F q) K hK

end AlgebraicGeometry
