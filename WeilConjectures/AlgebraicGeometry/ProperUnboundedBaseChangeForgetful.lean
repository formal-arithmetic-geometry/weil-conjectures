/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.AlgebraicGeometry.UnboundedCoefficientForgetfulAux

/-! # Transfer of unbounded exchange isomorphisms through coefficient forgetting -/

@[expose] public section

universe u

open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme
variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

private theorem isIso_of_isIso_derivedRestrictScalars_map
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    {T : Scheme.{u}} (φ : R →+* S)
    {K L : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S))}
    (a : K ⟶ L)
    (h : IsIso ((CategoryTheory.Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map a)) :
    IsIso a := by
  let F := CategoryTheory.Sheaf.restrictScalars T.smallEtaleTopology φ
  have hF : F.mapDerivedCategory.ReflectsIsomorphisms := by
    constructor
    intro K L e he
    rw [DerivedCategory.isIso_iff] at he ⊢
    intro n
    have hn := he n
    have hm : IsIso (F.map ((DerivedCategory.homologyFunctor _ n).map e)) :=
      (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) e).2 hn
    exact isIso_of_reflects_iso _ F
  let _ : F.mapDerivedCategory.ReflectsIsomorphisms := hF
  exact isIso_of_reflects_iso _ F.mapDerivedCategory

/-- Transfer an invertible Z/nZ exchange to coefficients in a ring killed by n.
No properness assertion is used, and `n` need not be positive (`ZMod 0` is `ℤ`).
(Stacks, Tag 0D6J) -/
theorem isIso_derivedBaseChangeMap_of_isIso_modN
    (n : ℕ) (hunit : n • (1 : Λ) = 0) (sq : IsPullback g' f' f g)
    (hbase : IsIso (Etale.derivedBaseChangeMap
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) sq.toCommSq))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((Etale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
  have hn : (n : Λ) = 0 := by simpa only [nsmul_one] using hunit
  let φ : ULift.{u + 1} (ZMod n) →+* Λ :=
    (ZMod.castHom (ringChar.dvd hn) Λ).comp ULift.ringEquiv.toRingHom
  apply isIso_of_isIso_derivedRestrictScalars_map (T := Y') φ
  apply (isIso_restricted_derivedBaseChangeMap_iff φ sq K).2
  let _ := hbase
  infer_instance

end AlgebraicGeometry
