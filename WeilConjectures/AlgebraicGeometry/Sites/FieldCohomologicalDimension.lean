/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionDirectImage

/-!
# Torsion cohomological dimension and the ground field

The vanishing `Hᵠ(Spec K, F) = 0` for `q > 0` over a separably closed field `K`
(`AlgebraicGeometry.Scheme.subsingleton_H_of_pos_of_isSepClosed`, blueprint
`lem-kun-03qu-sep-closed`) says that `cd(Spec K) = 0`
(`AlgebraicGeometry.Scheme.torsionCohomologicalDimension_spec_of_isSepClosed`). If `X` is of
finite type over a field `K` with `cd_tor(K) ≤ c` and
`cd_tor(X_K̄) ≤ e` for an algebraic closure `K̄` of `K`, then `cd_tor(X) ≤ c + e`
(`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_add_of_isAlgClosure`, blueprint
`lem-sc-cd-ground-field`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

/-- `cd_tor` is invariant under isomorphisms; more generally it descends along universal
homeomorphisms: if `f : X ⟶ Y` is a universal homeomorphism and `cd_tor(X) ≤ c`, then
`cd_tor(Y) ≤ c`, étale cohomology being invariant under universal homeomorphisms
(`AlgebraicGeometry.Etale.cohomologyMap_bijective`). -/
lemma HasTorsionCohomologicalDimensionLE.of_isUniversalHomeomorphism {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsUniversalHomeomorphism f] {c : ℕ}
    (h : X.HasTorsionCohomologicalDimensionLE c) :
    Y.HasTorsionCohomologicalDimensionLE c := fun F hF q hq ↦
  have := h _ (Etale.isTorsion_upperStar f hF) q hq
  (Etale.cohomologyMap_bijective f F q).injective.subsingleton

/-- Blueprint `lem-kun-03qu-sep-closed`: Vanishing on a separably closed point.

If `K` is separably closed and `F` is an abelian sheaf on `Spec(K)_ét`, then
`Hᵠ(Spec(K)_ét, F) = 0` for every `q > 0`. This is
`AlgebraicGeometry.Scheme.subsingleton_H_of_isSepClosed` (the constant sheaf `ℤ` is projective),
stated for positive `q`. -/
theorem subsingleton_H_of_pos_of_isSepClosed (K : Type u) [Field K] [IsSepClosed K]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H F q) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hq
  simpa using subsingleton_H_of_isSepClosed K F n

/-- The spectrum of a separably closed field has torsion étale cohomological dimension at most
zero (`AlgebraicGeometry.Scheme.subsingleton_H_of_isSepClosed`). -/
lemma hasTorsionCohomologicalDimensionLE_zero_of_isSepClosed (K : Type u) [Field K]
    [IsSepClosed K] : (Spec (.of K)).HasTorsionCohomologicalDimensionLE 0 :=
  fun F _ q hq ↦ subsingleton_H_of_pos_of_isSepClosed K F q hq

/-- **Cohomological dimension of a separably closed point.** If `K` is a separably closed field,
then `cd(Spec K) = 0` in the sense of blueprint `def-kun-cd`. This is blueprint
`lem-kun-cd-sep-closed-point`, whose content (the vanishing of `Hᵠ(Spec K, F)` for `q > 0`) is
`AlgebraicGeometry.Scheme.subsingleton_H_of_isSepClosed`. -/
theorem torsionCohomologicalDimension_spec_of_isSepClosed (K : Type u) [Field K]
    [IsSepClosed K] : (Spec (.of K)).torsionCohomologicalDimension = 0 :=
  le_antisymm (torsionCohomologicalDimension_le_iff.2
    (hasTorsionCohomologicalDimensionLE_zero_of_isSepClosed K)) bot_le

/-- Blueprint `lem-sc-cd-ground-field`: Descent of a geometric cohomological dimension bound.

Let `X` be a scheme of finite type over a field `K` (structure morphism `a`), and let `K̄` be an
algebraic closure of `K`. If `cd_tor(K) ≤ c` and `cd_tor(X_K̄) ≤ e`, then `cd_tor(X) ≤ c + e`.
The proof uses the Leray spectral sequence of `a`
(`AlgebraicGeometry.Etale.subsingleton_H_of_rightDerived_lowerStar`), after reducing to sheaves
killed by an integer. The higher direct images `Rᵠa_* F` vanish for `q > e`
(`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isAlgClosure`): their stalks are the
colimits of those of the higher direct images from the `X_L`, `L` running over the finite
subextensions of `K^sep/K`, into which they inject, and the higher direct image from
`X_{K^sep}` vanishes since `cd_tor(X_{K^sep}) = cd_tor(X_K̄) ≤ e`, `X_K̄ ⟶ X_{K^sep}` being a
universal homeomorphism. -/
theorem hasTorsionCohomologicalDimensionLE_add_of_isAlgClosure {K : Type u} [Field K]
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosure K L] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a] {c e : ℕ}
    (hK : (Spec (.of K)).HasTorsionCohomologicalDimensionLE c)
    (hX : HasTorsionCohomologicalDimensionLE
      (pullback a (Spec.map (CommRingCat.ofHom (algebraMap K L)))) e) :
    X.HasTorsionCohomologicalDimensionLE (c + e) := fun F hF q hq ↦ by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian a
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian X := ⟨⟩
  refine Etale.subsingleton_H_of_isTorsion hF q fun G N hN hG ↦ ?_
  let Φ := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  let M := Φ.objPreimage G
  let eM : Φ.obj M ≅ G := Φ.objObjPreimageIso G
  have hM : (Φ.obj M).IsTorsion :=
    Etale.isTorsion_of_iso eM.symm (isTorsion_of_nsmul_id_eq_zero hN hG)
  refine Etale.subsingleton_H_of_rightDerived_lowerStar a G (c := c) (e := e)
    (fun q' hq' ↦ ?_) (fun p q' hp ↦ hK _ (isTorsion_of_nsmul_id_eq_zero hN ?_) p hp) q hq
  · refine IsZero.of_iso ?_ (((((a)_*[AddCommGrpCat.{u + 1}]).rightDerived q').mapIso eM).symm ≪≫
      (Etale.forget₂HigherDirectImageIso a M q').symm)
    exact Functor.map_isZero _
      (Etale.isZero_higherDirectImage_of_isAlgClosure L a hX M hM q' hq')
  · rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hG, Functor.map_zero]

end AlgebraicGeometry.Scheme
