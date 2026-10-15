/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimension
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing
import WeilConjectures.AlgebraicGeometry.Sites.LerayVanishing
import Sheaf.AlgebraicGeometry.Sites.FieldHigherDirectImageStalk

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

private lemma isZero_of_isZero_field_sheafFiber {K : Type u} [Field K]
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsZero (((pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F)) :
    IsZero F := by
  have : LocallySmall.{u + 1} (Spec (.of K)).Etale := locallySmall_max.{u + 1}
  let s := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have hs : ⋃ _ : PUnit.{u + 1}, Set.range s = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨PUnit.unit, default, Subsingleton.elim _ _⟩
  have hc := isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ
    (Spec (.of K)) (fun _ : PUnit.{u + 1} ↦ s) hs
  apply (IsZero.iff_id_eq_zero F).2
  apply (hc.jointlyFaithful AddCommGrpCat.{u + 1}).map_injective
  rintro ⟨_, ⟨i⟩⟩
  have hz : IsZero ((((pointSmallEtale s).ulift.{u + 1}).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj F) :=
    hF.of_iso (((pointSmallEtale s).uliftSheafFiberIso.{u + 1}
      AddCommGrpCat.{u + 1}).app F)
  let Φ := ((pointSmallEtale s).ulift.{u + 1}).sheafFiber (A := AddCommGrpCat.{u + 1})
  calc
    Φ.map (𝟙 F) = 𝟙 (Φ.obj F) := Φ.map_id F
    _ = 0 := hz.eq_of_src _ _
    _ = Φ.map 0 := (Φ.map_zero F F).symm

/-- Blueprint `lem-sc-cd-ground-field`: Descent of a geometric cohomological dimension bound.

Let `X` be a scheme of finite type over a field `K` (structure morphism `a`), and let `K̄` be an
algebraic closure of `K`. If `cd_tor(K) ≤ c` and `cd_tor(X_K̄) ≤ e`, then `cd_tor(X) ≤ c + e`.
The proof uses the Leray spectral sequence of `a`: the geometric stalk of `Rᵠa_* F` is
`Hᵠ(X_{K^sep}, F)`, which agrees with `Hᵠ(X_K̄, F)` since `X_K̄ ⟶ X_{K^sep}` is a universal
homeomorphism. -/
theorem hasTorsionCohomologicalDimensionLE_add_of_isAlgClosure {K : Type u} [Field K]
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosure K L] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a] {c e : ℕ}
    (hK : (Spec (.of K)).HasTorsionCohomologicalDimensionLE c)
    (hX : HasTorsionCohomologicalDimensionLE
      (pullback a (Spec.map (CommRingCat.ofHom (algebraMap K L)))) e) :
    X.HasTorsionCohomologicalDimensionLE (c + e) := by
  let := IsAlgClosure.isAlgClosed K (K := L)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian a
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  intro F hF n hn
  apply Etale.subsingleton_H_of_isTorsion hF n
  intro G N hN hG
  have hGt : G.IsTorsion := isTorsion_of_nsmul_id_eq_zero hN hG
  refine Etale.subsingleton_H_of_rightDerived_lowerStar a G ?_ ?_ n hn
  · intro q hq
    obtain ⟨d⟩ := Etale.nonempty_addEquiv_sheafFiber_rightDerived_lowerStar_of_isAlgClosure
      L a G hGt q
    have hz := hX _ (Etale.isTorsion_upperStar
      (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap K L)))) hGt) q hq
    apply isZero_of_isZero_field_sheafFiber L
    exact AddCommGrpCat.isZero_iff_subsingleton.2 d.toEquiv.subsingleton
  · intro p q hp
    apply hK _ _ p hp
    apply isTorsion_of_nsmul_id_eq_zero hN
    let R := (Etale.lowerStar AddCommGrpCat.{u + 1} a).rightDerived q
    calc
      N • 𝟙 (R.obj G) = R.map (N • 𝟙 G) := by rw [Functor.map_nsmul, R.map_id]
      _ = R.map 0 := congrArg R.map hG
      _ = 0 := R.map_zero _ _

end AlgebraicGeometry.Scheme
