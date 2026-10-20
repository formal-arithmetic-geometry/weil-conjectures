/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange

public import Sheaf.AlgebraicGeometry.InvertibleOrdersColimit
import Sheaf.AlgebraicGeometry.AbelianExchangeFilteredColimit
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion

/-! Filtered-colimit passage for the torsion exchange map.
Source: Stacks Project, Tag 073E and blueprint `lem-kun-invertible-orders-colimit`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- Exchange for every bounded invertible-order torsion subsheaf implies exchange for the
whole torsion sheaf. The proof uses the canonical filtered colimit of those subsheaves,
exact inverse image, filtered-colimit preservation of higher direct images, and naturality
of the derived exchange transformation.
Source: Stacks Project, Tag 073E and Tag 0F1I
(blueprint: lem-kun-torsion-exchange-filtered-passage).

Proof: the allowable positive integers form a filtered category under divisibility:
1 is an index and the product is a common upper bound. The stalk hypothesis makes
every stalk torsion, hence F is torsion. The invertible-order colimit theorem identifies
the canonical colimit of the kernels F[n] with F. Each exchange on F[n] is invertible
by the hypothesis. Filtered-colimit exchange makes the exchange on their colimit
invertible; naturality along the canonical comparison isomorphism gives the result.
-/
theorem isIso_exchange_of_isIso_torsion_pieces
    {K : Type u} [Field K] {X S' T : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f]
    [S'.Over (Spec (.of K))] [T.Over (Spec (.of K))]
    (g : T ⟶ S') [g.IsOver (Spec (.of K))]
    [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionOfInvertibleOrder K (Over.mk (T ↘ Spec (.of K))) F)
    (hpieces : ∀ (n : ℕ) (_hn : n ∈ invertibleTorsionOrders K),
      IsIso (((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1}
        (CommSq.mk (pullback.condition (f := pullback.snd f (S' ↘ Spec (.of K)))
          (g := g)).symm)).app
        ((DerivedCategory.singleFunctor _ 0).obj
          (etaleNTorsion F n))))) :
    IsIso (((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1}
      (CommSq.mk (pullback.condition (f := pullback.snd f (S' ↘ Spec (.of K)))
        (g := g)).symm)).app
      ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  let J := ObjectProperty.FullSubcategory
    (fun n : PNat.DvdOrder ↦ n.val ∈ invertibleTorsionOrders K)
  have : Nonempty J := ⟨⟨⟨1, by decide⟩, by
    exact ⟨by decide, by simp [PNat.DvdOrder.val, PNat.DvdOrder.toPNat]⟩⟩⟩
  have : IsFilteredOrEmpty J := {
    cocone_objs := fun n m ↦ by
      let k : J := ⟨⟨n.obj.val * m.obj.val,
        Nat.mul_pos n.property.1 m.property.1⟩,
        ⟨Nat.mul_pos n.property.1 m.property.1, by
          change ((n.obj.val * m.obj.val : ℕ) : K) ≠ 0
          rw [Nat.cast_mul]
          exact mul_ne_zero n.property.2 m.property.2⟩⟩
      refine ⟨k, ?_, ?_, trivial⟩
      · exact ObjectProperty.homMk (homOfLE (show n.obj.val ∣ k.obj.val from dvd_mul_right _ _))
      · exact ObjectProperty.homMk (homOfLE (show m.obj.val ∣ k.obj.val from dvd_mul_left _ _))
    cocone_maps := fun n m α β ↦ ⟨m, 𝟙 _, by rfl⟩ }
  have : IsFiltered J := {}
  have ht : F.IsTorsion := by
    apply (Scheme.isTorsion_iff_isAddTorsion_sheafFiber F).mpr
    intro Ω _ _ s x
    obtain ⟨n, hn, hx⟩ := hF Ω s x
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn.1, hx⟩
  have hc := (Scheme.isTorsionEtaleSheafOfFieldInvertibleOrder_iff_isIso_comparison
    K F ht).mp hF
  let M := Scheme.fieldInvertibleTorsionDiagram K F
  have hM : ∀ j : J, IsIso ((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1}
      (CommSq.mk (pullback.condition (f := pullback.snd f (S' ↘ Spec (.of K)))
        (g := g)).symm)).app ((DerivedCategory.singleFunctor _ 0).obj (M.obj j))) :=
    fun j ↦ hpieces j.obj.val j.property
  have hcol := isIso_exactExchange_colimit
    (IsPullback.of_hasPullback (pullback.snd f (S' ↘ Spec (.of K))) g).flip J M hM
  exact (NatTrans.isIso_app_iff_of_iso
    (Functor.whiskerLeft (DerivedCategory.singleFunctor _ 0)
      (exactDerivedBaseChangeMap AddCommGrpCat.{u + 1}
        (CommSq.mk (pullback.condition (f := pullback.snd f (S' ↘ Spec (.of K)))
          (g := g)).symm)))
    (asIso (Scheme.fieldInvertibleTorsionComparison K F))).mp hcol

end AlgebraicGeometry.Etale
