/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FrobeniusSaturation
public import WeilConjectures.WeilSheaf.Category
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
import WeilConjectures.DeligneLaumon.LisseCountableImage
import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedOpenImmersion
import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteEtaleLisse
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

/-! # Lissity of the explicit Frobenius saturation

Source: the Frobenius-orbit sum in `sk-i-dl-general-real`.
(blueprint: lem-zl-lisse-frobenius-saturation).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Endofunctor
open scoped AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.WeilSheaf

/-- Saturating a lisse map extended by zero from a clopen immersion gives a lisse carrier.
Source: the Frobenius-orbit construction in `sk-i-dl-general-real`.
Proof: clopen extension by zero agrees with finite etale direct image and preserves
lissity. All positive and negative Frobenius translates are lisse. Forgetting the
Weil structure preserves images; apply the countable-image lemma to their sum.
(blueprint: lem-zl-lisse-frobenius-saturation). -/
theorem isLisse_frobeniusSaturation
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    {D : Scheme.{u}} (v : D ⟶ (X ↘ Spec (.of k)).geometricFiber)
    [IsOpenImmersion v] [IsClosedImmersion v]
    (V : ProEtaleWeilSheaf k l X) (M : ProEtale.AdicSheaf l D)
    (s : M ⟶ (v)^*ᵃ[l].obj V.carrier)
    (hV : ProEtale.IsAdicLisseSheaf V.carrier) (hM : ProEtale.IsAdicLisseSheaf M) :
    ProEtale.IsAdicLisseSheaf
      (IsoAlgebra.saturation (frobeniusPullback k l X) (v)_!ᵃ[l] (v)^*ᵃ[l]
        (ProEtale.adicOpenImmersionLowerShriekAdjunction l v) V M s).carrier := by
  let F := frobeniusPullback k l X
  let S := (v)_!ᵃ[l].obj M
  have hS : ProEtale.IsAdicLisseSheaf S := by
    have := ProEtale.isIso_adicOpenImmersionLowerShriekToLowerStar_of_isClosed_range
      l v v.isClosedEmbedding.isClosed_range
    exact (hM.lowerStar_of_finite_etale v).of_iso
      (asIso ((ProEtale.adicOpenImmersionLowerShriekToLowerStar l v).app M)).symm
  have hF (T : ProEtale.AdicSheaf l (X ↘ Spec (.of k)).geometricFiber)
      (hT : ProEtale.IsAdicLisseSheaf T) : ProEtale.IsAdicLisseSheaf (F.obj T) :=
    hT.lowerStar_of_finite_etale _
  have hI (T : ProEtale.AdicSheaf l (X ↘ Spec (.of k)).geometricFiber)
      (hT : ProEtale.IsAdicLisseSheaf T) : ProEtale.IsAdicLisseSheaf (F.inv.obj T) := by
    let e := Iso.isoInverseOfIsoFunctor
      (G := F.asEquivalence)
      (G' := ProEtale.adicLowerStarEquivalence l
        (X ↘ Spec (.of k)).geometricGaloisFrobenius.symm) (Iso.refl _)
    exact (hT.lowerStar_of_finite_etale
      (X ↘ Spec (.of k)).geometricGaloisFrobenius.hom).of_iso (e.app T).symm
  have hpos (n : ℕ) : ProEtale.IsAdicLisseSheaf (IsoAlgebra.Free.posObj F S n) := by
    induction n with
    | zero => exact hS
    | succ n hn => exact hF _ hn
  have hneg (n : ℕ) : ProEtale.IsAdicLisseSheaf (IsoAlgebra.Free.negObj F S n) := by
    induction n with
    | zero => exact hI _ hS
    | succ n hn => exact hI _ hn
  have hA (n : ℤ) : ProEtale.IsAdicLisseSheaf (IsoAlgebra.Free.obj F S n) := by
    cases n with
    | ofNat n => exact hpos n
    | negSucc n => exact hneg n
  let t := (ProEtale.adicOpenImmersionLowerShriekAdjunction l v).homEquiv M V.carrier
  have h := ProEtale.isAdicLisseSheaf_image_sigma (IsoAlgebra.Free.obj F S) V.carrier
    (IsoAlgebra.Free.hom V (t.symm s)) hA hV
  exact h.of_iso (PreservesImage.iso (IsoAlgebra.forget F)
    (IsoAlgebra.saturationMap F (v)_!ᵃ[l] (v)^*ᵃ[l]
      (ProEtale.adicOpenImmersionLowerShriekAdjunction l v) V M s))

end AlgebraicGeometry.WeilSheaf
