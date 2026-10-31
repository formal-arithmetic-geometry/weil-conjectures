/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.PoweredGeometricPullback
public import WeilConjectures.WeilSheaf.BaseChangeField.Geometric
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.DeligneLaumon.FrobeniusSaturation
import WeilConjectures.WeilSheaf.StalkFunctor
import WeilConjectures.DeligneLaumon.ClopenReturnSheetOpen
import WeilConjectures.DeligneLaumon.ClopenReturnSaturationEpi
import WeilConjectures.DeligneLaumon.LisseFrobeniusSaturation

/-! # Lifting lisse subobjects from a clopen return sheet

Source: the geometric-socle and Frobenius-return step of `sk-i-dl-general-real`.
(blueprint: lem-zl-clopen-return-subobject).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Endofunctor
open scoped AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.WeilSheaf

/-- Keep the categorical assembly abstract in both restriction functors, so kernel
checking does not unfold the native powered pullback. -/
private theorem subobject_of_lisse_saturation
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X C : Scheme.{u}} [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
    [LocallyOfFiniteType (X ↘ Spec (.of k₀))]
    [QuasiCompact (X ↘ Spec (.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (.of k₁))]
    (v : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    [IsOpenImmersion v] [IsClosedImmersion v]
    (Q : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₁ l C)
    [PreservesFiniteLimits Q]
    (R : WeilSheaf k₀ l X ⥤ WeilSheaf k₁ l C)
    (H : Q ⋙ IsoAlgebra.forget (frobeniusPullback k₁ l C) ≅
      IsoAlgebra.forget (frobeniusPullback k₀ l X) ⋙ (v)^*ᵃ[l])
    (I : R ⋙ (objectProperty k₁ l C).ι ≅ (objectProperty k₀ l X).ι ⋙ Q)
    (V : WeilSheaf k₀ l X)
    (G : WeilSheaf k₁ l C)
    (i : G ⟶ R.obj V) [Mono i.hom]
    (hU : ProEtale.IsAdicLisseSheaf
      (IsoAlgebra.saturation (frobeniusPullback k₀ l X) (v)_!ᵃ[l] (v)^*ᵃ[l]
        (ProEtale.adicOpenImmersionLowerShriekAdjunction l v) V.obj G.obj.carrier
        ((i.hom ≫ I.hom.app V).hom.f ≫
          H.hom.app V.obj)).carrier)
    (hep : Epi (IsoAlgebra.saturationUnit (frobeniusPullback k₀ l X) (v)_!ᵃ[l] (v)^*ᵃ[l]
        (ProEtale.adicOpenImmersionLowerShriekAdjunction l v) V.obj G.obj.carrier
        ((i.hom ≫ I.hom.app V).hom.f ≫
          H.hom.app V.obj))) :
    ∃ (U : WeilSheaf k₀ l X) (j : U ⟶ V), Mono j ∧ U.IsLisse ∧
      ∃ e : R.obj U ≅ G,
        R.map j = e.hom ≫ i := by
  have : IsLocallyNoetherian (X ↘ Spec (.of k₀)).geometricFiber :=
    LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure
  exact IsoAlgebra.fullSubcategory_saturation (frobeniusPullback k₀ l X)
    (v)_!ᵃ[l] (v)^*ᵃ[l] (ProEtale.adicOpenImmersionLowerShriekAdjunction l v)
    (frobeniusPullback k₁ l C) Q
    H (objectProperty k₀ l X)
    (objectProperty k₁ l C) R
    I V G i
    (fun W ↦ ProEtale.IsAdicLisseSheaf W.carrier) hU hU.isAdicConstructibleSheaf hep

/-- Apply the lissity theorem and the sheet calculation before instantiating the
abstract restriction functors. -/
private theorem lisse_subobject_of_saturation_epi
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X C : Scheme.{u}} [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
    [LocallyOfFiniteType (X ↘ Spec (.of k₀))]
    [QuasiCompact (X ↘ Spec (.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (.of k₁))]
    (v : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    [IsOpenImmersion v] [IsClosedImmersion v]
    (Q : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₁ l C)
    [PreservesFiniteLimits Q]
    (R : WeilSheaf k₀ l X ⥤ WeilSheaf k₁ l C)
    (H : Q ⋙ IsoAlgebra.forget (frobeniusPullback k₁ l C) ≅
      IsoAlgebra.forget (frobeniusPullback k₀ l X) ⋙ (v)^*ᵃ[l])
    (I : R ⋙ (objectProperty k₁ l C).ι ≅ (objectProperty k₀ l X).ι ⋙ Q)
    (V : WeilSheaf k₀ l X) (hV : V.IsLisse)
    (G : WeilSheaf k₁ l C) (hG : G.IsLisse)
    (i : G ⟶ R.obj V) [Mono i]
    (hep : ∀ i₀ : G.obj ⟶ Q.obj V.obj,
      Epi (IsoAlgebra.saturationUnit (frobeniusPullback k₀ l X) (v)_!ᵃ[l] (v)^*ᵃ[l]
        (ProEtale.adicOpenImmersionLowerShriekAdjunction l v) V.obj G.obj.carrier
        (i₀.hom.f ≫ H.hom.app V.obj))) :
    ∃ (U : WeilSheaf k₀ l X) (j : U ⟶ V), Mono j ∧ U.IsLisse ∧
      ∃ e : R.obj U ≅ G,
        R.map j = e.hom ≫ i := by
  have : IsLocallyNoetherian (X ↘ Spec (.of k₀)).geometricFiber :=
    LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure
  let F := frobeniusPullback k₀ l X
  let i₀ : G.obj ⟶ Q.obj V.obj := i.hom ≫ I.hom.app V
  let s : G.obj.carrier ⟶ (v)^*ᵃ[l].obj V.obj.carrier :=
    i₀.hom.f ≫ H.hom.app V.obj
  let adj := ProEtale.adicOpenImmersionLowerShriekAdjunction l v
  let U₀ := IsoAlgebra.saturation F (v)_!ᵃ[l] (v)^*ᵃ[l] adj V.obj G.obj.carrier s
  have : Mono i.hom := (objectProperty k₁ l C).ι.map_mono i
  have hep₀ := hep i₀
  have hU₀ : ProEtale.IsAdicLisseSheaf U₀.carrier :=
    isLisse_frobeniusSaturation (k := k₀) v V.obj G.obj.carrier s hV hG
  exact subobject_of_lisse_saturation v Q R
    H I V G i hU₀ hep₀

/-- A lisse subobject on the distinguished return sheet extends to the source.
Source: blueprint `sk-i-dl-general-real`, geometric-socle/Frobenius orbit step.
(blueprint: lem-zl-clopen-return-subobject).

Proof: Put r = [k₁:k₀]. The geometric fiber of the clopen image of C in X is
the disjoint union of r sheets, indexed by the k₀-embeddings of k₁ in its
algebraic closure. Geometric k₀-Frobenius cyclically permutes these sheets.
The chosen closure identification specifies v as the inclusion of one sheet;
the two projection equations characterize that inclusion by the pullback
universal property. On this sheet take the carrier of G and its injection i.
On the next sheet transport this injection using the inverse source Weil
isomorphism, and repeat through r sheets. The equation saying i is a morphism
of return Weil sheaves identifies the r-th transported injection with the
initial one using the return Weil isomorphism of G. Thus their direct sum is
a Frobenius-stable subsheaf of the source carrier on the clopen image of C.
Extend it by zero to the complementary clopen subset. The resulting carrier is
lisse: each piece is transported from the lisse sheaf G, and extension across
a clopen complement is locally either that sheaf or zero. Lissity implies
constructibility here, so the carrier and its induced Weil isomorphism define
a source Weil sheaf U and a monomorphism j into V. Restriction to the chosen
sheet gives the canonical isomorphism e and recovers i; this is the asserted
equation. The construction works also for zero G, for empty complement, and
for r=1; it uses neither simplicity nor nonvanishing of V. -/
theorem exists_lisse_subobject_clopen_return
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    [Algebra k₀ k₁] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X C : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [C.Over (Spec (CommRingCat.of k₁))]
    [Smooth (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₁))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₁))]
    [QuasiCompact (C ↘ Spec (CommRingCat.of k₁))]
    (c : C ⟶ X) [IsOpenImmersion c] [IsClosedImmersion c]
    (hc : c ≫ (X ↘ Spec (CommRingCat.of k₀)) =
      (C ↘ Spec (CommRingCat.of k₁)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)))
    (r : ℕ) (hr : Nat.card k₁ = Nat.card k₀ ^ r)
    (v : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    (hp : v ≫ (X ↘ Spec (.of k₀)).geometricFiberProj =
      (C ↘ Spec (.of k₁)).geometricFiberProj ≫ c)
    (hb : v ≫ (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure =
      (C ↘ Spec (.of k₁)).geometricFiberToAlgebraicClosure ≫
        Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k₁).symm.toRingHom))
    (hv : (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom ≫ v =
      v ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom)
    (V : WeilSheaf k₀ l X) (hV : V.IsLisse)
    (G : WeilSheaf k₁ l C) (hG : G.IsLisse)
    (i : G ⟶ (poweredGeometricPullback v r hv).obj V) [Mono i] :
    ∃ (U : WeilSheaf k₀ l X) (j : U ⟶ V), Mono j ∧ U.IsLisse ∧
      ∃ e : (poweredGeometricPullback v r hv).obj U ≅ G,
        (poweredGeometricPullback v r hv).map j = e.hom ≫ i := by
  have := isOpenImmersion_clopen_return_sheet (k₀ := k₀) (k₁ := k₁) c v hp hb
  have := isClosedImmersion_clopen_return_sheet (k₀ := k₀) (k₁ := k₁) c v hp hb
  exact lisse_subobject_of_saturation_epi v (poweredGeometricPullbackAll v r hv)
    (poweredGeometricPullback v r hv) (poweredPullbackAllCarrierIso v r hv)
    (poweredPullbackInclusionIso v r hv) V hV G hG i
    (fun i₀ ↦ epi_clopen_return_saturationUnit (k₀ := k₀) (k₁ := k₁)
      c hc r hr v hp hb hv V.obj G.obj i₀)

end AlgebraicGeometry.WeilSheaf
