/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructure
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportResidueBound
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportAmplitude
import WeilConjectures.NumberTheory.Padics.ResidueTorAmplitudeTest
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitudeResidue

/-! # Closed Tor transport for lifted purity coefficients -/
@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance 20000] CommRing.toRing
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local instance 20000] SymmetricCategory.toBraidedCategory sheafBraidedCategory
private theorem homology_bounds {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (L : _root_.DerivedCategory C) (a b : ℤ) :
    _root_.DerivedCategory.homologyConcentratedIn a b L ↔
      ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((_root_.DerivedCategory.homologyFunctor C i).obj L) := by
  constructor
  · rintro ⟨hlo, hhi⟩ i (hi | hi)
    · exact (_root_.DerivedCategory.isGE_iff L a).1 hlo i hi
    · exact (_root_.DerivedCategory.isLE_iff L b).1 hhi i hi
  · intro h
    exact ⟨(_root_.DerivedCategory.isGE_iff L a).2 (fun i hi ↦ h i (.inl hi)),
      (_root_.DerivedCategory.isLE_iff L b).2 (fun i hi ↦ h i (.inr hi))⟩

private theorem boundary_residue_test
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) (r : A) (hr : IsNilpotent r)
    [(Ideal.span {r}).IsMaximal] (a b : ℤ) (K : DerivedCategoryModule A T) :
    DerivedCategory.hasTorAmplitudeIn A T a b K ↔
      ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((_root_.DerivedCategory.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) i).obj
          (((derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
                (ModuleCat.of A (A ⧸ Ideal.span {r})))))) := by
  rw [DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn]
  change _root_.DerivedCategory.torAmplitudeIn _ a b K ↔ _
  refine (_root_.DerivedCategory.torAmplitudeIn_iff_homologyConcentratedIn_tensor_singleFunctor
    (C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (R := A) r hr
    (Sheaf.constantSheafQuotientIsoCokernel T.smallEtaleTopology r)
    (fun F _ _ _ f _ _ hY ↦
      Sheaf.mono_whiskerRight_of_smul_id_eq_zero r f hY F) a b K).trans ?_
  exact homology_bounds _ a b


private theorem boundary_closed_tor_from_residue_test
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ModuleCat.{u + 1} A) [Finite N]
    (htest : ∀ (S : Scheme.{u}) (x y : ℤ) (L : DerivedCategoryModule A S),
      DerivedCategory.isBoundedConstructible A S L →
      (DerivedCategory.hasTorAmplitudeIn A S x y L ↔
        ∀ q : ℤ, q < x ∨ y < q → IsZero
          ((_root_.DerivedCategory.homologyFunctor _ q).obj
            (((derivedTensor (ModuleCat.{u + 1} A) S).obj L).obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj
                ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N))))))
    {Z T U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (a b c : ℤ) (hc : 0 ≤ c)
    (hcd : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ), c < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj M))))
    (hcons : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ),
      Scheme.IsConstructibleEtaleModuleSheaf M →
      Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj M))))
    (K : DerivedCategoryModule A T)
    (hK : DerivedCategory.isBoundedConstructible A T K)
    (hTor : DerivedCategory.hasTorAmplitudeIn A T a b K) :
    DerivedCategory.isBoundedConstructible A Z
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K) ∧
    DerivedCategory.hasTorAmplitudeIn A Z a (b + c + 1)
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K) := by
  let Q := (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K
  obtain ⟨a₀, b₀, hab₀, hK₀⟩ := hK.2
  have hKbounds : _root_.DerivedCategory.homologyConcentratedIn a₀ b₀ K := by
    constructor
    · exact (_root_.DerivedCategory.isGE_iff K a₀).2 fun q hq ↦ hK₀ q (Or.inl hq)
    · exact (_root_.DerivedCategory.isLE_iff K b₀).2 fun q hq ↦ hK₀ q (Or.inr hq)
  obtain ⟨hQbounds, hQcons⟩ :=
    (closedImmersion_rightAdjoint_amplitude A i j hij a₀ b₀ c hc hcd).2
      hcons K hKbounds hK.1
  have hQ : DerivedCategory.isBoundedConstructible A Z Q := by
    refine ⟨hQcons, a₀, b₀ + c + 1, by omega, ?_⟩
    intro q hq
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff Q a₀).1 hQbounds.1 q hq
    · exact (_root_.DerivedCategory.isLE_iff Q (b₀ + c + 1)).1 hQbounds.2 q hq
  exact ⟨hQ, (htest Z a (b + c + 1) Q hQ).2
    (closedSupport_finiteTensor_vanishing A N i j hij a b c hc hcd K hTor)⟩


end AlgebraicGeometry.Etale

namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry.Etale
open AlgebraicGeometry.ProEtale.RetractedSupport

/-- Closed-support Tor transport for the actual lifted finite coefficient ring.
Source: closed-support residue test and amplitude theorem, with the quotient's
uniformizer transported through the canonical ULift ring equivalence.
Proof: the image of the uniformizer is nilpotent and generates a maximal ideal.
The residue criterion reduces Tor amplitude to cohomology after tensoring with
its finite residue module. The closed-support tensor theorem bounds this tensor,
and the criterion gives the required interval for the closed exceptional value.
(blueprint: lem-pur-boundary-closed-tor-transport). -/
theorem boundary_closed_tor_transport (P : PurityFiniteSetting.{u})
    {Z T U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (a b c : ℤ) (hc : 0 ≤ c)
    (hcd : ∀ (M : EtSheaves P U) (q : ℤ), c < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((Etale.lowerStar (Modules P) j).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M))))
    (hcons : ∀ (M : EtSheaves P U) (q : ℤ),
      Scheme.IsConstructibleEtaleModuleSheaf M →
      Scheme.IsConstructibleEtaleModuleSheaf
        ((DerivedCategory.homologyFunctor _ q).obj
          ((Etale.lowerStar (Modules P) j).rightDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj M))))
    (K : DerivedCategory (EtSheaves P T))
    (hK : Etale.DerivedCategory.isBoundedConstructible P.Coefficient T K)
    (hTor : Etale.DerivedCategory.hasTorAmplitudeIn P.Coefficient T a b K) :
    Etale.DerivedCategory.isBoundedConstructible P.Coefficient Z
      ((etClosed P i).obj K) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn P.Coefficient Z a (b + c + 1)
      ((etClosed P i).obj K) := by
  let l := P.coefficients.l
  let E := P.extension
  let n := P.level
  let r₀ : P.Ring := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
    (Padic.coefficientExtensionUniformizer l E)
  have hr₀ : IsNilpotent r₀ := by
    refine ⟨n, ?_⟩
    change (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
      (Padic.coefficientExtensionUniformizer l E)) ^ n = 0
    rw [← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.2
    rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hdvr := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hmax : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := hdvr.2.2.2.2.1
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have : (Ideal.span {Padic.coefficientExtensionUniformizer l E}).IsMaximal := hgen ▸ hmax
  have hm := Ideal.IsMaximal.map_of_surjective_of_ker_le
    (f := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n))
    (m := Ideal.span {Padic.coefficientExtensionUniformizer l E})
    Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]
      exact Ideal.pow_le_self (by have := P.level_pos; dsimp [n]; omega))
  have hm₀ : (Ideal.span {r₀}).IsMaximal := by
    simpa only [Ideal.map_span, Set.image_singleton, r₀, l, E, n,
      Ring, ringCommRing] using hm
  let e : P.Ring ≃+* P.Coefficient := ULift.ringEquiv.symm
  let r := e r₀
  have hr : IsNilpotent r := hr₀.map e
  have hm' : (Ideal.span {r}).IsMaximal := by
    have hmmap := hm₀.map_bijective e e.bijective
    simpa only [Ideal.map_span, Set.image_singleton] using hmmap
  let : (Ideal.span {r}).IsMaximal := hm'
  let N := ModuleCat.of P.Coefficient (P.Coefficient ⧸ Ideal.span {r})
  let : Finite N := Finite.of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  exact AlgebraicGeometry.Etale.boundary_closed_tor_from_residue_test
    P.Coefficient N (fun S x y L _ ↦
      AlgebraicGeometry.Etale.boundary_residue_test P.Coefficient S r hr x y L)
    i j hij a b c hc hcd hcons K hK hTor

end WeilConjectures.PurityFiniteSetting
