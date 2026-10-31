/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.WeilMixedUpperBounds
public import WeilConjectures.AlgebraicGeometry.WeilIndSheafCategory
public import WeilConjectures.AlgebraicGeometry.SfConstructibleHeart
public import WeilConjectures.AlgebraicGeometry.SfWeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.AdicPunctualWeights
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion

import WeilConjectures.AlgebraicGeometry.ZlCanonicalImmersionPunctualSpectrum
import WeilConjectures.AlgebraicGeometry.ZlCanonicalImmersionCohomology
import WeilConjectures.AlgebraicGeometry.ZlWeilHeartLocalizationExact

/-! # Immersion pullback preserves upper Weil weights

Source: main-20261015, sec-deligne-laumon-general/sk-l-dl-general-excision,
lem-zl-morphism-open-closed-reduction.proof.md, Restriction paragraph
(blueprint: lem-zl-immersion-pullback-weight-preservation).

Both assertions use fixed pairs on the common-stage constructible category.
The pullback Weil structure is the normalized geometric-Frobenius square.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

private theorem pure_of_iso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
    [IsAlgClosure (Padic l) Qbar]
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (iota : Qbar →+* ℂ) (w : ℝ)
    {F G : sfCommonStageWeilSheaf D l hl Y₀ Qbar} (e : F ≅ G)
    (h : SfIsPunctuallyPureOfWeight D l hl Qbar Y₀ iota F w) :
    SfIsPunctuallyPureOfWeight D l hl Qbar Y₀ iota G w := by
  intro y α hα
  obtain ⟨L, K, ⟨a⟩, hK⟩ := hα
  exact h y α ⟨L, K, ⟨(ObjectProperty.ι _).mapIso e ≪≫ a⟩, hK⟩

private theorem mixed_of_iso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
    [IsAlgClosure (Padic l) Qbar]
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (iota : Qbar →+* ℂ) (w : ℝ)
    {F G : sfCommonStageWeilSheaf D l hl Y₀ Qbar} (e : F ≅ G)
    (h : SfIsMixedOfWeightsAtMost D l hl Qbar Y₀ iota F w) :
    SfIsMixedOfWeightsAtMost D l hl Qbar Y₀ iota G w := by
  obtain ⟨m, A, φ, h0, ⟨a⟩, hmono, hpure⟩ := h
  exact ⟨m, A, φ, h0, ⟨a ≪≫ e⟩, hmono, hpure⟩

/-- Pullback along a locally closed immersion preserves mixed upper bounds on
constructible Weil sheaves and on Weil complexes.

Source: main-20261015, sec-deligne-laumon-general/sk-l-dl-general-excision,
lem-zl-morphism-open-closed-reduction.proof.md, Restriction paragraph
(blueprint: lem-zl-immersion-pullback-weight-preservation).

Proof:
1. By lem-zl-immersion-weil-local-behavior(1), a closed point of the source has
closed image with the same residue field, and the canonical stalk isomorphism
intertwines local geometric Frobenius. It takes a nonzero eigenvector to a nonzero
eigenvector of the same eigenvalue. Thus def-weil-punctual-weights implies that
restriction preserves punctual purity with the same weight; zero stalks are harmless.
2. Apply the exact restriction functor of that lemma to a finite mixed filtration.
Its successive quotients are the restrictions of the original pure quotients.
A Weil isomorphism preserves eigenvalues: equivariance of its iterated Weil
structure follows by induction and lem-pod-integral-pullback-composition; the
point transports are natural by lem-weil-frobenius-point-transport-natural(2).
Consequently all quotient weights retain their original upper bound. Repeated
terms are allowed, including quotients killed by restriction and length zero.
3. For every integer a, apply the sheaf assertion with bound w+a to H^a(K).
The natural Weil isomorphism H^a(h-star K) ≅ h-star H^a(K) from the same immersion
lemma transports the filtration to H^a(h-star K). Its quotient eigenvalues agree
by Step 2. The defining degreewise condition of def-weil-complex-weights then
proves the complex assertion. -/
theorem zlImmersionPullbackWeightPreservation
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
    [IsAlgClosure (Padic l) Qbar] (iota : Qbar ≃+* ℂ)
    (W₀ X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom] [IsSeparated W₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (h₀ : W₀ ⟶ X₀) [IsImmersion h₀.left] (w : ℝ) :
    (∀ F : sfCommonStageWeilSheaf D l hl X₀ Qbar,
      SfIsMixedOfWeightsAtMost D l hl Qbar X₀ iota.toRingHom F w →
        SfIsMixedOfWeightsAtMost D l hl Qbar W₀ iota.toRingHom
          ((zlWeilPull D l hl Qbar h₀).obj F) w) ∧
    (∀ K : sfCommonStageWeilComplex D l hl X₀ Qbar,
      SfComplexIsMixedOfWeightsAtMost D l hl Qbar X₀ iota.toRingHom K w →
        SfComplexIsMixedOfWeightsAtMost D l hl Qbar W₀ iota.toRingHom
          ((IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Qbar h₀)).obj K) w) := by
  classical
  let H := zlWeilPull D l hl Qbar h₀
  obtain ⟨hlim, hcolim⟩ :=
    (zlWeilHeartLocalizationExact D l hl Qbar iota
      (X₀ := X₀) (U₀ := X₀) (Z₀ := X₀)).2.1 W₀ h₀
  have hc := zlCanonicalImmersionCohomology D l hl Qbar W₀ X₀ h₀
  have : PreservesFiniteLimits H := hlim
  have : PreservesFiniteColimits H := hcolim
  have : H.Additive := Functor.additive_of_preserves_binary_products H
  have hp (F : sfCommonStageWeilSheaf D l hl X₀ Qbar) (v : ℝ)
      (hF : SfIsPunctuallyPureOfWeight D l hl Qbar X₀ iota.toRingHom F v) :
      SfIsPunctuallyPureOfWeight D l hl Qbar W₀ iota.toRingHom (H.obj F) v := by
    intro z α hα
    obtain ⟨hx, hcard, hs⟩ :=
      zlCanonicalImmersionPunctualSpectrum D l hl Qbar W₀ X₀ h₀ z
    rw [hcard]
    exact hF ⟨h₀.left z.val, hx⟩ α (hs F α hα)
  have hm (F : sfCommonStageWeilSheaf D l hl X₀ Qbar) (b : ℝ)
      (hF : SfIsMixedOfWeightsAtMost D l hl Qbar X₀ iota.toRingHom F b) :
      SfIsMixedOfWeightsAtMost D l hl Qbar W₀ iota.toRingHom (H.obj F) b := by
    obtain ⟨m, A, φ, h0, ⟨a⟩, hmono, hpure⟩ := hF
    refine ⟨m, fun i ↦ H.obj (A i), fun i ↦ H.map (φ i), H.map_isZero h0,
      ⟨H.mapIso a⟩, ?_, ?_⟩
    · intro i
      have := hmono i
      infer_instance
    · intro i
      obtain ⟨v, hv, hA⟩ := hpure i
      exact ⟨v, hv, pure_of_iso D l hl Qbar W₀ iota.toRingHom v
        (PreservesCokernel.iso H (φ i)) (hp _ v hA)⟩
  refine ⟨fun F hF ↦ hm F w hF, ?_⟩
  intro K hK a
  obtain ⟨e⟩ := hc a K
  exact mixed_of_iso D l hl Qbar W₀ iota.toRingHom (w + (a : ℝ)) e.symm
    (hm _ (w + (a : ℝ)) (hK a))

end WeilConjectures
