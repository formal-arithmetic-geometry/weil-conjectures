/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfLocalizationData

import WeilConjectures.AlgebraicGeometry.SfPositiveFiniteLocalizationConstruction
import WeilConjectures.AlgebraicGeometry.SfIntegralLocalizationComparisons
import WeilConjectures.AlgebraicGeometry.SfIntegralDirectImageConstructible
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # SfIntegralLocalizationConstruction

Source: current blueprint, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-localization-all-stages.proof.md.
(blueprint: lem-sf-integral-localization-construction). -/

@[expose] public noncomputable section

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

private theorem directImageLimit
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : k))
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Y X : Scheme.{u}} (t : X ⟶ Spec (.of k)) (f : Y ⟶ X) [IsImmersion f]
    [LocallyOfFiniteType t] [QuasiCompact t]
    [LocallyOfFiniteType (f ≫ t)] [QuasiCompact (f ≫ t)]
    (O : SfOrdinaryIntegralComparison l E f)
    (G : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
    (e : G ⋙ (sfIntegralConstructible l E X).ι ≅
      (sfIntegralConstructible l E Y).ι ⋙ sfCompletedDerivedDirectImage l E f)
    (Q : sfIntegralConstructibleCategory l E Y) :
    ∃ hp : HasProduct (sfDirectImageTerm l E f Q.obj),
      ∃ L : @SfIntegralDirectImage l _ E _ _ _ Y X f Q.obj hp,
        Nonempty (L.obj ≅ (G.obj Q).obj) ∧
          ∀ n : ℕ, IsIso (@sfDirectImageReductionComparison l _ E _ _ _ Y X f Q.obj hp L n) := by
  let : X.Over (Spec (.of k)) := ⟨t⟩
  let : Y.Over (Spec (.of k)) := ⟨f ≫ t⟩
  let : f.IsOver (Spec (.of k)) := ⟨rfl⟩
  let : LocallyOfFiniteType (X ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType t)
  let : QuasiCompact (X ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact t)
  let : LocallyOfFiniteType (Y ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (f ≫ t))
  let : QuasiCompact (Y ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact (f ≫ t))
  let h := sfIntegralDirectImage_constructible k l hl E f Q.obj Q.property
  obtain ⟨hp, ⟨L⟩⟩ := h.1
  let := hp
  exact ⟨hp, L, ⟨(O.push Q.obj Q.property L).symm ≪≫ (e.app Q).symm⟩,
    fun n ↦ (O.push_reduction Q.obj Q.property L n).1⟩

private theorem amplitude_of_iso
    (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory Y A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude Y A K a b) : HasProEtaleTorAmplitude Y A L a b := by
  refine ⟨h.1, ?_⟩
  intro N P hN f hf hP M q hq
  obtain ⟨v⟩ := hN
  exact h.2 N P ⟨v ≪≫ e.symm⟩ f hf hP M q hq

private theorem integralInterval_of_reductions
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Y T : Scheme.{u}}
    (G : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E T)
    (f : ∀ n : ℕ, SfLocalizationFiniteCategory l E n Y ⥤
      SfLocalizationFiniteCategory l E n T)
    (e : ∀ n : ℕ, G ⋙ sfLocalizationConstructibleReduction l E T n ≅
      sfLocalizationConstructibleReduction l E Y n ⋙ f n)
    (K : sfIntegralConstructibleCategory l E Y) (a b b' : ℤ) (hab' : a ≤ b')
    (hf : ∀ (n : ℕ) (L : SfLocalizationFiniteCategory l E n Y),
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (n + 1)) L.obj a b →
        HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E (n + 1))
          ((f n).obj L).obj a b')
    (hK : SfLocalizationIntegralInterval l E Y K a b) :
    SfLocalizationIntegralInterval l E T (G.obj K) a b' := by
  refine ⟨hab', ?_⟩
  intro n
  exact amplitude_of_iso T (Padic.coefficientExtensionRing l E (n + 1))
    ((intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) T).ι.mapIso
      ((e n).app K)).symm a b'
    (hf n ((sfLocalizationConstructibleReduction l E Y n).obj K) (hK.2 n))

private theorem integralFiniteTor_of_interval
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Y T : Scheme.{u}}
    (G : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E T)
    (right : ℤ → ℤ)
    (hG : ∀ (K : sfIntegralConstructibleCategory l E Y) (a b : ℤ),
      SfLocalizationIntegralInterval l E Y K a b →
        SfLocalizationIntegralInterval l E T (G.obj K) a (right b))
    (K : sfIntegralConstructibleCategory l E Y)
    (hK : finiteTorConstructibleIntegral l E Y K.obj) :
    finiteTorConstructibleIntegral l E T (G.obj K).obj := by
  obtain ⟨a, b, hab, hred⟩ := hK.2
  exact ⟨(G.obj K).property, a, right b, hG K a b ⟨hab, hred⟩⟩

/-- Construct the finite and integral localization records before scalar localization.
Source: supported localization proof, (1), (2) and (3), finite coefficients and
integral reduction comparison; Finite Tor amplitude, residue criterion through Other stages
(blueprint: lem-sf-integral-localization-construction).

Proof: apply finiteKernelConstructibleLocalization to the positive quotients of the
valuation ring. Restrict its five functors and three adjunctions to their full
constructible subcategories. The closed counit and open counit are invertible;
closed-to-open orthogonality makes the supported boundary unique and natural.
For the finite exceptional comparison, first restrict to the bounded-below
constructible objects. The comparison-site equivalence transports the etale
exceptional adjunction to this category; its Hom bijection and the kernel
adjunction have the same left adjoint. Uniqueness of right adjoints gives the
counit-normalized comparison with the specified finite exceptional functor.
This is the argument of finiteExceptionalSiteNormalization, but its published
finite-field hypothesis must be removed here by the torsion site-comparison
theorem over the given field; it cannot be applied directly. For the integral
operations use sfIntegralOrdinaryRecollement_realization. Its ordinary-operation
comparisons supply the recorded completed direct images and completed pullbacks,
and its direct-image limit comparisons supply the closed_limit and open_limit fields.
Apply exceptionalReductionTransitionComparison to their normalized units and
counits. These comparisons give the closed, open, pullback and exceptional reduction
fields with the two displayed adjunction equations. For every finite level,
the residue criterion and exact monoidal immersion pullbacks preserve the two
pullback intervals. The closed image interval follows by applying closed pullback
to its residue tensor, whose restriction to the open complement is zero. These
are the assertions of immersion_residue_tor_intervals in intrinsic coefficient
coordinates; its published coefficient universe needs a realization comparison
before it applies here.
openImmersion_generalField_uniformBound gives N = 2d+c, also when U is empty;
proEtale_open_residue_tor_bound supplies the open interval. Apply
supported_tor_reduction_propagation to the supported triangles and these reductions
to obtain the exceptional interval and all uniform integral bounds. Preservation
of finite Tor follows by choosing an interval. No finite cohomological-dimension
hypothesis is needed to construct the operations; it is used only in the tor fields.
-/
theorem sfIntegralLocalizationConstruction
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : k))
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (t : X ⟶ Spec (.of k))
    [IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]
    {Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : Set.range j = (Set.range i)ᶜ) :
    Nonempty (SfIntegralLocalization l E k hl t i j) := by
  classical
  let F : ∀ n : ℕ, SfFiniteLocalization l E n k i j := fun n ↦
    Classical.choice (sfPositiveFiniteLocalizationConstruction k l hl E X t i j hij n)
  obtain ⟨O⟩ := sfIntegralOrdinaryRecollement_realization l E k hl t i j hij
  obtain ⟨C⟩ := sfIntegralLocalizationComparisons k l hl E X t i j hij F O
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType t
  have : TopologicalSpace.NoetherianSpace U :=
    j.isOpenEmbedding.isInducing.noetherianSpace
  refine ⟨{
    supported := C.supported
    closed_pull := C.closed_pull
    open_pull := C.open_pull
    closed_push := C.closed_push
    open_push := C.open_push
    closed_limit := directImageLimit k l hl E t i O.closed
      C.supported.iPush C.closed_push
    open_limit := directImageLimit k l hl E t j O.opened
      C.supported.jPush C.open_push
    finiteStages := F
    closed_reduction := C.closed_reduction
    open_reduction := C.open_reduction
    open_pull_reduction := C.open_pull_reduction
    exceptional_reduction := C.exceptional_reduction
    exceptional_counit_reduction := C.exceptional_counit_reduction
    open_unit_reduction := C.open_unit_reduction
    tor := ?_
  }⟩
  intro d c hd hc
  have hN : 0 ≤ 2 * (d : ℤ) + (c : ℤ) := by positivity
  have hf := fun n ↦ (F n).tor d c hd hc
  have hi (Q : sfIntegralConstructibleCategory l E Z) (a b : ℤ)
      (hQ : SfLocalizationIntegralInterval l E Z Q a b) :
      SfLocalizationIntegralInterval l E X (C.supported.iPush.obj Q) a b :=
    integralInterval_of_reductions l E C.supported.iPush
      (fun n ↦ (F n).supported.iPush) C.closed_reduction Q a b b hQ.1
      (fun n L hL ↦ (hf n).closed_interval L a b hL) hQ
  have hip (K : sfIntegralConstructibleCategory l E X) (a b : ℤ)
      (hK : SfLocalizationIntegralInterval l E X K a b) :
      SfLocalizationIntegralInterval l E Z (C.supported.iPull.obj K) a b :=
    integralInterval_of_reductions l E C.supported.iPull
      (fun n ↦ (F n).supported.iPull) C.closed_pull_reduction K a b b hK.1
      (fun n L hL ↦ (hf n).closed_pull_interval L a b hL) hK
  have hjp (K : sfIntegralConstructibleCategory l E X) (a b : ℤ)
      (hK : SfLocalizationIntegralInterval l E X K a b) :
      SfLocalizationIntegralInterval l E U (C.supported.jPull.obj K) a b :=
    integralInterval_of_reductions l E C.supported.jPull
      (fun n ↦ (F n).supported.jPull) C.open_pull_reduction K a b b hK.1
      (fun n L hL ↦ (hf n).open_pull_interval L a b hL) hK
  have hj (G : sfIntegralConstructibleCategory l E U) (a b : ℤ)
      (hG : SfLocalizationIntegralInterval l E U G a b) :
      SfLocalizationIntegralInterval l E X (C.supported.jPush.obj G)
        a (b + (2 * (d : ℤ) + (c : ℤ))) :=
    integralInterval_of_reductions l E C.supported.jPush
      (fun n ↦ (F n).supported.jPush) C.open_reduction G a b _
      (hG.1.trans (le_add_of_nonneg_right hN))
      (fun n L hL ↦ (hf n).open_interval L a b hL) hG
  have he (K : sfIntegralConstructibleCategory l E X) (a b : ℤ)
      (hK : SfLocalizationIntegralInterval l E X K a b) :
      SfLocalizationIntegralInterval l E Z (C.supported.exceptional.obj K)
        a (b + (2 * (d : ℤ) + (c : ℤ)) + 1) :=
    integralInterval_of_reductions l E C.supported.exceptional
      (fun n ↦ (F n).supported.exceptional) C.exceptional_reduction K a b _
      (hK.1.trans ((le_add_of_nonneg_right hN).trans (by omega)))
      (fun n L hL ↦ (hf n).exceptional_interval L a b hL) hK
  exact {
    open_preserves := integralFiniteTor_of_interval l E C.supported.jPush
      (fun b ↦ b + (2 * (d : ℤ) + (c : ℤ))) hj
    exceptional_preserves := integralFiniteTor_of_interval l E C.supported.exceptional
      (fun b ↦ b + (2 * (d : ℤ) + (c : ℤ)) + 1) he
    closed_preserves := integralFiniteTor_of_interval l E C.supported.iPush id hi
    closed_pull_preserves := integralFiniteTor_of_interval l E C.supported.iPull id hip
    open_pull_preserves := integralFiniteTor_of_interval l E C.supported.jPull id hjp
    open_interval := hj
    exceptional_interval := he
    closed_interval := hi
    closed_pull_interval := hip
    open_pull_interval := hjp
  }

end WeilConjectures
