/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldScalarNormalizedData
import WeilConjectures.AlgebraicGeometry.FieldScalarSingleInclusion
import WeilConjectures.AlgebraicGeometry.FieldScalarIdentityComparison
import WeilConjectures.AlgebraicGeometry.FieldScalarSuccessiveComparison
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Field scalar normalized systems

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md, paragraph (1)
(blueprint: lem-sp-field-scalar-normalized-systems).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale.FieldScalar

private theorem cofinal_ramification (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    ∃ (h : ℕ) (a : (Padic.coefficientExtensionIntegers l E)ˣ), 0 < h ∧
      (l : Padic.coefficientExtensionIntegers l E) =
        a * Padic.coefficientExtensionUniformizer l E ^ h ∧
      ∀ n : ℕ, spEllIdeal l E ^ n =
        Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
          Set (Padic.coefficientExtensionIntegers l E)) ^ (h * n) := by
  have hfactor : ∃ e : ℕ, 1 ≤ e ∧
      ∃ v : (Padic.coefficientExtensionIntegers l E)ˣ,
        (l : Padic.coefficientExtensionIntegers l E) =
          v * Padic.coefficientExtensionUniformizer l E ^ e := by
    let O := Padic.coefficientExtensionIntegers l E
    let π := Padic.coefficientExtensionUniformizer l E
    have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
    let : IsDiscreteValuationRing O := h.2.2.2.2.2.2.2.1
    have hgen : Ideal.span ({π} : Set O) = Padic.coefficientExtensionMaximalIdeal l E :=
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    have hm : Padic.coefficientExtensionMaximalIdeal l E = IsLocalRing.maximalIdeal O :=
      IsLocalRing.eq_maximalIdeal h.2.2.2.2.1
    have hπ : Irreducible π :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 (hm.symm.trans hgen.symm)
    have hl0 : (l : O) ≠ 0 := by
      intro heq
      have heq' : (l : E) = 0 := congrArg (fun x : O ↦ (x : E)) heq
      have hq : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
      exact hq ((algebraMap ℚ_[l] E).injective (by simpa only [map_natCast, map_zero]
        using heq'))
    obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hπ
    refine ⟨e, ?_, v, hv⟩
    have hval : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
      have hext := spectralNorm_extends (K := ℚ_[l]) (L := E) (l : ℚ_[l])
      change spectralNorm ℚ_[l] E (l : E) < 1
      simpa only [map_natCast] using hext.trans_lt (Padic.norm_p_lt_one (p := l))
    have hnu : ¬ IsUnit (l : O) := by
      intro hu
      exact (ne_of_lt hval) ((h.2.2.1 (l : O)).mp hu)
    by_contra he
    have he0 : e = 0 := by omega
    apply hnu
    rw [hv, he0, pow_zero, mul_one]
    exact v.isUnit
  obtain ⟨e, hepos, v, hv⟩ := hfactor
  refine ⟨e, v, hepos, hv, ?_⟩
  intro n
  unfold spEllIdeal
  rw [hv, Ideal.span_singleton_mul_left_unit v.isUnit, Ideal.span_singleton_pow,
    ← pow_mul, ← Ideal.span_singleton_pow]

/-- Exact field scalar extension preserves normalized constructible towers, every
common cohomological and Tor interval, and reduction of every integral derived object.
The comparison is an isomorphism of entire ordinary derived strict systems, with the
multiplication and insertion-of-one formulas before localization and the identity and
successive-field-extension squares. Ramification is included via the displayed cofinal
uniformizer powers.
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md, paragraph (1)
(blueprint: lem-sp-field-scalar-normalized-systems).

Proof:
1. The ring O_F is finite free over O_E. Choose an integral basis. Its reductions give
bases modulo every ell power, since quotient commutes with finite direct sums. The
same basis gives the completed coefficient sheaf basis. In a DVR ell is a unit times
a positive power of the uniformizer; taking powers gives precisely the cofinal ideals.
2. Define extension and restriction on whole strict systems by sheafified tensor and
restriction along the quotient inclusions. Transitions send x tensor b to t(x) tensor
q(b). The one basis identifies the restricted extension functor with the same finite
sum, including every transition and morphism. Consequently extension is exact.
3. Termwise extension preserves quasi-isomorphisms and descends to the ordinary
unbounded derived category, with its localization counit invertible on every complex.
Finite free scalar extension preserves each common cohomological and Tor interval.
Tensor associativity respects the normalization maps. Constructibility is preserved
by finite scalar extension on a common finite stratification. Thus N_A maps to N_B.
4. Resolve the integral object by a flat-term K-flat complex P. Scalar extension
preserves such representatives. In every degree and quotient level multiplication
identifies the two double tensors, with inverse insertion of 1. Tensor balancing
and sheafification verify both inverse equations, all transitions and all chain maps.
5. Localize these entire strict tower complexes, using the K-flat resolving class.
The universal counits give the displayed representative equation, hence a natural
isomorphism on the whole derived category, including morphisms represented by roofs.
6. Identity multiplication gives the unitors. For three fields both composites on
a tensor generator multiply the same three factors. This proves the ordinary square;
localization and the counit equations prove the derived square. Choose these canonical
comparisons simultaneously; their construction does not depend on a choice of basis. -/
theorem field_scalar_normalized_systems (P : WeilConjectures.PurityFiniteSetting.{u})
    (X Y : Scheme.{u}) [X.Over (Spec (CommRingCat.of P.field.k))]
    [Y.Over (Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d f] [IsSeparated f] :
    ∀ T : Scheme.{u}, (T = X ∨ T = Y) → Nonempty (Family P.coefficients.l T) := by
  classical
  intro T hT
  have hX : IsNoetherian X := by
    let := LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ Spec (CommRingCat.of P.field.k))
    let := QuasiCompact.compactSpace_of_compactSpace
      (X ↘ Spec (CommRingCat.of P.field.k))
    exact ⟨⟩
  have hY : IsNoetherian Y := by
    let := LocallyOfFiniteType.isLocallyNoetherian
      (Y ↘ Spec (CommRingCat.of P.field.k))
    let := QuasiCompact.compactSpace_of_compactSpace
      (Y ↘ Spec (CommRingCat.of P.field.k))
    exact ⟨⟩
  let : IsNoetherian T := hT.elim (fun h ↦ h ▸ hX) (fun h ↦ h ▸ hY)
  refine ⟨{
    data := fun E F _ _ _ _ _ _ ι DA DB RA RB ↦
      Classical.choice (field_scalar_single_inclusion P.coefficients.l E F ι T DA DB RA RB)
    identity := fun E _ _ _ DA RA ↦ field_scalar_identity_comparison _
    successive := fun E F L _ _ _ _ _ _ _ _ _ ι κ DA DB DC RA RB RC ↦
      field_scalar_successive_comparison _ _ _
    cofinal := fun E _ _ _ ↦ cofinal_ramification P.coefficients.l E
  }⟩

end AlgebraicGeometry.ProEtale.FieldScalar
