/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.PurityAffineChartBounds
/-!
# Uniform finite-stage exceptional inverse-image preservation

Source: Weil blueprint, `sec-six-functors/sk-prop-sf-rf-shriek-preservation`,
`thm-sf-preservation-class`, order 2085 (blueprint: thm-sf-preservation-class).

The functor is the constructible comparison-transported étale exceptional functor.
The conclusion gives the constructible analogues of preservation clauses (2) and (3)
of exceptional-adjoint admissibility. No unrestricted ambient adjoint or FullCD datum
is an input or an output. There is no assertion about integral or field coefficients.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Uniform cohomological and Tor bounds for the constructible exceptional inverse image.
The interval and Tor predicates are the published fixed-scalar module-sheaf
presentation, at the actual positive finite coefficient quotient. At these finite stages
bounded constructibility agrees with the intrinsic notion by the origin comparison.
The target dimension is zero for the empty scheme. The maximum includes empty source
charts and equals zero for an empty chart family.

Source: blueprint thm-sf-preservation-class, order 2085
(blueprint: thm-sf-preservation-class).

Proof:
1. Identify the functor with ν_X^* f^× Rν_{Y,*}, as in
   def-weil-exceptional-inverse-image. By lem-sf-proetale-constructible-origin every
   bounded constructible input, including every finite-Tor constructible input, is
   of étale origin. The adjunction of cor-sf-ambient-adjoint-discharge is relative
   to that class; no unrestricted ambient right adjoint is used.
2. Apply `sf_purity_affine_chart_bounds` (cor-pur-general-admissibility-datum)
   directly to the supplied C. Its interface accepts arbitrary chart families and
   forms `C.nonemptyCharts` internally. This concrete restriction keeps the target
   cover, reindexes exactly the nonempty source charts by `Fintype.equivFin`, and
   inherits their dimensions and closed presentations. Any covering chart containing
   a point survives, so the restricted family still covers; its source-nonemptiness
   follows from the index subtype. Its maximum D₀=`C.nonemptyCharts.maxDimension`
   is at most D=`C.maxDimension`: each restricted index selects an original index
   with the same dimension, bounded by the original finite supremum. Its constants are
   c_U=2(d_U+dim Y) and c₀=max_U(c_U+1+2(D₀-d_U)). It gives constructibility,
   finite-Tor membership, and both interval bounds [a-2D₀,b-2D₀+c₀].
3. Every summand in c₀ is 2D₀+2dim Y+1, so the upper endpoint is b+2dim Y+1.
   Since D₀≤D, widen the lower endpoint to a-2D. Vanishing outside an interval
   persists on widening, including after tensoring each degree-zero module sheaf.
   If X is empty, each object of its small pro-etale site has the empty covering;
   all module sheaves and hence all cohomology sheaves are zero. If Y is empty,
   X is empty too. These arguments apply even if empty charts inflate the supplied D.
   For an empty chart family D=0; for an empty target e=0, as stated.
4. Keep the same charts while varying every n≥1. None of d_U, D, or dim Y depends
   on n; the identical cancellation gives the same shifts at all finite stages.
   Thus the universal quantifier over n below uses one fixed C and the same bounds.
5. Read these as signed shifts c_f^-=-2D and c_f^+=2e+1 in preservation clauses
   (2) and (3). Finite-Tor membership is included explicitly. The stronger ambient
   clause (1), its unrestricted adjoint datum, and coefficient-comparison assertions
   at integral or field stages are neither assumed nor concluded. -/
theorem sf_preservation_class
    (F : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X Y : Scheme.{u}) [X.Over (Spec (.of F.k))] [Y.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of F.k))] [QuasiCompact (X ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of F.k))] [QuasiCompact (Y ↘ Spec (.of F.k))]
    [IsSeparated (Y ↘ Spec (.of F.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of F.k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification f) (C : SfAffineChartPresentation f) :
    ∀ (n : ℕ) (hn : 1 ≤ n) (a b : ℤ) (_hab : a ≤ b),
      (∀ L : _root_.DerivedCategory (Sheaf (ProEt.topology Y)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))),
        ProEtale.DerivedCategory.constructibleIn
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
          Y a b L →
        ProEtale.DerivedCategory.constructibleIn
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
          X (a - 2 * (C.maxDimension : ℤ)) (b + 2 * (sfDimension Y : ℤ) + 1)
          ((ProEtale.sfFiniteExceptionalInverseImage F.k l E n hn c).obj L)) ∧
      (∀ K : _root_.DerivedCategory (Sheaf (ProEt.topology Y)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))),
        ProEtale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) Y K →
        ProEtale.DerivedCategory.torAmplitudeIn
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) Y a b K →
        ProEtale.DerivedCategory.torAmplitudeIn
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
          X (a - 2 * (C.maxDimension : ℤ)) (b + 2 * (sfDimension Y : ℤ) + 1)
          ((ProEtale.sfFiniteExceptionalInverseImage F.k l E n hn c).obj K)) ∧
      (∀ K : _root_.DerivedCategory (Sheaf (ProEt.topology Y)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))),
        ProEtale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) Y K →
        ProEtale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X
          ((ProEtale.sfFiniteExceptionalInverseImage F.k l E n hn c).obj K)) := by
  classical
  have hD₀ : C.nonemptyCharts.maxDimension ≤ C.maxDimension := by
    apply Finset.sup_le
    intro ij _
    change C.dimension ij.1
      (((Fintype.equivFin {j : Fin (C.size ij.1) // Nonempty (C.source ij.1 j)}).symm
        ij.2).val) ≤ C.maxDimension
    let j := ((Fintype.equivFin
      {j : Fin (C.size ij.1) // Nonempty (C.source ij.1 j)}).symm ij.2).val
    have hj : C.dimension ij.1 j ≤ C.maxDimension := by
      simpa only [SfAffineChartPresentation.maxDimension] using
        (Finset.le_sup (f := fun ij : (i : Fin C.count) × Fin (C.size i) ↦
          C.dimension ij.1 ij.2)
          (s := Finset.univ) (b := Sigma.mk (ij.1 : Fin C.count) j) (Finset.mem_univ _))
    exact hj
  have hD : C.assemblyDimension ≤ C.maxDimension := by
    unfold SfAffineChartPresentation.assemblyDimension
    split_ifs
    · exact hD₀
    · exact Nat.zero_le _
  have hLower (a : ℤ) :
      a - 2 * (C.maxDimension : ℤ) ≤ a - 2 * (C.assemblyDimension : ℤ) := by
    have : (C.assemblyDimension : ℤ) ≤ (C.maxDimension : ℤ) := by exact_mod_cast hD
    omega
  have hUpper (b : ℤ) :
      b - 2 * (C.assemblyDimension : ℤ) + C.assemblyConstant ≤
        b + 2 * (sfDimension Y : ℤ) + 1 := by
    unfold SfAffineChartPresentation.assemblyDimension
      SfAffineChartPresentation.assemblyConstant
    split_ifs <;> omega
  intro n hn a b hab
  have h := sf_purity_affine_chart_bounds F l _hl E n hn X Y f c C a b hab
  refine ⟨?_, ?_, ?_⟩
  · intro L hL
    obtain ⟨hLc, hLi⟩ := h.1 L hL
    exact ⟨hLc, hLi.mono (hLower a) (hUpper b)⟩
  · intro K hK hKt
    exact ProEtale.DerivedCategory.torAmplitudeIn.mono (hLower a) (hUpper b)
      (h.2 K hK hKt).2
  · intro K hK
    obtain ⟨a', b', hKt⟩ := hK.2
    exact (sf_purity_affine_chart_bounds F l _hl E n hn X Y f c C
      (min a' b') b' (min_le_right _ _) |>.2 K hK
        (ProEtale.DerivedCategory.torAmplitudeIn.mono (min_le_left _ _) le_rfl hKt)).1

end AlgebraicGeometry.Scheme
