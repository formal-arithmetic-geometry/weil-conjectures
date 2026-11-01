/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunctionMaps
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace

/-! # Native finite Kummer exponent compatibility

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, final paragraph, and
lem-pur-vector-integration-site-comparison, exponent independence.
(blueprint: lem-route-coordinate-line-conjugate-exponents).

The displayed maps use ordinary finite Kummer lines and their exact comparison
pullbacks. The affine-chart coordinate is removed using the existing canonical
Tate inverse-image comparison. All exponents below are indexed by predecessors:
`r` denotes the positive exponent `r + 1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.NativeCoordinateLine

open AffineLinePurity VectorIntegrationSite

variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- The ordinary finite power comparison rho_{b,a}, normalized on pure root tensors.
The existing unique comparison in twistCompatibility is characterized by
IsFiniteTateEtaleTransition: u tensor x maps to u^(ell^(b-a)) tensor x.
Source: def-coefficient-twists-detailed and vector-integration exponent comparison
(blueprint: lem-route-coordinate-line-conjugate-exponents). -/
def powerComparison (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    (a b : ℕ) (hab : a ≤ b)
    (ha : ((P.coefficients.l ^ (a + 1) : ℕ) : Ring P) = 0)
    (hb : ((P.coefficients.l ^ (b + 1) : ℕ) : Ring P) = 0) :
    Scheme.finiteEtaleTateTwist T (P.coefficients.l ^ (b + 1)) (Ring P) hb 1 ≅
      Scheme.finiteEtaleTateTwist T (P.coefficients.l ^ (a + 1)) (Ring P) ha 1 :=
  ((twistCompatibility P.coefficients.l P.extension (P.level - 1)).2.2
    T (primeUnit P T aT) a b hab ha hb 1).exists.choose

/-- The native transition tau_{s0,s1}: inverse rho_{M,s0}, then rho_{M,s1}.
Here M=max(s0,s1); predecessor indexing commutes with maximum. No coefficient
extension or reduction is taken in this construction.
Source: the common-exponent transition in the node's statement
(blueprint: lem-route-coordinate-line-conjugate-exponents). -/
def transition (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    (r s : ℕ)
    (hr : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hs : ((P.coefficients.l ^ (s + 1) : ℕ) : Ring P) = 0) :
    Scheme.finiteEtaleTateTwist T (P.coefficients.l ^ (r + 1)) (Ring P) hr 1 ≅
      Scheme.finiteEtaleTateTwist T (P.coefficients.l ^ (s + 1)) (Ring P) hs 1 :=
  (powerComparison P T aT r (max r s) (Nat.le_max_left r s) hr
    ((Nat.cast_pow P.coefficients.l (max r s + 1)).trans
      (pow_eq_zero_of_le (Nat.add_le_add_right (Nat.le_max_left r s) 1)
        ((Nat.cast_pow P.coefficients.l (r + 1)).symm.trans hr)))).symm ≪≫
  powerComparison P T aT s (max r s) (Nat.le_max_right r s) hs
    ((Nat.cast_pow P.coefficients.l (max r s + 1)).trans
      (pow_eq_zero_of_le (Nat.add_le_add_right (Nat.le_max_left r s) 1)
        ((Nat.cast_pow P.coefficients.l (r + 1)).symm.trans hr)))

/-- The native compared shifted Kummer coefficient C_T B_{s,T}[2].
Source: the definition of Phi_s in the node
(blueprint: lem-route-coordinate-line-conjugate-exponents). -/
abbrev line (T : Scheme.{u}) (r : ℕ)
    (hr : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0) :=
  (VectorIntegrationSite.comparison (Ring P) T).obj
    ((Etale.ordinaryFiniteLine (Ring P) (P.coefficients.l ^ (r + 1)) hr T)⟦(2 : ℤ)⟧)

/-- The existing affine-chart coordinate identified with C_X B_{s,X}[2].
Source: the specified Tate inverse-image comparison for the standard chart
(blueprint: lem-route-coordinate-line-conjugate-exponents). -/
def chartComparison (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    (r : ℕ) (hr : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0) :
    coefficient P.coefficients.l P.extension (P.level - 1) T r hr ≅
      line P (AffineSpace PUnit.{u + 1} T) r hr :=
  eqToIso (coefficient_comparison_eq P.coefficients.l P.extension (P.level - 1) T r hr) ≪≫
    (VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).mapIso
      (eqToIso (etaleCoefficient_eq P.coefficients.l P.extension (P.level - 1) T r hr)) ≪≫
    comparedLinePullback (Ring P) (P.coefficients.l ^ (r + 1))
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hr
      (ProjectiveLine.affineChart T)
      (by simpa only [Nat.cast_pow] using
        (primeUnit P (ProjectiveLine T) ((ProjectiveLine T ↘ T) ≫ aT)).pow (r + 1))

/-- Phi_s in native Kummer coordinates. The existing affineLinePurityComparison
is the specified normalized projection-formula/integration transpose in chart
coordinates. Tensoring the inverse canonical chart comparison expresses it on
C_X B_{s,X}[2]. Equivalently this is gamma after tensoring alpha_s[2]; no
arbitrary purity isomorphism is selected.
Source: the affine-line comparison display and the definition of Phi_s
(blueprint: lem-route-coordinate-line-conjugate-exponents). -/
def conjugate (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (r : ℕ) (hr : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
    (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) T Ke)
    (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj) :
    projectionSourceObject (Ring P) (AffineSpace PUnit.{u + 1} T ↘ T)
      (line P (AffineSpace PUnit.{u + 1} T) r hr) K.obj ⟶
      (sfFiniteExceptionalAt (Ring P) (affineTraceLineCompactification T)).obj K.obj :=
  (CoordinateLine.tensorCoefficientIso (Ring P) T _ _
    (chartComparison P T aT r hr).symm K.obj).hom ≫
    affineLinePurityComparison P T r hr aT K Ke hKe eK

/-- Tensoring coefficient isomorphisms is functorial for composition.
Proof: unfold `tensorCoefficientIso`; it is `Functor.mapIso` of a fixed functor. -/
private theorem tensorCoefficientIso_trans (T : Scheme.{u})
    (W W' W'' : DerivedCategory
      (Sheaf (Scheme.ProEt.topology (AffineSpace PUnit.{u + 1} T)) (ModuleCat.{u + 1} (Ring P))))
    (e : W ≅ W') (f : W' ≅ W'')
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P)))) :
    CoordinateLine.tensorCoefficientIso (Ring P) T W W'' (e ≪≫ f) K =
      CoordinateLine.tensorCoefficientIso (Ring P) T W W' e K ≪≫
        CoordinateLine.tensorCoefficientIso (Ring P) T W' W'' f K := by
  unfold CoordinateLine.tensorCoefficientIso
  rw [Functor.mapIso_trans]
  with_unfolding_all rfl

/-- Tensoring coefficient isomorphisms commutes with inverses.
Proof: unfold `tensorCoefficientIso`; it is `Functor.mapIso` of a fixed functor. -/
private theorem tensorCoefficientIso_symm (T : Scheme.{u})
    (W W' : DerivedCategory
      (Sheaf (Scheme.ProEt.topology (AffineSpace PUnit.{u + 1} T)) (ModuleCat.{u + 1} (Ring P))))
    (e : W ≅ W')
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P)))) :
    CoordinateLine.tensorCoefficientIso (Ring P) T W' W e.symm K =
      (CoordinateLine.tensorCoefficientIso (Ring P) T W W' e K).symm := by
  unfold CoordinateLine.tensorCoefficientIso
  rw [Functor.mapIso_symm]
  with_unfolding_all rfl

/-- The coefficient-category cancellation needed to compare two common exponent maps.
Source: the finite Tate transition normalization in the proof plan.
Proof: `transition` is `rho_{M,r}⁻¹ ≫ rho_{M,s}` with `M = max r s`, where each
`rho` is the map chosen from the ordered clause of `twistCompatibility`; that clause
gives `C(rho_{M,a}) ≫ tw_a = tw_M` for `a = r, s`. Hence
`C(transition) ≫ tw_s = C(rho_{M,r})⁻¹ ≫ tw_M = tw_r`. `Ring P` is by definition
the finite Tate coefficient ring, so no change of coefficients occurs.
(blueprint: lem-route-native-transition-compatibility). -/
theorem native_transition_compatibility (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) (r s : ℕ)
    (hr : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hs : ((P.coefficients.l ^ (s + 1) : ℕ) : Ring P) = 0) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Ring P))
      (AffineSpace PUnit.{u + 1} T)).mapIso
        (transition P (AffineSpace PUnit.{u + 1} T)
          ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT) r s hr hs) ≪≫
      twistComparison P.coefficients.l P.extension (P.level - 1)
        (AffineSpace PUnit.{u + 1} T)
        (primeUnit P (AffineSpace PUnit.{u + 1} T)
          ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT)) s hs 1 =
    twistComparison P.coefficients.l P.extension (P.level - 1)
      (AffineSpace PUnit.{u + 1} T)
      (primeUnit P (AffineSpace PUnit.{u + 1} T)
        ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT)) r hr 1 := by
  have hM : ((P.coefficients.l ^ (max r s + 1) : ℕ) : Ring P) = 0 :=
    (Nat.cast_pow P.coefficients.l (max r s + 1)).trans
      (pow_eq_zero_of_le (Nat.add_le_add_right (Nat.le_max_left r s) 1)
        ((Nat.cast_pow P.coefficients.l (r + 1)).symm.trans hr))
  have h1 := ((twistCompatibility P.coefficients.l P.extension (P.level - 1)).2.2
    (AffineSpace PUnit.{u + 1} T)
    (primeUnit P (AffineSpace PUnit.{u + 1} T) ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT))
    r (max r s) (Nat.le_max_left r s) hr hM 1).exists.choose_spec.2
  have h2 := ((twistCompatibility P.coefficients.l P.extension (P.level - 1)).2.2
    (AffineSpace PUnit.{u + 1} T)
    (primeUnit P (AffineSpace PUnit.{u + 1} T) ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT))
    s (max r s) (Nat.le_max_right r s) hs hM 1).exists.choose_spec.2
  unfold transition powerComparison
  rw [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc, h2]
  exact (congrArg (fun e => _ ≪≫ e) h1.symm).trans (Iso.symm_self_id_assoc _ _)

/-- The chart-coordinate bridge after the normalized coefficient transition.
Source: the canonical affine-chart Tate inverse-image comparison.
Proof: unfolding `coefficientTwistIso`, `twistPullbackComparison` and
`chartComparison` gives `coefficientTwistIso_t = chartComparison_t ≫ twistDerived_t`
for `t = r, s`, so the left side is `twistDerived_r ≫ twistDerived_s⁻¹`. Unfold
`twistDerived` (commShift of the comparison functor, then the single-functor
comparison, then `twistComparison`). Rewrite `tw_r` by `htrans`, then move the
transition across by naturality of `commShiftIso` and of
`mapDerivedCategorySingleFunctor`. The remaining terms cancel.
(blueprint: lem-route-native-chart-compatibility). -/
theorem native_chart_compatibility (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) (r s : ℕ)
    (hr : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hs : ((P.coefficients.l ^ (s + 1) : ℕ) : Ring P) = 0)
    (hP : IsUnit (P.coefficients.l : Γ(ProjectiveLine T, ⊤)))
    (hX : IsUnit (P.coefficients.l : Γ(AffineSpace PUnit.{u + 1} T, ⊤)))
    (htrans :
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Ring P))
        (AffineSpace PUnit.{u + 1} T)).mapIso
          (transition P (AffineSpace PUnit.{u + 1} T)
            ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT) r s hr hs) ≪≫
        twistComparison P.coefficients.l P.extension (P.level - 1)
          (AffineSpace PUnit.{u + 1} T)
          (primeUnit P (AffineSpace PUnit.{u + 1} T)
            ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT)) s hs 1 =
      twistComparison P.coefficients.l P.extension (P.level - 1)
        (AffineSpace PUnit.{u + 1} T)
        (primeUnit P (AffineSpace PUnit.{u + 1} T)
          ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT)) r hr 1) :
    (chartComparison P T aT r hr).symm ≪≫
        (coefficientTwistIso P.coefficients.l P.extension (P.level - 1)
          T r hr hP hX ≪≫
          (coefficientTwistIso P.coefficients.l P.extension (P.level - 1)
            T s hs hP hX).symm) ≪≫
        chartComparison P T aT s hs =
      (VectorIntegrationSite.comparison (Ring P)
        (AffineSpace PUnit.{u + 1} T)).mapIso
        ((shiftFunctor _ (2 : ℤ)).mapIso
          ((DerivedCategory.singleFunctor _ 0).mapIso
            (transition P (AffineSpace PUnit.{u + 1} T)
              ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT) r s hr hs))) := by
  sorry

/-- Direct exponent independence for the normalized affine-line source.
Source: ordered root-power compatibility in vector integration, followed by max-exponent
cancellation; no coordinate-line adjunction theorem is used.
Proof: for `r ≤ s`, use the root-power comparison from `twistCompatibility` to
transport the normalized vector-integration comparison from level `s` to level
`r`. Tensor this equality with the fixed pullback of `K` and compose with the
normalized affine-line purity map. For arbitrary `r,s`, apply the ordered
identities through `max r s` and cancel the common comparison isomorphism.
(blueprint: lem-route-native-source-exponent-compatibility). -/
theorem native_source_exponent_compatibility (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (r s : ℕ)
    (hr : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hs : ((P.coefficients.l ^ (s + 1) : ℕ) : Ring P) = 0)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
    (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) T Ke)
    (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj) :
    (CoordinateLine.tensorCoefficientIso (Ring P) T _ _
      (coefficientTwistIso P.coefficients.l P.extension (P.level - 1)
        T r hr
        (primeUnit P (ProjectiveLine T) ((ProjectiveLine T ↘ T) ≫ aT))
        (primeUnit P (AffineSpace PUnit.{u + 1} T)
          ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT)) ≪≫
        (coefficientTwistIso P.coefficients.l P.extension (P.level - 1)
          T s hs
          (primeUnit P (ProjectiveLine T) ((ProjectiveLine T ↘ T) ≫ aT))
          (primeUnit P (AffineSpace PUnit.{u + 1} T)
            ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT))).symm) K.obj).hom ≫
      affineLinePurityComparison P T s hs aT K Ke hKe eK =
      affineLinePurityComparison P T r hr aT K Ke hKe eK := by
  sorry

/-- Tensoring the chart bridge with the fixed affine purity map transports the
source-coordinate exponent equation. This is the final categorical glue step.
Source: the final composition in the affine-line adjunction paragraph.
Proof: `tensorCoefficientIso` is the image of a coefficient isomorphism under the
fixed functor `Lp^*K ⊗ -`, so it respects composition and inverses. Apply it to
`hchart`, compose with `conjugate_s = (chart_s⁻¹ ⊗ 1) ≫ gamma_s`, cancel
`chart_s ≫ chart_s⁻¹`, and rewrite the middle factor by `hsource`.
(blueprint: lem-route-native-conjugate-transport). -/
theorem native_conjugate_transport (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (r s : ℕ)
    (hr : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hs : ((P.coefficients.l ^ (s + 1) : ℕ) : Ring P) = 0)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
    (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) T Ke)
    (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj)
    (hchart :
      (chartComparison P T aT r hr).symm ≪≫
          (coefficientTwistIso P.coefficients.l P.extension (P.level - 1)
            T r hr
            (primeUnit P (ProjectiveLine T) ((ProjectiveLine T ↘ T) ≫ aT))
            (primeUnit P (AffineSpace PUnit.{u + 1} T)
              ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT)) ≪≫
            (coefficientTwistIso P.coefficients.l P.extension (P.level - 1)
              T s hs
              (primeUnit P (ProjectiveLine T) ((ProjectiveLine T ↘ T) ≫ aT))
              (primeUnit P (AffineSpace PUnit.{u + 1} T)
                ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT))).symm) ≪≫
          chartComparison P T aT s hs =
        (VectorIntegrationSite.comparison (Ring P)
          (AffineSpace PUnit.{u + 1} T)).mapIso
          ((shiftFunctor _ (2 : ℤ)).mapIso
            ((DerivedCategory.singleFunctor _ 0).mapIso
              (transition P (AffineSpace PUnit.{u + 1} T)
                ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT) r s hr hs))))
    (hsource :
      (CoordinateLine.tensorCoefficientIso (Ring P) T _ _
        (coefficientTwistIso P.coefficients.l P.extension (P.level - 1)
          T r hr
          (primeUnit P (ProjectiveLine T) ((ProjectiveLine T ↘ T) ≫ aT))
          (primeUnit P (AffineSpace PUnit.{u + 1} T)
            ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT)) ≪≫
          (coefficientTwistIso P.coefficients.l P.extension (P.level - 1)
            T s hs
            (primeUnit P (ProjectiveLine T) ((ProjectiveLine T ↘ T) ≫ aT))
            (primeUnit P (AffineSpace PUnit.{u + 1} T)
              ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT))).symm) K.obj).hom ≫
        affineLinePurityComparison P T s hs aT K Ke hKe eK =
      affineLinePurityComparison P T r hr aT K Ke hKe eK) :
    (CoordinateLine.tensorCoefficientIso (Ring P) T _ _
      ((VectorIntegrationSite.comparison (Ring P)
        (AffineSpace PUnit.{u + 1} T)).mapIso
        ((shiftFunctor _ (2 : ℤ)).mapIso
          ((DerivedCategory.singleFunctor _ 0).mapIso
            (transition P (AffineSpace PUnit.{u + 1} T)
              ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT) r s hr hs)))) K.obj).hom ≫
      conjugate P T aT s hs K Ke hKe eK = conjugate P T aT r hr K Ke hKe eK := by
  have h := congrArg (fun e => (CoordinateLine.tensorCoefficientIso (Ring P) T _ _ e K.obj).hom ≫
    conjugate P T aT s hs K Ke hKe eK) hchart
  simp only [tensorCoefficientIso_trans, tensorCoefficientIso_symm, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, conjugate, Iso.hom_inv_id_assoc] at h hsource
  rw [hsource] at h
  simp only [conjugate, tensorCoefficientIso_symm, Iso.symm_hom]
  exact h.symm

/-- The normalized finite affine-line conjugates are independent of the exponent.
The transition is exactly inverse rho_{M,s0} followed by rho_{M,s1}, placed
in degree zero, shifted by two, pulled to the pro-etale site, and tensored
with Lp^*K. Source: final affine-line-adjunction paragraph of
cor-pur-affine-space-zero-section-purity.proof.md
(blueprint: lem-route-coordinate-line-conjugate-exponents).

Proof: the finite purity setting fixes the coefficient quotient and the normalized
integration transpose. For ordered exponents the root power map preserves the
Kummer boundary and its coefficient unit. The normalized root comparisons of
vector-integration site comparison therefore intertwine alpha at the two levels.
Tensor with Lp^*K, shift by two and compose with the fixed normalized gamma.
For arbitrary exponents apply this ordered equality to each exponent and their
maximum. Cancel the invertible common-level power comparison; the remaining map
is precisely transition. Equal exponents give identities. For the zero ring,
empty base or zero K the equation is the equality of the unique zero maps.
-/
theorem conjugate_exponents (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (r s : ℕ)
    (hr : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hs : ((P.coefficients.l ^ (s + 1) : ℕ) : Ring P) = 0)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
    (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) T Ke)
    (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj) :
    (CoordinateLine.tensorCoefficientIso (Ring P) T _ _
      ((VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).mapIso
        ((shiftFunctor _ (2 : ℤ)).mapIso
          ((DerivedCategory.singleFunctor _ 0).mapIso
            (transition P (AffineSpace PUnit.{u + 1} T)
              ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT) r s hr hs)))) K.obj).hom ≫
      conjugate P T aT s hs K Ke hKe eK = conjugate P T aT r hr K Ke hKe eK := by
  have hP : IsUnit (P.coefficients.l : Γ(ProjectiveLine T, ⊤)) :=
    primeUnit P (ProjectiveLine T) ((ProjectiveLine T ↘ T) ≫ aT)
  have hX : IsUnit (P.coefficients.l : Γ(AffineSpace PUnit.{u + 1} T, ⊤)) :=
    primeUnit P (AffineSpace PUnit.{u + 1} T)
      ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT)
  have htrans := native_transition_compatibility P T aT r s hr hs
  have hchart := native_chart_compatibility P T aT r s hr hs hP hX htrans
  have hsource := native_source_exponent_compatibility P T aT r s hr hs K Ke hKe eK
  exact native_conjugate_transport P T aT r s hr hs K Ke hKe eK hchart hsource

end AlgebraicGeometry.ProEtale.NativeCoordinateLine
