/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingMappingTower
import WeilConjectures.SixFunctors.IntegralDualizingMappingTowerFiniteComponents

/-! # Finite adjunction comparison of strict mapping towers

Source: current blueprint prop-coef-integral-dualizing, second proof paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The finite exceptional adjunctions identify the two strict derived Hom
towers before taking their limits. The input is the coherent finite dualizing
tower, and the conclusion contains no integral dualizing limit object.

Source: current blueprint prop-coef-integral-dualizing, middle and final displayed
comparisons in the second proof paragraph, and its final counit-compatibility sentence.
(blueprint: lem-coef-integral-dualizing-mapping-tower-finite-comparison).

Proof: resolve the given completed-coefficient tower simultaneously. The evaluation
isomorphisms of T followed by e identify its finite terms with the specified finite
dualizing objects. For any bounded constructible K, residue Tor invariance gives a
single finite Tor interval on all reductions. Compact-support reduction identifies
the finite compact-support complexes with the reductions of the defined integral
compact-support value C; point sections preserve those comparisons and their maps.
Scalar tensor-restriction adjunction identifies each evaluated global Hom tower
with the finite-coefficient Hom. Finite exceptional adjunction then identifies it
with RHom_R(C,A_n), using the actual compact-support projection and scalar balancing.
The equation he and the finite adjunction transition square show that all these
comparisons use the prescribed exceptional counits under every quotient map.
Form the trace on simultaneous resolutions from those counits, compose with
compact-support evaluation and its coaugmentation, and curry. This constructs an
actual map of derived strict towers, natural in K before evaluation. Do not lift
unrelated levelwise isomorphisms or choose an arbitrary compact-support trace.
Evaluation identifies the map with the preceding finite adjunction isomorphisms.
Exact tower evaluations jointly detect quasi-isomorphisms, so this map is invertible.
Naturality follows from evaluation dinaturality and the injectivity of currying.
The closed Hom from a constant complex used in the target is the same simultaneous
Hom(P,I_n) model by uniqueness of its tensor right adjoint. Change of localization
model uses integralDualizingTowerEquivalence. No common Tor interval for all K is
required: the natural map is defined first, and invertibility is checked one K
at a time. For zero K and empty X all these maps are maps between zero objects. -/
theorem integralDualizing_mapping_tower_finite_comparison
    (T : NormalizedDVRTower l E X D hl)
    (e : ∀ n : ℕ, T.M n ≅ integralDualizingFiniteTerm l E D X n)
    (he : ∀ {m n : ℕ} (h : n ≤ m),
      T.tau h ≫ (normalizedDVRRes l E X h).map (e n).hom =
        (e m).hom ≫
          (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
            (integralDualizingFiniteComparison l E D X hl h))
    : Nonempty (integralDualizingMappingTower l E X T.tower ≅
      (integralDualizingCompactSections l E D hl X).op ⋙
        integralDualizingCoefficientHomTower l E) := by
  obtain ⟨a, ha⟩ := integralDualizing_mapping_tower_finite_components
    D l hl E X T e he
  exact ⟨NatIso.ofComponents a (fun f ↦ ha f)⟩

end WeilConjectures
