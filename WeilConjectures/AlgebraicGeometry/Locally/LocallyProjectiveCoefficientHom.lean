/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientPairingChange.InternalAdjunctionPairingChange
public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.Locally.LocallyProjectiveCoefficientHomConstructibility
import WeilConjectures.AlgebraicGeometry.Locally.LocallyProjectiveCoefficientHomEvaluation

/-! # Coefficient Hom from a locally finite projective sheaf

Source: blueprint thm-coef-finite-hom, the finite-projective local calculation in
proof paragraphs 2--3 (blueprint: lem-coef-locally-projective-coefficient-hom).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Etale
open CoefficientPairingChange

/-- The local finite-projective calculation, with arbitrary finite coefficients and
an arbitrary second argument of finite-Tor bounded constructibility.
Source: blueprint thm-coef-finite-hom, proof paragraphs 2--3
(blueprint: lem-coef-locally-projective-coefficient-hom).

Proof: The finite projective trivializing values are finite sets and flat modules.
The finite-value and geometric-stalk criteria therefore make the sheaf finite
locally constant and flat. Existing degree-zero and internal-Hom stability results
give both finiteness conclusions. The degree-zero sheaf is dualizable. Derived
scalar extension is strong monoidal even without flatness of the coefficient map.
Its tensorator has the prescribed cochain normalization, so uniqueness identifies
it with the specified tensor comparison. The evaluation transpose is consequently
the internal-Hom comparison at a dualizable object and is invertible. The argument
also covers rank zero, the empty scheme and zero rings; it uses no global rank bound. -/
theorem locallyProjectiveCoefficientHom
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    (L : Sheaf T.smallEtaleTopology (ModuleCat A))
    (hL : ∃ d : Scheme.LocallyConstantDatum L, ∀ i : d.cover.I₀,
      ∃ P : ModuleCat A, Module.Finite A P ∧ Module.Projective A P ∧
        Nonempty (L.over (d.cover.etalePrecoverageToEtale i) ≅
          (constantSheaf (T.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
            (ModuleCat A)).obj P))
    (N : DerivedCategoryModule A T)
    (hN : DerivedCategory.isBoundedConstructible A T N ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A T a b N) :
    (DerivedCategory.isBoundedConstructible A T
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L) ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A T a b
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) ∧
    (DerivedCategory.isBoundedConstructible A T
        (((derivedHom (ModuleCat A) T).obj
          (op ((_root_.DerivedCategory.singleFunctor _ 0).obj L))).obj N) ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A T a b
        (((derivedHom (ModuleCat A) T).obj
          (op ((_root_.DerivedCategory.singleFunctor _ 0).obj L))).obj N)) ∧
    IsIso (evaluationComparison φ T ((_root_.DerivedCategory.singleFunctor _ 0).obj L) N) := by
  have hfin := locallyProjectiveCoefficientHom_constructibility T L hL N hN
  have heval := locallyProjectiveCoefficientHom_evaluation φ T L hL N hN
  exact ⟨hfin.1, hfin.2, heval⟩

end AlgebraicGeometry.Etale
