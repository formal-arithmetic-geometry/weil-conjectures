/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.FormalPolynomialPowerLifts

/-! # Affine local vanishing of ideal-power evaluation

Source: Stacks Project, Properties, Lemma 01PM, injectivity argument, as used in 01PQ.
(blueprint: lem-weil-pbc-ideal-power-evaluation-affine-eventually-zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Evaluation zero forces eventual vanishing on a single affine open. No compactness
of the ambient scheme is required.

Source: Stacks Project, Properties, Lemma 01PM, proof of injectivity, and Lemma 01PQ,
first proof paragraph.
(blueprint: lem-weil-pbc-ideal-power-evaluation-affine-eventually-zero).

Proof: On V identify the quasi-coherent ideal with a finitely generated ideal J
of A = Γ(V, O_X), and F with the sheaf of its section module M. The recursive
power inclusions identify P_n with the sheaf of J^n, including n = 0. Choose
finitely many generators f_i of J. Each D(f_i) lies in U by the stalk description
of U. The section one n restricts to the inverse image of 1 under the power
inclusion; hence the restriction of evaluation is phi(f_i^n)/f_i^n. Its vanishing
implies f_i^k_i phi(f_i^n) = 0 by the localization zero criterion. Enlarge the
finitely many k_i to a common k with n+k positive. Linearity then gives
phi(f_i^(n+k)) = 0. Every generating monomial of degree t*(n+k-1)+1 contains
one f_i^(n+k), so phi vanishes on that ideal power. Enlarge this degree to be
at least n. If J is zero, take a positive exponent at least n instead. The maps
r are the power inclusions: their composites with the monic inclusion of P_n
are the inclusions of P_m. The affine tilde/Gamma equivalence converts the
zero linear map to the asserted zero restricted sheaf morphism. The argument
also covers the empty affine open and n = 0. -/
theorem ideal_power_evaluation_affine_eventually_zero
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
    (r : ∀ (n m : ℕ), n ≤ m →
      ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1))
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (hone : ∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U)))
    (hr : ∀ (n m : ℕ) (h : n ≤ m),
      r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2) :
    ∀ (V : X.affineOpens) (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ F),
      φ.app U (one n) = 0 →
      ∃ (m : ℕ) (h : n ≤ m), (r n m h ≫ φ).over V.1 = 0 := by sorry

end AlgebraicGeometry.Scheme
