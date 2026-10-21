/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses
import Sheaf.Paper.IntegralResidueTor
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.FiniteConstructibleHom
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-!
# Residue-controlled uniform bounds for finite internal Homs

Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-tower,
cor-coef-integral-internal-hom.proof.md, sentences 2–3 and the final sentence
(blueprint: lem-coef-residue-controlled-finite-homs).

The index `n : ℕ` denotes exponent `n+1`; index zero is the residue reduction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The finite internal Hom of the two canonical reductions, at exponent `n+1`.
It uses modules over the constant finite coefficient sheaf on the original small site.
Source: main-20261015, cor-coef-integral-internal-hom.proof.md, sentence 3
(blueprint: lem-coef-residue-controlled-finite-homs). -/
noncomputable def integralFiniteInternalHom
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (K L : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :
    proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)) :=
  (derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X)
    (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n + 1)))).obj
      (op ((scalarReductionDerivedExtension.{u, u} l E X n).obj K),
        (scalarReductionDerivedExtension.{u, u} l E X n).obj L)

/-- Residue cohomological bounds give one uniform interval for bounded constructibility,
Tor amplitude and cohomological support of all finite internal Homs.
Source: main-20261015, cor-coef-integral-internal-hom.proof.md, sentences 2–3
and the final sentence (blueprint: lem-coef-residue-controlled-finite-homs).

Proof:
1. Integral constructibility gives bounded constructibility of every reduction.
Since l differs from the characteristic of the base field, l is invertible on X.
Apply lem-coef-integral-residue-tor to K and L with the supplied residue intervals,
obtaining Tor intervals [a,b] and [c,e] at every positive level. Together with
constructibility these are the conditions of def-weil-finite-tor-amplitude.
2. Apply the pro-etale clause of cor-weil-finite-constructible-hom at exponent n+1.
It gives bounded constructibility and Tor interval [c-b-2d,e-a+2d]. The endpoints
involve only the residue bounds and d, so they are independent of n.
3. Test Tor amplitude against the coefficient sheaf in degree zero. On a K-flat
representative P, the maps P tensor B_n → P, x tensor r ↦ r x, and
P → P tensor B_n, x ↦ x tensor 1, are inverse chain maps by tensor balancing
and linearity of the differential. Hence the tensor test is the same derived
object, giving the stated cohomological support inclusion. -/
theorem residue_controlled_finite_homs
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (K L : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (_hK : sfIntegralConstructible l E X K) (_hL : sfIntegralConstructible l E X L)
    (a b c e : ℤ) (_hab : a ≤ b) (_hce : c ≤ e)
    (_hK₁ : proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K) ⊆ Set.Icc a b)
    (_hL₁ : proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension.{u, u} l E X 0).obj L) ⊆ Set.Icc c e) :
    ∀ n : ℕ,
      intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) X (integralFiniteInternalHom l E X K L n) ∧
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        (integralFiniteInternalHom l E X K L n)
        (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ)) ∧
      proEtaleCohomologicalSupport (integralFiniteInternalHom l E X K L n) ⊆
        Set.Icc (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ)) := by
  sorry

end WeilConjectures
