/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
public import Sheaf.NumberTheory.Padics.CoefficientExtensionSmallLog
public import Mathlib.GroupTheory.GroupAction.ConjAct
import Sheaf.CategoryTheory.Galois.AutProfinite
import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.NumberTheory.Padics.DeepPrincipalUnitLog
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.GroupTheory.WeilGroup

/-!
# An invariant additive character from a multiplicative Weil character

Source: Weil conjectures blueprint, sec-purity-real-sheaves/sk-d-real-log,
lem-wf-compact-character-logarithm (blueprint: lem-wf-compact-character-logarithm).

The geometric fundamental group is represented by the kernel of the degree map, as in
lem-wf-weil-group-exact-sequence. The Weil group is the recorded subgroup of the arithmetic
fundamental group times discrete ℤ, with its subspace topology. Thus its geometric subgroup
is open and has its profinite topology. `MulAut.conjNormal` writes both conjugations within
this kernel, without an untyped coercion back from the Weil group.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- A continuous multiplicative Weil character has a uniform positive power whose small
logarithm is a continuous additive character of the geometric fundamental group, invariant
under conjugation by a degree-one lift and its inverse.

Source: blueprint sec-purity-real-sheaves/sk-d-real-log,
lem-wf-compact-character-logarithm, statement and three proof paragraphs
(blueprint: lem-wf-compact-character-logarithm).

Proof plan:
1. By def-galois-fibre-functor and lem-galois-aut-profinite the geometric fundamental group
is profinite, hence compact. Identify it with the degree kernel by
lem-wf-weil-group-exact-sequence; the Weil topology restricts to its profinite topology.
2. The absolute value of def-weil-l-adic-coefficient-extension and the uniformizer
factorization of lem-weil-l-adic-extension-integers-dvr give the normalized integer valuation.
The ultrametric inequality in lem-weil-l-adic-extension-absolute-value makes it locally
constant. The compact image under this valuation is a finite subgroup of ℤ, hence zero.
Thus every geometric value of the character is a unit of the integer ring.
3. Put e = v_E(ℓ) and r = 2e+1. Then r > e/(ℓ-1), also for ℓ = 2.
Apply lem-wf-deep-principal-unit-log to obtain a uniform N ≥ 1 taking all integer-ring
units into 1 + 𝔪_E^r. Since r ≥ 2e, this lies in 1 + ℓ² 𝒪_E. The deep logarithm
and the small logarithm of sk-d-real-log are the same convergent series there.
4. The power map on the abelian target is a continuous homomorphism. Compose its
restriction to the geometric group with the continuous deep logarithm and inclusion into E.
This gives the displayed formula, continuity, and the additive character identity.
5. Both conjugates have degree zero. Since the target Eˣ is abelian, the original
character has equal values on g, sgs⁻¹ and s⁻¹gs. Take N-th powers and apply the same
logarithm to obtain both asserted invariances. -/
theorem exists_compactCharacterLogarithm
    (k₀ : Type u) [Field k₀] [Finite k₀] {U₀ : Scheme.{u}}
    (p : U₀ ⟶ Spec (.of k₀)) [GeometricallyConnected p] [IsSeparated p]
    [LocallyOfFiniteType p] [QuasiCompact p]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ U₀)
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E]
    (χ : weilGroup p x (Aut (fiber x)) →* Eˣ)
    (hχ : @Continuous _ E inferInstance
      (spectralNorm.normedField (Padic ℓ) E).toUniformSpace.toTopologicalSpace
      (fun w ↦ (χ w : E)))
    (s : weilGroup p x (Aut (fiber x)))
    (hs : weilGroupDeg p x (Aut (fiber x)) s = Multiplicative.ofAdd 1) :
    ∃ N r : ℕ, 1 ≤ N ∧ 1 ≤ r ∧
      ∃ lam : (weilGroupDeg p x (Aut (fiber x))).ker → E,
        (∀ g : (weilGroupDeg p x (Aut (fiber x))).ker,
          χ g.val ^ N ∈ Padic.coefficientExtensionSmallUnits ℓ E) ∧
        (∀ g : (weilGroupDeg p x (Aut (fiber x))).ker,
          lam g = Padic.coefficientExtensionSmallLog ℓ E (((χ g.val ^ N : Eˣ) : E) - 1)) ∧
        @Continuous _ E inferInstance
          (spectralNorm.normedField (Padic ℓ) E).toUniformSpace.toTopologicalSpace lam ∧
        (∀ g h : (weilGroupDeg p x (Aut (fiber x))).ker, lam (g * h) = lam g + lam h) ∧
        (∀ g : (weilGroupDeg p x (Aut (fiber x))).ker,
          lam (MulAut.conjNormal s g) = lam g ∧ lam g = lam (MulAut.conjNormal s⁻¹ g)) := by
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
