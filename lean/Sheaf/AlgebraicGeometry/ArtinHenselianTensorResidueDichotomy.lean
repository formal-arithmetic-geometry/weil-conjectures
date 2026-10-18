/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Connected.Basic
public import Sheaf.RingTheory.IndPrincipalZariski
public import Sheaf.TraceFormula.AffineEtaleCoverComponentCriterion
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.AlgebraicGeometry.ArtinJoinTheorem63
import Sheaf.RingTheory.TensorComponentFromFactorComponents
import Sheaf.TraceFormula.ComponentQuotientIndEtale
import Sheaf.TraceFormula.IndEtaleLocalHenselianIntegral
import WeilConjectures.RingTheory.ProEtale.IndEtale

/-!
# Artin henselian tensor residue dichotomy

Source: Hübner–Schmidt, *The tame site of a scheme*, §6, component-ring convention, printed
p. 12, and Theorem 6.4, printed p. 13, two factors
(blueprint: lem-trf-artin-henselian-tensor-residue-dichotomy).

The statement was independently checked for the NB stage-2 delivery on 2026-10-18.

The component ideal `I_Z`, the component ring `C_Z = C / I_Z` and the map
`Spec C_Z → Spec C` are the landed `AlgebraicGeometry.componentIdeal`,
`AlgebraicGeometry.componentRing` and `AlgebraicGeometry.componentSpectrumMap`
(lem-trf-affine-etale-cover-component-criterion), the same convention as the node's.
-/

@[expose] public section

universe u

open scoped TensorProduct

/-- A ring homomorphism between maximal-ideal residue quotients makes the target a separable
algebraic extension, using the quotient field structures and the algebra structure of `f`.
Source: Hübner–Schmidt, Theorem 6.4, printed p. 13
(blueprint: lem-trf-artin-henselian-tensor-residue-dichotomy). -/
def RingHom.IsSeparableAlgebraic {K L : Type u} [CommRing K] [CommRing L]
    (n : Ideal K) (m : Ideal L) (_hn : n.IsMaximal) (_hm : m.IsMaximal)
    (f : (K ⧸ n) →+* (L ⧸ m)) : Prop :=
  letI : Field (K ⧸ n) := Ideal.Quotient.field n
  letI : Field (L ⧸ m) := Ideal.Quotient.field m
  letI : Algebra (K ⧸ n) (L ⧸ m) := f.toAlgebra
  Algebra.IsAlgebraic (K ⧸ n) (L ⧸ m) ∧ Algebra.IsSeparable (K ⧸ n) (L ⧸ m)

/-- Separably closedness of a maximal-ideal residue quotient, with its field structure installed.
Source: Hübner–Schmidt, Theorem 6.4, printed p. 13
(blueprint: lem-trf-artin-henselian-tensor-residue-dichotomy). -/
def Ideal.IsSepClosedQuotient {C : Type u} [CommRing C]
    (m : Ideal C) (_hm : m.IsMaximal) : Prop :=
  letI : Field (C ⧸ m) := Ideal.Quotient.field m
  IsSepClosed (C ⧸ m)

/-- Tensor products of ind-étale algebras with henselian local components have henselian
local components, and their residue fields satisfy Artin's dichotomy.
Source: Hübner–Schmidt, *The tame site of a scheme*, §6, Theorem 6.4,
printed p. 13 (blueprint: lem-trf-artin-henselian-tensor-residue-dichotomy).

Proof (from the node):
1. Component convention (lem-trf-affine-etale-cover-component-criterion): `T_Z = T / I_Z`
   and `Spec T_Z` has underlying space `Z`; this is the range clause. The hypotheses say the
   factors are quasi-acyclic: all component rings are henselian local.
2. Fix a component ring `C` of `B = B₁ ⊗[R] B₂`. By
   lem-trf-tensor-component-from-factor-components choose component quotients
   `q_j : B_j → D_j` and `E = D₁ ⊗[R] D₂ → C`, the composite from `B` being its component
   quotient. Each `D_j` is henselian local and ind-étale over `R`
   (lem-trf-component-ind-etale-local-henselian), hence a local integral
   `R^h_{p_j}`-algebra (lem-trf-ind-etale-local-henselian-integral). Artin's join theorem
   (lem-trf-artin-join-theorem-6-3) makes `E` quasi-acyclic, so `C` is henselian local.
3. For maximal `m ⊂ B` on the component `Z`: `I_Z ⊆ m`, `m_C = m / I_Z` is the maximal ideal
   of the local ring `C` and `C / m_C = B / m`. If both `D_j → C` are nonlocal,
   lem-trf-artin-join-theorem-6-3 gives `B / m` separably closed.
4. Otherwise some `D_i → C` is local; it is integral with algebraic residue extension
   (lem-trf-artin-join-theorem-6-3).
5. `n = q_i⁻¹(m_{D_i})` is maximal with `B_i / n ≅ D_i / m_{D_i}`, and locality with the
   commuting quotients gives `n = m ∩ B_i`; the residue map is the canonical
   `B_i / n → B / m`.
6. `B_i → B` is ind-étale by base change, `B → C` by
   lem-trf-component-ind-etale-local-henselian, so `B_i → C` is ind-étale
   (lem-weil-pbc-ind-etale-stability); lem-trf-ind-etale-residue-separable makes
   `B_i / n → B / m` separable algebraic. If `B = 0` both conclusions are vacuous. -/
theorem artin_henselian_tensor_residue_dichotomy
    (R B₁ B₂ : Type u)
    [CommRing R] [CommRing B₁] [CommRing B₂]
    [Algebra R B₁] [Algebra R B₂]
    [Algebra.IndEtale R B₁] [Algebra.IndEtale R B₂]
    (h₁ : ∀ x : PrimeSpectrum B₁,
      HenselianLocalRing (AlgebraicGeometry.componentRing B₁ x))
    (h₂ : ∀ x : PrimeSpectrum B₂,
      HenselianLocalRing (AlgebraicGeometry.componentRing B₂ x)) :
    (∀ x : PrimeSpectrum (TensorProduct R B₁ B₂),
      HenselianLocalRing (AlgebraicGeometry.componentRing (TensorProduct R B₁ B₂) x) ∧
        Set.range (AlgebraicGeometry.componentSpectrumMap (TensorProduct R B₁ B₂) x) =
          connectedComponent x) ∧
      ∀ (m : Ideal (TensorProduct R B₁ B₂)) [m.IsMaximal],
        Ideal.IsSepClosedQuotient m ‹m.IsMaximal› ∨
          (∃ (n : Ideal B₁),
            ∃ hn : n.IsMaximal, n = m.comap Algebra.TensorProduct.includeLeftRingHom ∧
            ∃ f : (B₁ ⧸ n) →+* ((TensorProduct R B₁ B₂) ⧸ m),
              f.comp (Ideal.Quotient.mk n) =
                (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom ∧
                f.IsSeparableAlgebraic n m hn ‹m.IsMaximal›) ∨
          (∃ (n : Ideal B₂),
            ∃ hn : n.IsMaximal, n = m.comap Algebra.TensorProduct.includeRight.toRingHom ∧
            ∃ f : (B₂ ⧸ n) →+* ((TensorProduct R B₁ B₂) ⧸ m),
              f.comp (Ideal.Quotient.mk n) =
                (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom ∧
                f.IsSeparableAlgebraic n m hn ‹m.IsMaximal›) := by
  sorry
