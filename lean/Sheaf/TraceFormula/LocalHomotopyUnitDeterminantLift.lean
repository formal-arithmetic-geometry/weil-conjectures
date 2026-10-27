/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.LocalRing.Basic
import Sheaf.TraceFormula.LocalCommonSummandSurjections
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # A determinant-trivial chain automorphism lifting a local homotopy

Source: Stacks Project, more-algebra.tex, Tags 0FJK (lemma-homotopic-surjections)
and 0FJF (lemma-det-switch), with the explicit block-inverse refinement
(blueprint: lem-trf-local-homotopy-unit-determinant-lift).

A two-term complex is displayed by its two modules and its sole differential.
Chain maps and chain automorphisms are displayed by their two components and the
commutation equation. All other degrees are zero. No derived quasi-isomorphism
hypothesis is required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v₁ v₂ v₃ v₄

namespace LinearMap

/-- A homotopy of degreewise surjections lifts through a common summand to a chain
 automorphism with equal determinants in both degrees and identity determinant-line action.
The maps `a₁`, `b₁` are in degree -1; `a₀`, `b₀` are in degree zero. The equivalences
`K`, `L` are the components of the chain automorphism. The equations on `n + x` give
its block matrix and the block matrix of its inverse, without choosing a basis of the kernel.

Source: Stacks Project, more-algebra.tex, Tag 0FJK, first two and final proof paragraphs,
and Tag 0FJF (blueprint: lem-trf-local-homotopy-unit-determinant-lift).

Proof:
1. Choose finite bases and apply lem-trf-local-common-summand-surjections to the coordinate
maps of a₁ and b₁. Transport its common summand U back to P₁. Both restrictions are
isomorphisms and P₁ = ker(a₁) ⊕ U. Set s = inclusion composed with the inverse restriction.
2. Put t = sh, K = 1 + tdP, L = 1 + dPt. Then a₁t = h. Expansion gives dPK = LdP.
The two homotopy equations and the chain-map equation give a₁K = b₁ and a₀L = b₀.
3. On ker(a₁) ⊕ U, tdP takes values in U. Its restriction to the kernel is C, and the
U-block of K is B = (a₁|U)⁻¹(b₁|U). Thus K has blocks (1,0;C,B). Direct multiplication
gives inverse blocks (1,0;-B⁻¹C,B⁻¹), without any freeness assertion for the kernel.
4. Write w = K⁻¹ and V = 1 - dPwt. The equations Kw = wK = 1 give
wt + tdPwt = t and wt + wtdPt = t. Hence LV = VL = 1, so L⁻¹ = V.
The equation dPK = LdP also gives VdP = dPw, making the inverses a chain map.
5. In any finite bases the two component matrices are I+DT and I+TD. Apply
lem-trf-rectangular-determinant-switch, including either rank being zero.
6. By lem-weil-pbc-exterior-power-free-basis the top exterior powers are free on the
top basis wedges (generator 1 in rank zero). Multilinear expansion shows the top exterior
maps multiply by the common determinant δ. The inverse negative component multiplies by
δ⁻¹, as does its dual by precomposition. Their tensor product multiplies by δδ⁻¹ = 1.
-/
theorem exists_local_homotopy_unit_determinant_lift
    {R : Type u} [CommRing R] [IsLocalRing R]
    {P₁ : Type v₁} [AddCommGroup P₁] [Module R P₁]
    {P₀ : Type v₂} [AddCommGroup P₀] [Module R P₀]
    {Q₁ : Type v₃} [AddCommGroup Q₁] [Module R Q₁]
    {Q₀ : Type v₄} [AddCommGroup Q₀] [Module R Q₀]
    [Module.Free R P₁] [Module.Finite R P₁]
    [Module.Free R P₀] [Module.Finite R P₀]
    [Module.Free R Q₁] [Module.Finite R Q₁]
    [Module.Free R Q₀] [Module.Finite R Q₀]
    (dP : P₁ →ₗ[R] P₀) (dQ : Q₁ →ₗ[R] Q₀)
    (a₁ b₁ : P₁ →ₗ[R] Q₁) (a₀ b₀ : P₀ →ₗ[R] Q₀)
    (ha : a₀.comp dP = dQ.comp a₁) (hb : b₀.comp dP = dQ.comp b₁)
    (ha₁ : Function.Surjective a₁) (hb₁ : Function.Surjective b₁)
    (ha₀ : Function.Surjective a₀) (hb₀ : Function.Surjective b₀)
    (h : P₀ →ₗ[R] Q₁) (hh₀ : b₀ - a₀ = dQ.comp h)
    (hh₁ : b₁ - a₁ = h.comp dP) :
    ∃ (U : Submodule R P₁) (eA eB : U ≃ₗ[R] Q₁),
      eA.toLinearMap = a₁.domRestrict U ∧
      eB.toLinearMap = b₁.domRestrict U ∧
      IsCompl (LinearMap.ker a₁) U ∧
      ∃ (s : Q₁ →ₗ[R] P₁) (t : P₀ →ₗ[R] P₁)
        (K : P₁ ≃ₗ[R] P₁) (L : P₀ ≃ₗ[R] P₀)
        (C : LinearMap.ker a₁ →ₗ[R] U),
        s = U.subtype.comp eA.symm.toLinearMap ∧
        t = s.comp h ∧ a₁.comp t = h ∧
        K.toLinearMap = LinearMap.id + t.comp dP ∧
        L.toLinearMap = LinearMap.id + dP.comp t ∧
        dP.comp K.toLinearMap = L.toLinearMap.comp dP ∧
        a₁.comp K.toLinearMap = b₁ ∧ a₀.comp L.toLinearMap = b₀ ∧
        U.subtype.comp C = (t.comp dP).comp (LinearMap.ker a₁).subtype ∧
        (∀ (n : LinearMap.ker a₁) (x : U),
          K ((n : P₁) + (x : P₁)) = (n : P₁) + ((C n + eA.symm (eB x) : U) : P₁)) ∧
        (∀ (n : LinearMap.ker a₁) (x : U),
          K.symm ((n : P₁) + (x : P₁)) =
            (n : P₁) + ((eB.symm (eA (x - C n)) : U) : P₁)) ∧
        L.symm.toLinearMap = LinearMap.id - dP.comp (K.symm.toLinearMap.comp t) ∧
        dP.comp K.symm.toLinearMap = L.symm.toLinearMap.comp dP ∧
        (∀ (r₁ r₀ : ℕ) (c₁ : Module.Basis (Fin r₁) R P₁)
          (c₀ : Module.Basis (Fin r₀) R P₀),
          Matrix.det (LinearMap.toMatrix c₀ c₀ L.toLinearMap) =
            Matrix.det (LinearMap.toMatrix c₁ c₁ K.toLinearMap)) ∧
        TensorProduct.map
          (exteriorPower.map (Module.finrank R P₀) L.toLinearMap)
          (exteriorPower.map (Module.finrank R P₁) K.symm.toLinearMap).dualMap =
          LinearMap.id := by
  sorry

end LinearMap
