/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Sheaf.Topology.PresheafModuleStalkFunctor
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.Support

/-!
# Closed support of a finite type module

Source: Stacks Project, Morphisms, Lemma 056J (part (1)), via Lemma 056I,
Properties Lemma 01PB and Algebra Lemma 00L2 (blueprint:
lem-weil-pbc-finite-type-module-support-closed).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Let `F` be a quasi-coherent `𝒪_X`-module of finite type and `U` an affine open with
`A = Γ(X, U)`, `M = Γ(F, U)`, the point `x ∈ U` corresponding to the prime `p_x` of `A`.
Then (1) `F_x ≅ M_{p_x}`, the isomorphism sending `m / s` to `s_x⁻¹ • m_x`
(stated as `s_x • e (m / s) = m_x`, which determines `e` since `s_x` is a unit);
(2) `x ∈ Supp F` iff `Ann_A(M) ⊆ p_x`; (3) `Supp F ∩ U = V(Ann_A(M))`;
(4) `Supp F = {x | F_x ≠ 0}` is closed in `X`.

Proof: on the affine chart `U ≅ Spec A` the restriction `F|_U` is quasi-coherent of finite
type, hence `F|_U ≅ M~` with `M` finitely generated (Properties 01PB and the tilde/Γ
adjunction). The stalk of `F` at `x` is the stalk of `F|_U` (cofinal neighbourhoods), and the
stalk of `M~` at `p_x` is `M_{p_x}` (Schemes 01HV (7)), giving (1). By Algebra 00L2 a finite
module has `M_p ≠ 0` iff `Ann_A(M) ⊆ p`, giving (2) and (3). The sets `V(Ann_A(M))` are closed
in each affine chart and the affine opens cover `X`, giving (4).
Source: Stacks Project, Morphisms, Lemma 056J (1), via Lemma 056I, Properties Lemma 01PB and
Algebra Lemma 00L2.
(blueprint: lem-weil-pbc-finite-type-module-support-closed) -/
theorem finite_type_module_support_closed (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    (∀ (U : X.affineOpens) (x : X) (hx : x ∈ U.1),
      ∃ e : LocalizedModule (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U.1) ≃+
          (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F,
        ∀ (m : Γ(F, U.1)) (s : (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl),
          X.presheaf.germ U.1 x hx s.1 • e (LocalizedModule.mk m s) =
            F.presheaf.germ U.1 x hx m) ∧
    (∀ (U : X.affineOpens) (x : X) (hx : x ∈ U.1),
      ¬ Subsingleton (F.presheaf.stalk x) ↔
        Module.annihilator Γ(X, U.1) Γ(F, U.1) ≤ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal) ∧
    (∀ (U : X.affineOpens),
      {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∩ (U.1 : Set X) =
        U.2.fromSpec '' PrimeSpectrum.zeroLocus
          (Module.annihilator Γ(X, U.1) Γ(F, U.1) : Set Γ(X, U.1))) ∧
    IsClosed {x : X | ¬ Subsingleton (F.presheaf.stalk x)} := by
  sorry

end AlgebraicGeometry.Scheme.Modules
