/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsSepClosed
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Absolute cohomological dimension of a profinite geometric family

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph
(blueprint: lem-sfb-profinite-geometric-family-heart-cd).

This is the agent-formulated absolute input in the node, with the nonsharp bound `2e + 2`.
The full norm-topological coefficient statement remains a source obligation; the module
states it without claiming it follows from a torsion or completed-coefficient theorem.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Ordinary module-object cohomology of a proper family over an affine reduced,
zero-dimensional w-contractible base with separably closed residue fields vanishes above
`2e + 2` on the entire constructibly generated weak Serre coproduct heart.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph; agent-formulated
absolute estimate, exact reference for the full coefficient generality wanted
(blueprint: lem-sfb-profinite-geometric-family-heart-cd).

Proof plan, the four steps of the DAG node:
1. For an affine open V of Z, the composite V -> C is locally of finite type by properness
of h and openness of V. Since V and C are affine it is quasi-compact, hence finite type.
Each geometric fibre V_c is open in Z_c. Closure of irreducible chains in the ambient
space shows its dimension is at most e, including empty fibres.
2. Open module pullback is additive exact by det-prop-sfb-module-pullback-exact-main.
It preserves coproducts by the module pullback/direct-image adjunction and
lem-weil-pbc-left-adjoint-preserves-colimits. Restricting strata and their scalar-model
covers preserves the very same finitely presented scalar modules. Thus the inverse-image
class has every defining closure property of the weak Serre coproduct intersection,
and minimality sends N in P_Z to its restriction in P_V. This argument does not assert
that a cohomology vanishing class is closed under kernels.
3. Apply lem-sfb-affine-profinite-family-serre-cd to V -> C, the same e, coefficients,
and restricted N, to obtain affine-open cohomology vanishing in degrees q > e + 2.
No finite-subextension or completion replacement is made.
4. Apply lem-sfb-zero-dimensional-base-affine-global with base C, scheme Z, coefficient
ring Lambda_Z, module N, and a = e + 2. Properness supplies separatedness and finite type;
the ringed open comparison identifies the restriction with the pullback in Step 2.
The conclusion is vanishing for r > e + (e + 2) = 2e + 2. Both inputs include the empty
base, source and opens, and the bound is independent of N and of the affine open.
-/
theorem profinite_geometric_family_serreHeart_cohomology_vanishes
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj (PadicAlgCl ℓ))))
    {C Z : Scheme.{u}} [IsAffine C] [IsReduced C]
    [IsWContractibleRing Γ(C, ⊤)]
    (hCdim : ∀ p : PrimeSpectrum Γ(C, ⊤), p.asIdeal.IsMaximal)
    (hCres : ∀ c : C, IsSepClosed (C.residueField c))
    (h : Z ⟶ C) [IsProper h] (e : ℕ)
    (he : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (c : Spec (CommRingCat.of K) ⟶ C),
      topologicalKrullDim (pullback h c : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (hN : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ Z) N)
    (r : ℤ) (hr : 2 * (e : ℤ) + 2 < r) :
    IsZero ((DerivedCategory.homologyFunctor _ r).obj
      ((condensedModuleSections Λ Z).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj N))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
