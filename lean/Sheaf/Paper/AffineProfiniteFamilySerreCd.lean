/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.EtaleFieldGsets
import Sheaf.RingTheory.StrictHenselizationPresentationIn
import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.RingTheory.Etale.QuasiFiniteAtPrime
import WeilConjectures.RingTheory.Etale.LocalDimension
import Sheaf.AlgebraicGeometry.DimensionExtension
import Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine
import Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.AffineSepclosedEtaleAcyclic
import Sheaf.AlgebraicGeometry.ExactGlobalSectionsLeray

/-! # An affine cohomology bound over a profinite geometric base

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph, affine-local input
(blueprint: lem-sfb-affine-profinite-family-serre-cd).

The affine torsion argument is motivated by Stacks Tag 0F0V. The final transfer to
ordinary continuous topological coefficients is a separate, still open source obligation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Affine finite-type families over reduced zero-dimensional w-contractible bases
with separably closed residue fields have ordinary module-object cohomology zero above
`e + 2` on the weak Serre coproduct closure of finite constant-model constructible modules.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph; agent-formulated affine
obligation, motivated on the torsion branch by Stacks Tag 0F0V. An exact reference for
the full topological-coefficient transfer remains wanted
(blueprint: lem-sfb-affine-profinite-family-serre-cd).

Proof plan (the six steps of the DAG node):
1. Write R = Gamma(C, O_C). Each R_c is reduced with its maximal ideal as its only prime,
so this ideal is zero and R_c is the separably closed field kappa(c). The pointed-etale
colimit defining its strict henselization is the field itself: use the selected factor
of each pointed etale algebra, by lem-exc-etale-field-gsets and def-sc-ring-strict-henselization.
The affine strict-local comparison lem-exc-affine-strict-local-ring-comparison identifies
C_(c-bar) with Spec kappa(c), without identifying the latter with an algebraic closure.
2. For every affine etale V -> U, its coordinate map is finite type by
lem-weil-pbc-etale-ring-map-quasi-finite. Thus V -> C is finite type. By etale base change
and lem-sc-etale-local-dimension, each geometric fibre has dimension at most e.
Affineness makes V -> C quasi-compact and separated, hence quasi-separated.
3. By lem-kun-dimension-extension, the ordinary fibre V_c has dimension at most e.
Its separably closed base field has torsion dimension zero by
lem-sf-separably-closed-torsion-cd. Apply thm-sc-affine-torsion-cd to obtain vanishing
above e for every torsion abelian etale sheaf on V_c, including the empty fibre.
4. For a torsion etale sheaf F on V, apply prop-weil-pbc-strict-henselization-stalk-formula
to V -> C. Step 1 identifies its strict-local fibre with V_c; Step 3 kills the stalks
of every higher direct image above e. Apply lemma-weil-pbc-geometric-stalk-conservative
to conclude that those higher direct images vanish.
5. Every point of C is closed and its residue field is separably closed. By
lem-cbc-affine-sepclosed-etale-acyclic, global sections on its etale site are exact.
The identification def-weil-pbc-exact-global-sections-leray now gives zero cohomology
above e on every affine etale V -> U for every torsion abelian etale sheaf.
6. Apply lem-sfb-torsion-cd-topological-serre-transfer with X = U and d = e to precisely
the uniform torsion hypothesis just proved. Its coefficient choices, all-continuous-map
norm topology on Omega, ordinary internal modules, constant-model generators and
weak Serre coproduct closure are the same as here. It yields the cutoff e + 2.
This is an independent coefficient theorem, not an application of torsion vanishing
to non-torsion coefficients. The transfer includes the empty scheme and zero ring.
-/
theorem affine_profinite_family_serreHeart_cohomology_vanishes
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
    {C U : Scheme.{u}} [IsAffine C] [IsReduced C] [IsAffine U]
    [IsWContractibleRing Γ(C, ⊤)]
    (hCdim : ∀ p : PrimeSpectrum Γ(C, ⊤), p.asIdeal.IsMaximal)
    (hCres : ∀ c : C, IsSepClosed (C.residueField c))
    (g : U ⟶ C) [LocallyOfFiniteType g] [QuasiCompact g] (e : ℕ)
    (he : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (c : Spec (CommRingCat.of K) ⟶ C),
      topologicalKrullDim (pullback g c : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (hN : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ U) N)
    (r : ℤ) (hr : (e : ℤ) + 2 < r) :
    IsZero ((DerivedCategory.homologyFunctor _ r).obj
      ((condensedModuleSections Λ U).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj N))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
