/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.Paper.SupportedImageRigidityFromModelComparisons

/-! # Restriction for supported finite scalar models

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md (2), first paragraph;
steps 2--5 of lem-sfb-supported-three-term-scalar-rigidity.
(blueprint: lem-sfb-supported-finite-model-scalar-rigidity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The actual derived restriction is invertible on a single finite scalar local model
extended along a qcqs open-closed path. This concerns the model itself; images and homology
of arbitrary morphisms between such models are not assumed to have local models.

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md (2), first paragraph;
steps 2--5 of lem-sfb-supported-three-term-scalar-rigidity.
(blueprint: lem-sfb-supported-finite-model-scalar-rigidity).

Proof: For finite discrete coefficients, finite scalar presentations encode finite ordinary
modules. Pro-etale descent makes their local systems classical. Along the support path,
append the complementary zero stratum at every open or closed extension; the quasi-compact
open complements make this a finite constructible stratification. Constructible comparison
therefore realizes the supported model as the pro-etale pullback of a torsion etale module.
Bounded-below site comparison, its pullback coherence and scalar-forgetting comparison
identify the homology maps of the actual restriction with those in ht. They are invertible
in nonnegative degrees by ht; negative degrees vanish. Hence the derived arrow is invertible.
For integral coefficients, the supported integral restriction-tower theorem identifies the
actual arrow with total derived inverse limit of a strict tower of etale restrictions.
Every level is killed by a power of ell, so the same argument using ht makes its restriction
invertible. Exact derived evaluation detects invertibility of the strict tower arrow;
applying derived inverse limit preserves it. Apply the rational transfer theorem to Z_ell
and Q_ell, and to O_E and E for every finite E. The norm-topological algebraic-closure
transfer then supplies the last case. Transport along each displayed coefficient-ring
isomorphism by restriction of scalars, which identifies sections and their actual
restriction units. The zero module, empty schemes and root path give the same constructions
and require no nonvanishing hypothesis. -/
theorem supported_finite_model_scalar_rigidity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
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
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    {T₀ T S : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace T₀] [QuasiSeparatedSpace T₀]
    (t : T₀ ⟶ T) [IsClosedImmersion t]
    (ht : ∀ (F : Sheaf T.smallEtaleTopology Ab.{u + 1}),
      Scheme.IsTorsionAbelianSheaf F → ∀ q : ℕ,
        Function.Bijective (Etale.cohomologyMap t F q))
    (tree : QcqsOpenClosedTree T) (p : tree.Path S)
    (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (hN : HasFiniteConstantLocalModel Λ S N) :
    IsIso ((supportedModelDerivedRestriction Λ t p).app N) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
