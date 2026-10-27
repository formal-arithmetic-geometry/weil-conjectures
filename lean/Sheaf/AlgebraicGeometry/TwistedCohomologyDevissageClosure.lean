/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum

/-! # Exact invertible twists and eventual cohomology vanishing

Source: Stacks Project, `coherent.tex`, Tag 0B5V,
lemma-surjective-finite-morphism-ample, verification of conditions (1) and (2)
of Tag 01YM, lemma-property-higher-rank-cohomological.
(blueprint: lem-trf-twisted-cohomology-devissage-closure)
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

/-- A specified bound for vanishing in every positive degree after all larger twists.
This is the witnessing-bound predicate in the definition of `P_L` in Stacks Project,
`coherent.tex`, Tag 0B5V, proof of lemma-surjective-finite-morphism-ample.
(blueprint: lem-trf-twisted-cohomology-devissage-closure) -/
def TwistedCohomologyVanishingBound {X : Scheme.{u}} (L E : X.Modules) (b : ℕ) : Prop :=
  ∀ n : ℕ, b ≤ n → ∀ p : ℕ, 1 ≤ p →
    Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace p).obj (E ⊗ L.tensorPow n))

/-- The property `P_L`: a single bound works for all positive cohomological degrees.
On coherent modules this is precisely the property used in Stacks Project,
`coherent.tex`, Tag 0B5V, proof of lemma-surjective-finite-morphism-ample.
(blueprint: lem-trf-twisted-cohomology-devissage-closure) -/
def HasEventualTwistedCohomologyVanishing {X : Scheme.{u}} (L E : X.Modules) : Prop :=
  ∃ b : ℕ, TwistedCohomologyVanishingBound L E b

/-- Invertible twists are additive and exact, and their cohomology is additive, has long
exact sequences, and preserves finite sums. Eventual positive cohomology vanishing holds
for zero, is closed under coherent extensions with the maximum bound, and descends from
a nonempty finite sum of copies with the same bound. Finite sums of coherent modules,
including the empty sum, are coherent. Finite direct sums are written as coproducts `∐`.

Source: Stacks Project, `coherent.tex`, Tag 0B5V,
lemma-surjective-finite-morphism-ample, conditions (1) and (2) of Tag 01YM,
lemma-property-higher-rank-cohomological; Modules, Tag 01BY.
(blueprint: lem-trf-twisted-cohomology-devissage-closure)

Proof:
1. Induct on the power, starting with the structure module. Tensor products of invertible
modules are invertible by lem-pc-tensor-dual-invertible. Each power is finite locally free
of rank one. By lem-sc-ext-tensor-exact, left tensoring is exact; symmetry and additivity
from lem-pc-sheaf-modules-tensor-closed give exact, additive right tensoring.
2. The module category is abelian with enough injectives by
lem-sc-ringed-space-module-sheaves-enough-injectives. Global sections is additive and left
exact by lem-sc-global-sections-left-exact. Apply
lem-weil-pbc-right-derived-universal-delta-functor and then the exact twist. This gives
additive degree functors and the long exact sequence, with the degree functors equal to
the stated composites of tensoring and RingedSpace.moduleCohomology.
3. Additivity preserves the finite-sum inclusion/projection identities, so cohomology
preserves finite direct sums. On zero its identity is zero, so its value is zero;
the bound zero witnesses the property of the zero module.
4. For bounds b₁ and b₂, take n at least max b₁ b₂ and p at least one. The long exact
sequence has zero groups on both sides of the middle H^p, so that group is zero.
The maximum is independent of p and therefore witnesses the middle term's property.
5. Clause (3) of lem-weil-pbc-coherent-modules-kernel-cokernel-sum gives coherence of
finite sums, including zero for the empty sum.
6. If r is positive, choose one inclusion into the sum of r copies and its projection.
Their composite is the identity. Applying the twisted cohomology functor gives a retract.
When the sum's cohomology is zero, the identity of the retract factors through zero,
so the retract is zero. This works for every n and p with the original witnessing bound.
-/
theorem twistedCohomology_devissage_closure (X : Scheme.{u}) [IsLocallyNoetherian X]
    (L : X.Modules) [L.IsInvertible] :
    (∀ n : ℕ, (L.tensorPow n).IsInvertible ∧
      (tensorRight (L.tensorPow n)).Additive ∧
      PreservesFiniteLimits (tensorRight (L.tensorPow n)) ∧
      PreservesFiniteColimits (tensorRight (L.tensorPow n)) ∧
      (∀ p : ℕ,
        (tensorRight (L.tensorPow n) ⋙ RingedSpace.moduleCohomology X.toRingedSpace p).Additive ∧
        ∀ r : ℕ, PreservesColimitsOfShape (Discrete (Fin r))
          (tensorRight (L.tensorPow n) ⋙ RingedSpace.moduleCohomology X.toRingedSpace p)) ∧
      ∃ G : CohomologicalDeltaFunctor X.Modules
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))),
        G.F = fun p : ℕ ↦
          tensorRight (L.tensorPow n) ⋙ RingedSpace.moduleCohomology X.toRingedSpace p) ∧
    HasEventualTwistedCohomologyVanishing L (0 : X.Modules) ∧
    (∀ (S : ShortComplex X.Modules), S.ShortExact →
      RingedSpace.IsCoherent X.toRingedSpace S.X₁ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₂ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₃ →
      ∀ b₁ b₂ : ℕ, TwistedCohomologyVanishingBound L S.X₁ b₁ →
        TwistedCohomologyVanishingBound L S.X₃ b₂ →
        TwistedCohomologyVanishingBound L S.X₂ (max b₁ b₂)) ∧
    (∀ (r : ℕ) (E : Fin r → X.Modules),
      (∀ i : Fin r, RingedSpace.IsCoherent X.toRingedSpace (E i)) →
      RingedSpace.IsCoherent X.toRingedSpace (∐ E)) ∧
    (∀ (E : X.Modules), RingedSpace.IsCoherent X.toRingedSpace E →
      ∀ r : ℕ, 1 ≤ r → ∀ b : ℕ,
        TwistedCohomologyVanishingBound L (∐ fun _ : Fin r ↦ E) b →
        TwistedCohomologyVanishingBound L E b) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
