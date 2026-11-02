/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedExchange
import WeilConjectures.AlgebraicGeometry.Open.OpenDirectImageFiniteCoefficients
import WeilConjectures.AlgebraicGeometry.OpenDirectImageFieldBaseChange
import WeilConjectures.AlgebraicGeometry.ModuleLocalConstancyOfFiniteUnderlying
import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
import WeilConjectures.AlgebraicGeometry.NoetherianGlobalConstructibility
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Data.ZMod.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Mathlib.Algebra.CharP.Basic
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Open direct image over a field with finite primary coefficients

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/
sec-generic-constructibility-of-direct-image-along-an-open-immersion/
sk-cor-geo-open-finiteness/_section.md and sk-cor-geo-open-finiteness.proof.md,
corollary (7.22) and its proof (blueprint: sk-cor-geo-open-finiteness).

Finite discrete coefficients are the continuous condensed ring, pulled back to each
scheme. Bounded constructibility and the ordinary derived operations are the recorded
module-object constructions. Base change uses the actual mate-based exchange.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Open direct image preserves bounded constructibility with finite primary coefficients
and its canonical exchange is invertible after finite-type base change over the field.

Source: blueprint part-six-operations/sec-constructibility-upper-shriek/
sec-generic-constructibility-of-direct-image-along-an-open-immersion/
sk-cor-geo-open-finiteness, corollary (7.22) and its proof
(blueprint: sk-cor-geo-open-finiteness).

Proof plan, following the four DAG steps:
1. Finite type over the field makes the schemes Noetherian and qcqs; the finite coefficient
ring is Noetherian, and finite, finitely generated and finitely presented modules agree.
Use lem-sfb-noetherian-global-constructibility and sk-thm-pe-constructible-comparison to
represent K by a bounded constructible etale complex and to transport constructibility back.
2. On each stratum finite locally constant underlying modules are locally constant with
coefficients by lem-pod-module-local-constancy-of-finite-underlying. Thus forgetting the
finite coefficient action detects constructibility, also for the ell-killed quotients.
3. Apply thm-fin-deligne-generic-open with S = Spec k: its nonempty open is the whole base.
Filter by powers of ell, using thm-constructible-serre for the terms and quotients.
Long exact sequences preserve bounded constructibility, and maps of triangles preserve
exchange isomorphisms. Use lem-sbc-canonical-restrict-scalars-functor-comparisons for the
coefficient action. Finite truncation triangles give the complex statement, assembled in
cor-fin-deligne-open-finite-coefficients and det-geo-open-finiteness-base-change.
4. Transport direct image through sk-thm-pe-direct-image-comparison. Its compatibility
with units, counits and inverse-image composition identifies the actual pro-etale exchange
with the pullback of the etale exchange; it is therefore invertible. Naturality transports
this along the chosen etale realization of K. No completion or Tor bound is imposed. -/
theorem openDirectImage_field_finiteness_and_baseChange
    (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k)
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (r : ℕ) (hr : 1 ≤ r) (hA : (ℓ ^ r : A) = 0)
    {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (j : X ⟶ Y) [IsOpenImmersion j] (hj : j ≫ aY = aX)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) X)))
    (hK : constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) X K) :
    constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) Y
        ((CondensedRing.moduleObjectDerivedPushforward
          (Profinite.continuousCoefficientRingObj A) j).obj K) ∧
      ∀ (T : Over (Spec (.of k))),
        LocallyOfFiniteType T.hom → QuasiCompact T.hom → IsSeparated T.hom →
        IsIso ((CondensedRing.moduleObjectDerivedExchange
          (Profinite.continuousCoefficientRingObj A)
          (CommSq.mk ((baseChange_morphism_projections
            (Over.homMk j hj : Over.mk aX ⟶ Over.mk aY) T).1.symm))).app K) := by
  sorry

end AlgebraicGeometry.ProEtale
