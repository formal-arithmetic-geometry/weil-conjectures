/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.NoetherianSpace

import WeilConjectures.AlgebraicGeometry.LocallyFreeTensorSingle
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import all WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import WeilConjectures.AlgebraicGeometry.IntegralLfpLocallyFreeResolution
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-! # Local tensor calculations over ell-adic coefficients

Source: Bhatt--Scholze, Proposition 6.8.11(3), using locally finite free resolutions.
(a step of blueprint `lem-sfb-dc-tensor-preserves`)
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj ZeroObject
open CategoryTheory Limits MonoidalCategory MonObj Opposite Pretriangulated
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory.TStructure.t

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]

/-- The tensor of two locally finitely presented `ℚ̄_ℓ`-module sheaves has no cohomology below
degree -1, and its cohomology is locally finitely presented.
Source: Bhatt--Scholze, Proposition 6.8.11(3).
Proof: local triviality makes the first factor locally finite free, so the finite free tensor
calculation gives the assertion (and a stronger lower bound 0).
(a step of blueprint `lem-sfb-dc-tensor-preserves`) -/
theorem lfp_tensor_single_padicAlgClRingObj
    (F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hF : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) F)
    (hG : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) G) :
    ((DerivedCategory.singleFunctor _ 0).obj F ⊗
      (DerivedCategory.singleFunctor _ 0).obj G).IsGE (-1) ∧
    ∀ n : ℤ, IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((DerivedCategory.singleFunctor _ 0).obj F ⊗
        (DerivedCategory.singleFunctor _ 0).obj G)) := by
  obtain ⟨hb, hl⟩ := locallyFree_tensor_single _ X F G (algcl_lf ℓ X F hF) hG
  have := hb
  exact ⟨DerivedCategory.TStructure.t.isGE_of_ge _ (-1) 0 (by decide), hl⟩

end AlgebraicGeometry.ProEtale.CondensedRing
