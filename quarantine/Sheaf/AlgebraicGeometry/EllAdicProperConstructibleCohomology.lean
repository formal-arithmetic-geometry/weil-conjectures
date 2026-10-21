/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C5
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
import Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.Paper.CondensedQcqsPushforwardContinuity
import Sheaf.Paper.IntegralConstructibleSerre

/-!
# Constructibility of proper ell-adic direct-image cohomology

This is the constructibility assertion of proper finiteness, separated from the
uniform cohomological-dimension estimate.
(blueprint: lem-sfb-noetherian-proper-constructible-cohomology)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Every cohomology module of the proper direct image of a bounded constructible
ell-adic complex is constructible, over a Noetherian base.

Source: Bhatt--Scholze, Theorem 6.7.1, Lemma 6.7.2 and Remark 6.8.15;
blueprint sk-thm-sfb-proper-base-change,
integral and rational proper finiteness, constructibility clauses.
(blueprint: lem-sfb-noetherian-proper-constructible-cohomology)

Proof: first place a constructible module in degree zero. For integral coefficients,
its derived reductions modulo powers of a uniformizer are constructible torsion
complexes. Proper torsion finiteness makes their higher direct images constructible;
proper base change identifies the reductions and their transition maps. Derived
completeness and the compatible finite presentations on a common finite stratification
recover finitely presented integral local models for each cohomology sheaf. For finite
rational coefficients choose integral lattices on the strata. Proper pushforward
commutes with inverting ell by bounded-below qcqs continuity. The integral result,
localization and extension by zero therefore give constructibility. For condensed
Qlbar the finitely many local models descend to a common finite coefficient field;
finite coefficient extension and bounded-below continuity identify the scalar-extended
proper images. This proves the assertion for a constructible heart object. The
constructible modules over each of these coefficient rings are closed under kernels,
cokernels and extensions on a Noetherian scheme. Induction on the finite cohomological
interval of K, using its good-truncation triangles, then proves the same assertion
for K: in every degree the middle cohomology of the image triangle is an extension
of a cokernel by a kernel of constructibles. All steps are local on the target and
use proper finiteness over a Noetherian base, without a finite-type structure map to k.
The zero complex and empty strata are included.
-/
theorem properLowerStar_constructible_cohomology_ellAdic
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [IsEllAdicFinitenessCoefficient ℓ Λ]
    {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
    {Z Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    (hK : boundedConstructible (condensedRingObj Λ Z) K) :
    ∀ q : ℤ, IsConstructibleModuleObject (condensedRingObj Λ Y)
      ((DerivedCategory.homologyFunctor _ q).obj (R((p)_*⟦Λ⟧).obj K)) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
