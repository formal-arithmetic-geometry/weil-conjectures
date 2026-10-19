/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.TAdmissibleCoefficientModels
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.CoherentRingPerfectComplexCohomology
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingClassicalGenerator
import Sheaf.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels
import Sheaf.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.Paper.WContractibleCondensedScalarEvaluation

/-!
# Truncations and the heart for t-admissible condensed coefficients

Source: Hemo--Richarz--Scholbach, Definition 6.1 and Theorem 6.2(2)
(blueprint: lem-zl-t-admissible-dualizable-truncations).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Standard truncations preserve dualizability, the standard t-structure restricts,
and its heart is exactly the scalar local models. Every cohomology sheaf of a
dualizable object has such models, with no uniform module or amplitude required.

Source: Hemo--Richarz--Scholbach, Definition 6.1 and Theorem 6.2(2)
(blueprint: lem-zl-t-admissible-dualizable-truncations).

Proof for stage 3, following the six steps of the node:
1. Coherence gives finitely presented cohomology of each scalar perfect complex
   (lem-sc-coherent-ring-perfect-complex-cohomology). The finite-projective-resolution
   hypothesis makes those cohomology modules perfect in degree zero. Induct through
   the finite Postnikov tower using shift and cone closure from
   lem-sf-perfect-ring-classical-generator. Both standard scalar truncations are perfect,
   including truncation degrees outside the cohomological support.
2. On the affine weakly contractible basis (sk-thm-pe-weakly-contractible-basis), use
   lem-zl-wcontractible-condensed-scalar-evaluation to evaluate scalar extension as
   tensor with Γ(pi_0 V, Λ). This ring is R-flat by t-admissibility. The kernel,
   image and cokernel calculation of lem-weil-pbc-flat-tensor-exact therefore commutes
   with cohomology and truncation. Use det-pe-sections-conservative to detect the
   comparison isomorphisms. This calculation imposes no component condition on V.
3. Use lem-zl-condensed-dualizable-local-perfect-models to obtain local scalar perfect
   models. Identified-coefficient restriction is exact by lem-sfb-alpha-iso and
   def-weil-pbc-proetale-operations. It commutes with truncation and cohomology.
   Steps 1 and 2 give perfect scalar models of both truncations. Apply the reverse
   local-model criterion on X to obtain dualizability of those ambient truncations.
4. The same local-model theorem makes the dualizable full subcategory stable.
   Intersect the ambient nonpositive and nonnegative parts with it. Orthogonality
   and shift inclusions restrict, and step 3 puts the ambient decomposition triangle
   in the subcategory. This proves precisely the inherited standard t-structure.
5. For a dualizable M[0], take degree-zero cohomology of its local scalar perfect
   models. Step 2 identifies this with Λ tensor the constant H^0 of the scalar model,
   which is finitely presented by the coherent-ring cohomology theorem.
6. Conversely each finitely presented N is perfect in degree zero by hypothesis.
   Step 2 identifies its derived extension with ordinary scalar extension in degree
   zero; the reverse local-model criterion gives dualizability. Truncate a dualizable
   K above and below degree j, then shift to degree zero. Steps 3 and 5 give the
   asserted local models for H^j(K). Zero modules and cover-dependent ranks are allowed. -/
theorem tAdmissible_dualizable_truncations
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (hΛ : IsTAdmissible Λ)
    (X : Scheme.{u}) (hX : HasLocallyFiniteIrreducibleComponents X) :
    (∀ K : LisseAmbient Λ X, dualizableProperty Λ X K → ∀ n : ℤ,
      dualizableProperty Λ X ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
      dualizableProperty Λ X ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
    (∃ h : (dualizableProperty Λ X).IsTriangulated,
      HasRestrictedStandardTStructure Λ X h) ∧
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X),
      dualizableProperty Λ X ((DerivedCategory.singleFunctor _ 0).obj M) ↔
        HasScalarLocalModels Λ X M) ∧
    (∀ K : LisseAmbient Λ X, dualizableProperty Λ X K → ∀ q : ℤ,
      HasScalarLocalModels Λ X ((DerivedCategory.homologyFunctor _ q).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
