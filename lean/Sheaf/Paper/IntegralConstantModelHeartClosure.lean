/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.AdicStratifiedPerfect
import Sheaf.Paper.IntegralCohomologicalAdicCriterion

/-!
# Integral constant-model constructible heart closure

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(1), printed pp. 60--61
(blueprint: lem-sfb-integral-constant-model-heart-closure).

The theorem states closure under ambient kernels, cokernels, and short exact extensions
for finite constant scalar models over the pulled-back condensed ring of integers.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Integral scalar-constant constructible module sheaves form a weak Serre subcategory.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(1), printed pp. 60--61
(blueprint: lem-sfb-integral-constant-model-heart-closure).

Proof: identify the finite constant scalar-model convention with the completed adic model
over the valuation ring of the finite coefficient field.  The adic stratified-perfect
criterion gives closure under cones, so the cone of a map between degree-zero objects has
constructible cohomology equal to its kernel and cokernel.  The same criterion applied to
the degree-zero triangle associated to a short exact sequence gives extension closure.
The coefficient comparison preserves scalar matrices and restrictions to strata, and the
Noetherian hypothesis is exactly quasi-compactness together with local Noetherianity.
-/
theorem isConstantModelConstructible_serre_padicIntegers
    (X : Scheme.{u}) [IsNoetherian X] (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) :
    (∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)) (f : M ⟶ N),
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X M →
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X N →
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X (kernel f) ∧
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X (cokernel f)) ∧
    (∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)),
      S.ShortExact →
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X S.X₁ →
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X S.X₃ →
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X S.X₂) := by
  sorry

end AlgebraicGeometry.ProEtale
