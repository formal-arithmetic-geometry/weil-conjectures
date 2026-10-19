/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteDualityMaps

/-! # Ordinary evaluation for bounded finite-projective complexes

Source: Stacks Project, Tag 08JJ (blueprint: lem-sfb-ordinary-perfect-evaluation).
-/

@[expose] public section
set_option autoImplicit false
universe c v r w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Ordinary total evaluation from a bounded finite-free-retract complex is an isomorphism.
Source: Stacks Project, sites-cohomology.tex, Tag 08JJ, final paragraph.
Proof: the degree q term of D=Hom(E,O[0]) is Hom(E^(-q),O). In total degree n,
only the finite interval supporting E contributes. Projection of the specified
ordinary evaluation to its a-th Hom factor is zero off q=-a and is the canonical
module evaluation F^(a+n) tensor Hom(E^a,O) to Hom(E^a,F^(a+n)) on that summand.
For a finite free term its inverse is the finite dual-basis formula
h maps to sum_j h(t_j) tensor lambda_j. The same assertion for a retract follows
by naturality and retract stability of isomorphisms. Consequently the finite
sum-to-product diagonal map is invertible in every degree. The specified ordinary
evaluation is already a chain map, so its degreewise inverses give a chain
isomorphism. Empty support intervals, zero ranks and zero coefficient rings use
the same finite formulas. There is no boundedness condition on F.
(blueprint: lem-sfb-ordinary-perfect-evaluation). -/
theorem ringedSiteOrdinaryEvaluation_isIso
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (K : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n))
    (pkg : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ K)
    (F : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    IsIso (ringedSiteOrdinaryEvaluation.{c, v, r} J R K F) := by sorry

end CategoryTheory
