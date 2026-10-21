/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q6
-/
module

public import Sheaf.SixFunctors.IntegralOpenReductionComparison
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Completeness of ordinary open restriction

Source: Stacks Project, Tags 08TC and 0941; immersion completed-pullback comparison.
The statement keeps independent universes for sites and coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralOpenReduction
namespace WeilConjectures.OpenRestrictionCompleteness

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : Operations l E j)

/-- Ordinary open restriction preserves quotient-tower completeness, and its actual
completion unit is invertible on every such restriction.
Source: the open case of lem-sf-immersion-completed-pullback-comparison, Stacks
sites-cohomology.tex Tags 08TC, 0941, 07A4 and 0G7E.
(blueprint: lem-sf-open-restriction-completeness).

Proof: regard the open immersion as an immersion with identity closed factor.
Use the fixed coefficient maps and their quotient-projection equations to identify
ordinary open restriction with the immersion's exact ringed-site pullback. Restrict
one flat-term K-flat representative: exact restriction preserves its flat terms
and K-flatness. The quotient tensor identifications commute with every transition
and the scalar-unit augmentation. Restriction preserves the products in its Roos
triangle. Consequently the restricted augmented quotient triangle is the target
quotient triangle, which proves completeness. The completion comparison on this
good representative identifies its actual completion unit with the quotient
augmentation into the Roos complex. The distinguished quotient triangle makes
this map invertible. Transport along the representative isomorphisms by naturality
of the unit. All identifications use the fixed coefficient-equivalence units and
counits, so the result holds for the given operations. The empty open has the zero
module category; the identity open gives the original quotient triangle. -/
theorem openRestrictionComplete
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : U, Invertible (l : U.residueField x)] :
    ∀ H, complete l E X H →
      complete l E U ((star l E j o).obj H) ∧
      IsIso ((IntegralOnSlice.completionUnit l E U none).app
        ((star l E j o).obj H)) := by sorry

end WeilConjectures.OpenRestrictionCompleteness
