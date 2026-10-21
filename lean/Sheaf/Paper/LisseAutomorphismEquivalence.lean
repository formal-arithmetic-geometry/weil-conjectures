/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Sheaf.Paper.LisseAdicAutomorphismPullback

/-! # Inverse reindexing for lisse algebraic coefficients

Source: Weil II (1.1.1), (1.1.10); def-wf-lisse-adic-automorphism-pullback.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
open FiniteEtale

variable (l : ℕ) [Fact l.Prime] (Q : Type (u + 1)) [Field Q]
  [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
  {Y : Scheme.{u}} [IsNoetherian Y] [Y.IsSeparated]
  [∀ x : Y, Invertible (l : Y.residueField x)]
  (h : Y ≅ Y)

/-- Actual automorphism pullback remains an equivalence after coefficient localization.
Source: Weil II (1.1.1) b)-d), (1.1.10); the inverse-reindexing clause of
 def-wf-lisse-adic-automorphism-pullback.
(blueprint: new-p6-lisse-automorphism-equivalence)

Proof: reindex with h^-1. The site equivalence
 automorphismEtaleReindexEquivalence supplies the two natural cancellation
isomorphisms, whose underlying scheme maps are identities. Whiskering sheaves
with these isomorphisms gives inverse cancellation maps for finite coefficient
pullback. They preserve local constant finite modules and therefore restrict
to the lisse finite subcategories. Apply these maps at every level of each
integral system. Naturality in the level index gives integral cancellation;
tensoring integral Hom maps with the coefficient field gives rational
cancellation, including all rational arrows by tensor additivity. The scalar
comparisons of automorphismLisseCoefficientTransformation have the identity
formula on pure tensors. It follows on these tensors that both cancellation
maps commute with scalar extension. They therefore give natural isomorphisms
of the Grothendieck coefficient-pair functors. Those functors preserve the
cocartesian coefficient arrows, so the localization universal property descends
the two cancellation isomorphisms to the algebraic category. Their components
on every coefficient pair are the same cancellation maps. The two composites
are the identity by the finite site cancellation and tensor extensionality,
so h^-1 pullback is a quasi-inverse to h pullback. This argument does not
require connectedness or a nonempty scheme. -/
theorem lisseAlgebraicAutomorphismPullback_isEquivalence :
    (lisseAlgebraicAutomorphismPullback h l Q).IsEquivalence := by sorry

end AlgebraicGeometry.Scheme
