/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H5
-/
module

public import Sheaf.Paper.ConstantAdicQuotientScalarComparison

/-! # Algebraic isomorphism extracted from a constant adic quotient realization -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

/-- The point-stalk extraction step underlying the homology-level lift.

Source: Stacks Project, sites-modules.tex, Tags 093J and 03DH; proetale.tex,
Tag 03Q3.
(blueprint: lem-weil-pbc-constant-adic-quotient-realization-iso-lift).

Proof: transport the realized isomorphism across the canonical completion
quotient comparison and the inverse-image/constant-section comparison.  Evaluate
at the supplied point of the etale chart.  The stalk of a constant quotient
module is its coefficient module, so the evaluated isomorphism determines an
algebraic morphism between the two derived coefficient objects.  Exactness of
the stalk functor and the nonempty-chart constant-section detection show that
this morphism is an isomorphism.  The transport is natural in the derived
objects, so the same morphism is obtained before evaluation.  This is the
strictly smaller extraction statement; the homology conclusion is supplied by
`DerivedCategory.isIso_iff` in the parent theorem.
-/
theorem constantAdicQuotientRealization_iso_lift
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (W : Y.Etale) (_w : W.left)
    (E F : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (h : Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
      (constantAdicQuotientRealization (W.hom ≫ g) d n).obj F)) :
    ∃ f : E ⟶ F, IsIso f := by
  sorry

end AlgebraicGeometry.Scheme
