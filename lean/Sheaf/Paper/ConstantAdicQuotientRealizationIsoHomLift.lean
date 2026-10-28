/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W5
-/
module

public import Sheaf.Paper.ConstantAdicQuotientScalarComparison

/-! # Morphism lift for a constant adic quotient realization -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

/--
The fullness step in the point-stalk extraction argument: an isomorphism after
constant adic quotient realization has an algebraic morphism with the same
realized arrow.

Source: Stacks Project, sites-modules.tex, Tags 093J and 03DH; proetale.tex,
Tag 03Q3.
(blueprint: lem-weil-pbc-constant-adic-quotient-realization-iso-hom-lift).

Proof: transport the realized isomorphism through the completion quotient
comparison and the inverse-image/constant-section comparison.  The supplied
point of the nonempty etale chart identifies the stalk of each constant
quotient module with its coefficient module.  The induced coefficient-level
morphism is transported back through the natural comparison isomorphisms;
naturality gives an algebraic morphism whose realization is the original
isomorphism.  This is the morphism-extraction part of the argument; the
separate reflection theorem proves that the extracted morphism is invertible.
-/
theorem constantAdicQuotientRealization_iso_hom_lift
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (W : Y.Etale) (_w : W.left)
    (E F : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (e : (constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
      (constantAdicQuotientRealization (W.hom ≫ g) d n).obj F) :
    ∃ f : E ⟶ F,
      (constantAdicQuotientRealization (W.hom ≫ g) d n).map f = e.hom := by
  sorry

end AlgebraicGeometry.Scheme
