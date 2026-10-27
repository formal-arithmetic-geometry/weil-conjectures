/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.Paper.ConstantAdicQuotientScalarComparison
import Sheaf.CategoryTheory.ConstantRealizationReflectsIsomorphism

/-! # Homology-level lift from a constant adic quotient realization -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

/-- A realized isomorphism on a nonempty etale chart admits an algebraic
morphism whose cohomology maps are all isomorphisms.

Source: Stacks Project, sites-modules.tex, Tags 093J and 03DH; proetale.tex,
Tag 03Q3.
(blueprint: lem-weil-pbc-constant-adic-quotient-realization-homology-lift).

Proof: transport the realized isomorphism through the canonical completion
quotient comparison and the inverse-image/constant-section comparison.  Choose
the supplied point of the etale chart and apply the exact geometric stalk
functor.  The stalk of a constant quotient module is the corresponding
coefficient module, so the stalked isomorphism descends to a morphism of the
algebraic derived objects.  Exactness identifies its stalked cohomology maps
with the original realized maps; the nonempty point and constant-section
detection make each of these maps invertible.  The construction is natural in
roofs, hence gives one morphism whose every cohomology map is an isomorphism.
No boundedness or finiteness assumption is used.
-/
theorem constantAdicQuotientRealization_homology_lift
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (W : Y.Etale) (_w : W.left)
    (E F : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (h : Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
      (constantAdicQuotientRealization (W.hom ≫ g) d n).obj F)) :
    ∃ f : E ⟶ F, ∀ i : ℤ,
      IsIso ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
          (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))) i).map f) := by
  sorry

end AlgebraicGeometry.Scheme
