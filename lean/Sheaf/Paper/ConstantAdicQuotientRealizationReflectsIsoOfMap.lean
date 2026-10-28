/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W5
-/
module

public import Sheaf.Paper.ConstantAdicQuotientScalarComparison

/-! # Isomorphism reflection for a constant adic quotient realization map -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

/--
The reflection step for the point-stalk extraction argument: a morphism of
derived coefficient objects is an isomorphism when its constant adic quotient
realization is an isomorphism.

Source: Stacks Project, sites-modules.tex, Tags 093J and 03DH; proetale.tex,
Tag 03Q3.
(blueprint: lem-weil-pbc-constant-adic-quotient-realization-reflects-iso-of-map).

Proof: use the completion quotient comparison to move the realized isomorphism
to the coefficient-level constant realization.  Evaluate on the nonempty etale
chart at the supplied point.  Exactness of the stalk functor identifies the
homology of the kernel and cokernel with zero, while constant-section
detection on a nonempty chart makes those objects vanish.  The derived
isomorphism criterion then gives `IsIso` for the original coefficient map.
-/
theorem constantAdicQuotientRealization_reflects_iso_of_map
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (W : Y.Etale) (_w : W.left)
    (E F : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (f : E ⟶ F)
    (hf : IsIso ((constantAdicQuotientRealization (W.hom ≫ g) d n).map f)) :
    IsIso f := by
  sorry

end AlgebraicGeometry.Scheme
