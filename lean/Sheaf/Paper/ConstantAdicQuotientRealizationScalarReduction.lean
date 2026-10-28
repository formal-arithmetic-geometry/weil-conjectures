/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G9
-/
module

public import Sheaf.Paper.ConstantAdicQuotientScalarComparison
public import Sheaf.Paper.ConstantRealizationDerivedScalarExtension

/-! # Scalar restriction of consecutive constant quotient realizations

This is the coefficient comparison substep of the consecutive quotient
realization argument.  It contains no tower model or supplied model
isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

/-- Consecutive constant quotient realization commutes with derived restriction.

Source: Stacks Project, proetale.tex, Tags 0D6D and 03Q3, scalar comparison
for consecutive quotient coefficients.  The proof pastes the canonical
constant quotient scalar comparison at the two levels with the derived
constant realization scalar extension comparison; the quotient maps are
identified by completion evaluation.  This statement is the coefficient-only
part of the realization reduction and does not use an adic tower.
(blueprint: lem-weil-pbc-constant-adic-quotient-realization-scalar-reduction).
-/
theorem constantAdicQuotient_realization_scalar_reduction
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (n : ℕ) (W : Y.Etale) (_w : W.left)
    (E' : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1 + 1)))) :
    let q : (AdicCompletion d.ideal A ⧸
        (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1 + 1)) →+*
        (AdicCompletion d.ideal A ⧸
          (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)) :=
      Ideal.Quotient.factor (Ideal.pow_le_pow_right
        (I := d.ideal.map (algebraMap A (AdicCompletion d.ideal A)))
        (Nat.le_succ (n + 1)))
    let Rn := constantAdicQuotientRealization (W.hom ≫ g) d n
    let Rnp := constantAdicQuotientRealization (W.hom ≫ g) d (n + 1)
    let T := pbcDerivedExtend ((adicTowerInverseImage (W.hom ≫ g)).map
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
    Nonempty (Rn.obj ((CategoryTheory.ConstantScalarRealization.moduleDerivedExtension q).obj E') ≅
      T.obj (Rnp.obj E')) := by
  sorry

end AlgebraicGeometry.Scheme
