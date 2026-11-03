/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientIntrinsicTensor
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumCoefficientComputation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat

/-! # Finite quotient reduction with its canonical constructible origin

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction.proof.md, first paragraph and final associativity sentence;
lem-sf-reduction-flat-model and its proof.
(blueprint: lem-pur-finite-reduction-constructibility).

All scalar functors are actual derived extensions. The comparison is fixed by the
local tensor formula and the derived counits, rather than supplied as an extra hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.FiniteQuotientReduction

variable {ell : ℕ} [Fact ell.Prime]

/-- The ordinary pure scalar tensor, inserted through the actual sheafification unit.
Source: Stacks 03EL, blueprint flat-model computation
(blueprint: lem-pur-finite-reduction-constructibility). -/
def pureExtension (T : Scheme.{u}) {r m : ℕ}
    (f : Ring.{u} ell r →+* Ring.{u} ell m)
    (M : Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T (Ring ell r)))
    (V : T.ProEtᵒᵖ)
    (s : (Scheme.proEtaleConstantRing T (Ring ell m)).obj.obj V) (x : M.val.obj V) :
    ((Scheme.siteScalarChange T (Scheme.proEtaleConstantRingMap (T := T) f)).obj M).val.obj V :=
  (eqToHom (Scheme.siteScalarChange_obj_eq T
    (Scheme.proEtaleConstantRingMap (T := T) f) M).symm).val.app V
      (((PresheafOfModules.sheafificationAdjunction.{u + 1}
        (R := (sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (Scheme.proEtaleConstantRing T (Ring ell m))) (𝟙 _)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
          (Scheme.proEtaleConstantRingMap (T := T) f) M)).app V
            (s ⊗ₜ[_, ((Scheme.proEtaleConstantRingMap (T := T) f).hom.app V).hom] x))

end AlgebraicGeometry.FiniteQuotientReduction
