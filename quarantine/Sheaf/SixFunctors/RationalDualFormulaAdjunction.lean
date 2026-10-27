/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.SixFunctors.RationalOperationsData
public import Sheaf.SixFunctors.CoefDualFormulaScalarTranspose

/-! # The normalized adjunction for the rational dual formula

Source: the exceptional-adjunction and coefficient-localization argument in
lem-coef-rational-operations, steps 10--11
(blueprint: lem-sf-rational-dual-formula-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalOperations
open ConstructibleExceptionalCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f) (F : FieldStage.{u} l)
  (wX : IntegralFiniteExtension.DualizingDatum l X D hl F.carrier)
  (wY : IntegralFiniteExtension.DualizingDatum l Y D hl F.carrier)
  (A : RationalVerdier.Datum D l hl X F.carrier wX)
  (B : RationalVerdier.Datum D l hl Y F.carrier wY)

/-- The integral representative of the dual-pullback-dual functor, using the supplied
duality presentations and the prescribed completed pullback.
Source: lem-coef-rational-operations, step 11
(blueprint: lem-sf-rational-dual-formula-adjunction). -/
abbrev integralDualFormula :=
  (IntegralVerdier.restrictedDual l F.carrier Y wY.omega.obj B.preserves).rightOp ⋙
    (@constructibleIntegralPullback l _ F.carrier _ _ _ X Y f
      (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).op ⋙
    IntegralVerdier.restrictedDual l F.carrier X wX.omega.obj A.preserves

/-- The counit is the localization of the integral counit whose trace/evaluation
characterization makes the identity the integral formula comparison. This pins the
adjunction independently of any exceptional coefficient system or comparison isomorphism.
Source: lem-coef-rational-operations, steps 10--11, and the canonical integral formula
(blueprint: lem-sf-rational-dual-formula-adjunction). -/
def DualFormulaAdjunctionNormalized
    (adj : sfCompactSupportFiniteFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier ⊣
        dualFormula l X D hl (f := f) F wX wY A B) : Prop :=
  ∃ aZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (completedIntegralCommRingSheafUnrestricted l F.carrier c.Z),
    ∃ adjI : sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier ⊣
          integralDualFormula D l hl X F wX wY A B,
      (∀ M : sfIntegralConstructibleCategory l F.carrier Y,
        CoefDualFormulaScalarTranspose.FormulaNormalized D l hl F.carrier f c
          wX wY A.ordinary aZ B.ordinary A.symmetry
          (integralDualFormula D l hl X F wX wY A B) adjI M (Iso.refl _)) ∧
      ∀ M : sfIntegralConstructibleCategory l F.carrier Y,
        HEq (adj.counit.app ((sfRationalConstructibleLocalization l F.carrier Y).obj M))
          ((sfRationalConstructibleLocalization l F.carrier Y).map (adjI.counit.app M))

/-- The dual formula has an adjunction with its trace-normalized, localized counit.
This assertion concerns one coefficient field and does not choose an isomorphism from
the right adjoint of a coefficient system.
Source: lem-coef-rational-operations, steps 10--11
(blueprint: lem-sf-rational-dual-formula-adjunction).

Proof: use the supplied coefficient system for its integral exceptional adjunction
at the fixed compactification. The theorem
integral_residue_tor identifies its finite-Tor integral categories with the entire
integral constructible categories. Transport across these full-category equivalences
and integralLeft to obtain an adjunction for the prescribed integral compact support.
For the supplied dualizing objects, use the canonical integral dual formula.
Its components are characterized by FormulaNormalized: evaluate into omega_X, apply
the ordinary projection map and the quotient-normalized completion augmentation, and
then apply the relative structural trace. Currying and the inverse biduality map give
the inverse Hom bijection, so these components are natural isomorphisms. Transport the
integral exceptional adjunction along that isomorphism. The identity now satisfies
FormulaNormalized for the transported adjunction. Choose the ordinary derived tensor
presentation on c.Z; its representative normalization makes the projection map the same
one used in this characterization. The integral Hom bijection is O_F-linear, since
both dualities and completed pullback are linear. Tensor it and its inverse with the
fraction field. Objects are unchanged; the triangle equations localize, giving a
rational adjunction. The object and pure-map equations in A and B identify its right
functor with the stated dualFormula, and the coefficient-passage definition identifies
its left functor with the stated compact support. Its counit on an integral object is
the integral counit tensored with one, which is exactly the displayed HEq. Empty schemes,
zero objects and torsion objects require no change to these constructions. -/
theorem rationalDualFormulaAdjunction_exists
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (S : System l Ω D hl (f := f)) :
    ∃ adj : sfCompactSupportFiniteFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier ⊣
          dualFormula l X D hl (f := f) F wX wY A B,
      DualFormulaAdjunctionNormalized D l hl X c F wX wY A B adj := by sorry

end WeilConjectures.RationalOperations
