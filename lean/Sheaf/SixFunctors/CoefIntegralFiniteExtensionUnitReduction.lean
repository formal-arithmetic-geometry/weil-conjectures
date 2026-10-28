/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore

/-! Finite reduction of the multiplication unit on a dualizing object. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

/-- The multiplication unit satisfies each defining finite dualizing square.
Source: current blueprint lem-coef-integral-finite-extension, final paragraph,
unit equations transported from the finite comparisons.
(blueprint: lem-sf-integral-finite-extension-unit-reduction)

Proof: expand quotient into the inverse completion comparison, the finite
reduction comparison and the coefficient tensor square. Naturality of the
finite-reduction comparison cancels the completion factors against those
in unit. The identity coefficient map acts as identity on every quotient.
The finite exceptional comparison is the adjunction transpose of scalar
extension of its counit, hence equals the multiplication unit by the
adjunction triangle identities. Its realization on the pro-etale site
preserves that normalization. Substitute this identity into the tensor
square. What remains is naturality of the multiplication unit with respect
to (wE.reduction n).hom. This is a calculation at one finite level; it
uses neither reconstruction nor detection of integral morphisms. The same
calculation covers n=0, a zero dualizing object, and empty X. -/
theorem unit_dualizing_reduction
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (wE : DualizingDatum l X D hl E)
    (n : ℕ) :
    (scalarReductionDerivedExtension l E X n).map
        (unit l E X wE.omega.obj wE.omega.property.1).hom ≫ (wE.reduction n).hom =
      (quotient l E E (AlgHom.id (Padic l) E) X n
          wE.omega.obj wE.omega.property.1).hom ≫
        (pbcDerivedExtend (integralScalarQuotientSheafMap l E E
          (AlgHom.id (Padic l) E) X n)).map (wE.reduction n).hom ≫
        finiteU l E E (AlgHom.id (Padic l) E) X D n := by sorry

end WeilConjectures.IntegralFiniteExtension
