/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.RationalVerdierModels

/-! # K-flat part of the rationalization of an integral Verdier conclusion

This is the coefficient-localization part of the rational Verdier construction. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Localizing a fixed integral Verdier conclusion supplies the rational datum and the
Koszul naturality equation on K-flat representatives. Passing from this representative
equation to arbitrary derived maps is a separate descent step.
Source: blueprint thm-coef-rational-verdier, proof steps 2--5
(blueprint: lem-coef-rational-verdier-datum-kflat).

Proof: retain the integral tensor presentation and its signed representative, localize
the internal-Hom maps on pure tensors, and extend by additivity over the raw scalar
localization. Localized distinguished triangles give exactness and localized integral
delta gives the actual biduality isomorphism. The normalized completion comparison is
transported through the ordinary presentation; its naturality transports evaluation.
The Koszul representative formula is natural for K-flat chain maps; this theorem records
only that representative equation. -/
theorem datum_of_integral_kflat
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (h : IntegralVerdier.Conclusion l E X D hl wE.omega wE.reduction) :
    ∃ A : Datum D l hl X E wE,
      ∀ (P P' Q Q' : CochainComplex (IntegralHom.Modules.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X)) ℤ)
        (hP : IntegralHom.flat.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X) P)
        (hP' : IntegralHom.flat.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X) P')
        (hQ : IntegralHom.flat.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X) Q)
        (hQ' : IntegralHom.flat.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X) Q')
        (f : P ⟶ P') (g : Q ⟶ Q'),
        A.ordinary.tensor.map (Prod.mkHom (DerivedCategory.Q.map f)
          (DerivedCategory.Q.map g)) ≫
            (A.symmetry.swap (DerivedCategory.Q.obj P') (DerivedCategory.Q.obj Q')).hom =
          (A.symmetry.swap (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
            A.ordinary.tensor.map (Prod.mkHom (DerivedCategory.Q.map g)
              (DerivedCategory.Q.map f)) := by
  sorry

end WeilConjectures.RationalVerdier
