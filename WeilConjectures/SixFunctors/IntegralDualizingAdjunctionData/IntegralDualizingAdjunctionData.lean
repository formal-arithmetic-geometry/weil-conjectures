/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralDualizingRoosModel

/-! # Constructible adjunction in the integral dualizing coordinates

Source: current blueprint prop-coef-integral-dualizing, direct adjunction argument.
The record fixes the compact-support functor and coefficient unit up to their explicit
isomorphisms. Its right adjoint is consequently determined up to unique adjoint comparison.
(blueprint: def-coef-integral-dualizing-adjunction-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- A constructible exceptional adjunction with the published compact-support realization.
The unit object is the actual coefficient sheaf in degree zero, rather than an unspecified
coefficient object. No existence assertion or chosen witness is used in this definition.
Source: current blueprint prop-coef-integral-dualizing.proof.md, paragraphs 1--2
(blueprint: def-coef-integral-dualizing-adjunction-data). -/
structure IntegralDualizingAdjunctionData where
  /-- Compact support on the complete constructible categories. -/
  support : sfIntegralConstructibleCategory l E X ⥤
    sfIntegralConstructibleCategory l E (Spec (.of D.k))
  /-- Its constructible right adjoint. -/
  right : sfIntegralConstructibleCategory l E (Spec (.of D.k)) ⥤
    sfIntegralConstructibleCategory l E X
  /-- The ordinary adjunction, retaining its actual unit and counit. -/
  adjunction : support ⊣ right
  /-- Comparison with the specified strict-tower realization, natural on all maps. -/
  supportIso : support ⋙ (sfIntegralConstructible l E (Spec (.of D.k))).ι ≅
    (sfIntegralConstructible l E X).ι ⋙ integralDualizingCompactTower l E D hl X ⋙
      integralDualizingLimit l E (Spec (.of D.k))
  /-- The coefficient unit, as a constructible object. -/
  unit : sfIntegralConstructibleCategory l E (Spec (.of D.k))
  /-- Its identification with the regular coefficient sheaf in degree zero. -/
  unitIso : unit.obj ≅
    (DerivedCategory.singleFunctor (scalarReductionSource l E (Spec (.of D.k))) 0).obj
      (SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))))

variable {D l hl E X}

/-- The adjoint value is independent of all presentations in the record.
Source: uniqueness of right adjoints, applied to the current blueprint's exceptional value
(blueprint: def-coef-integral-dualizing-adjunction-data).
Proof: full faithfulness lifts the support and unit comparisons. Transport one adjunction
along the support isomorphism, compare its right adjoint with the other, and evaluate at
the two isomorphic units. -/
def IntegralDualizingAdjunctionData.valueIso
    (A B : IntegralDualizingAdjunctionData D l hl E X) :
    (A.right.obj A.unit).obj ≅ (B.right.obj B.unit).obj := by
  let e : A.support ≅ B.support :=
    ((sfIntegralConstructible l E (Spec (.of D.k))).fullyFaithfulι.whiskeringRight
      (sfIntegralConstructibleCategory l E X)).preimageIso
        (A.supportIso ≪≫ B.supportIso.symm)
  let a : B.support ⊣ A.right := A.adjunction.ofNatIsoLeft e
  let i : A.right ≅ B.right := a.rightAdjointUniq B.adjunction
  let v : A.unit ≅ B.unit :=
    (sfIntegralConstructible l E (Spec (.of D.k))).fullyFaithfulι.preimageIso
      (A.unitIso ≪≫ B.unitIso.symm)
  exact (sfIntegralConstructible l E X).ι.mapIso
    (i.app A.unit ≪≫ B.right.mapIso v)

/-- The actual degree-zero adjunction in the published ambient coordinates.
Source: current blueprint prop-coef-integral-dualizing.proof.md, last sentence of paragraph 2
(blueprint: def-coef-integral-dualizing-adjunction-data).
Proof: lift the source arrow through the fully faithful constructible inclusion, transpose
under the recorded adjunction, and transport its endpoints by supportIso and unitIso. -/
def IntegralDualizingAdjunctionData.homEquiv
    (A : IntegralDualizingAdjunctionData D l hl E X)
    (K : sfIntegralConstructibleCategory l E X) :
    (K.obj ⟶ (A.right.obj A.unit).obj) ≃
      ((integralDualizingLimit l E (Spec (.of D.k))).obj
        ((integralDualizingCompactTower l E D hl X).obj K.obj) ⟶
          (DerivedCategory.singleFunctor (scalarReductionSource l E (Spec (.of D.k))) 0).obj
            (SheafOfModules.unit
              (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))))) :=
  (sfIntegralConstructible l E X).fullyFaithfulι.homEquiv.symm.trans
    ((A.adjunction.homEquiv K A.unit).symm.trans
      ((sfIntegralConstructible l E (Spec (.of D.k))).fullyFaithfulι.homEquiv.trans
        (Iso.homCongr (A.supportIso.app K) A.unitIso)))

end WeilConjectures
