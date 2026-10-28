/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierData

/-! # Rational transition omega tower

(blueprint: lem-coef-qbar-finite-omega-transition-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion
  coefficientInclusion_laws)
open GeneralAlgebraicallyClosedCoefficients (Stage stageSystem stageSystem_existsUnique)

/-- The rational transition omega maps obey the scalar associator tower equation.
Source: the composition component of `lem-sf-integral-finite-extension-composition`,
localized through `RationalVerdier.ExtensionProperties`.
(blueprint: lem-coef-qbar-finite-omega-transition-tower). -/
theorem finiteOmegaTransition_tower (F : Finite D l hl Ω X)
    {E L M : Index l Ω} (h : E ≤ L) (k : L ≤ M) :
    (sfRationalScalarExtension l (Coefficient.{u} l Ω L) X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω M)
      (coefficientInclusion l Ω L M k)).map ((F.scalar E L h).omega.hom) ≫
        (F.scalar L M k).omega.hom =
      (GeneralAlgebraicallyClosedCoefficients.associator l Ω X E L M h k).hom.app
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
            (F.omega E).omega) ≫
        (F.scalar E M (h.trans k)).omega.hom := by sorry

end WeilConjectures.CoefQbarVerdier
