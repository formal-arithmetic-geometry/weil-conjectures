/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierData

/-! # The finite dualizing comparison in the recorded stage system

Source: thm-coef-qbar-verdier, finite coefficient transport in steps 4--5.
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

open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage stageSystem)

/-- The finite dualizing comparison, transported along the recorded transition equality. -/
def finiteOmegaStageComparison (F : Finite D l hl Ω X)
    {E L : Index l Ω} (h : E ≤ L) :
    ((stageSystem l Ω X).T h).obj
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
        (F.omega E).omega) ≅
      (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).obj
        (F.omega L).omega :=
  (operationStageTransitionIso l Ω X E L h).app _ ≪≫ (F.scalar E L h).omega

/-- The normalized finite dualizing comparisons obey the stage associator equation.
Source: thm-coef-qbar-verdier, finite coefficient transport in steps 4--5;
lem-coef-integral-finite-extension, composition of u.
(blueprint: lem-coef-qbar-finite-omega-stage-coherence).

Proof: replace each rational omega map by the localization of its normalized integral
u map, using F.normalized. The composition clause of integral finite extension gives
T(u(E,L)) followed by u(L,M) equal to the integral balanced tensor associator followed
by u(E,M). Localize this equality. The rational scalar functor sends the localized
integral u to its localized scalar extension; its associator is the localization of
the same balanced tensor associator. The coefficient-inclusion composition law
identifies the composite coefficient map with the direct inclusion. Finally transport
along operationStageTransitionIso and the specified stage associator equality.
Naturality of these equality isomorphisms cancels the intermediate transports.
This argument includes repeated fields, zero objects, and the empty scheme. -/
theorem finiteOmegaStageComparison_tower (F : Finite D l hl Ω X)
    {E L M : Index l Ω} (h : E ≤ L) (k : L ≤ M) :
    ((stageSystem l Ω X).T k).map (finiteOmegaStageComparison D l hl Ω X F h).hom ≫
        (finiteOmegaStageComparison D l hl Ω X F k).hom =
      ((stageSystem l Ω X).assoc h k).hom.app
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
            (F.omega E).omega) ≫
        (finiteOmegaStageComparison D l hl Ω X F (h.trans k)).hom := by sorry

end WeilConjectures.CoefQbarVerdier
