/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeWeilScalar.NativeWeilScalarCounitData

/-! # Pinned native scalar and Frobenius counit datum

Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance.proof.md, final paragraph
(blueprint: lem-sf-native-weil-scalar-frobenius-counit).

The ordinary counit datum is retained together with the two normalization witnesses.
This pins the comparison `alpha`, the ordinary exchange, and the inverse exchange at
once; the normalization fields therefore cannot be chosen for an unrelated counit datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.NativeWeilScalar
open AdicQbarRealization
variable (l : ℕ) [Fact l.Prime]

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (R : Family l D)
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
  [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
  (c₀ : Compactification f₀.left)

variable [I : ExceptionalFieldDescent.IntegralInput l D hl
  (FrobeniusExchange.geometricCompactification D f₀ c₀)]
  [J : ExceptionalFieldDescent.RationalOutput l D hl
    (FrobeniusExchange.geometricCompactification D f₀ c₀)]
  (S : ExceptionalFieldDescent.CommonStageData l D hl
    (FrobeniusExchange.geometricCompactification D f₀ c₀) (PadicAlgCl l))
  (O : ExceptionalFieldDescent.CommonOutput l D hl
    (FrobeniusExchange.geometricCompactification D f₀ c₀) (PadicAlgCl l) S)

end WeilConjectures.NativeWeilScalar
