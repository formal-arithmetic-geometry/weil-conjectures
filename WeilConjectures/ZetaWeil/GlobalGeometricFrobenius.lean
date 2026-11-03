/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FrobeniusCohomologyTransportIso
public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex

/-!
# Global geometric Frobenius

Source: Weil blueprint, sec-six-functors/sk-prop-sf-rf-shriek-preservation,
order 2061 (blueprint: def-weil-global-geometric-frobenius).

The ordinary and compact operators are transport along the geometric Frobenius,
followed by the corresponding cohomology functor applied to the Weil structure.
The compactification is the retained presentation of the compact-support functor.

## Main definitions

* `globalGeometricFrobenius`: the two endomorphisms of coefficient complexes.
* `globalGeometricFrobeniusOnCohomology`: their maps in every integer degree.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (E : Padic.FiniteCoefficientFields c.l c.Qbar)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom] (c₀ : Compactification Y₀.hom)

/-- The ordinary and compactly supported global geometric Frobenius operators.
The coefficient datum fixes l ≠ p and its chosen algebraic closure, and E is a finite
subextension of that closure. K is a fixed pair with theta : Lg_Y^* For(K) ≅ For(K).
Each component is exactly tau_For(K) followed by RΓ(theta), or tau_c,For(K) followed
by RΓ_c(theta). The transports are the canonical point/exchange composites of
`frobeniusCohomologyTransportRational`; their isomorphism assertion is the rational
clause of `frobeniusCohomologyTransport_isIso`. The compact functor evaluates Ra_!
at the geometric point of Spec k, using the retained model compactification c₀.
Source: blueprint order 2061, the two displayed composites
(blueprint: def-weil-global-geometric-frobenius). -/
def globalGeometricFrobenius (K : sfWeilComplex D c.l c.different Y₀ E.val) :
    End ((frobeniusCohomologyRationalFunctor D c.l c.different E.val Y₀ c₀ false).obj
      K.carrier) ×
    End ((frobeniusCohomologyRationalFunctor D c.l c.different E.val Y₀ c₀ true).obj
      K.carrier) :=
  ((frobeniusCohomologyTransportRational D c.l c.different E.val Y₀ c₀ K.carrier).1 ≫
      (frobeniusCohomologyRationalFunctor D c.l c.different E.val Y₀ c₀ false).map
        K.str.hom,
    (frobeniusCohomologyTransportRational D c.l c.different E.val Y₀ c₀ K.carrier).2 ≫
      (frobeniusCohomologyRationalFunctor D c.l c.different E.val Y₀ c₀ true).map
        K.str.hom)

/-- The actions denoted F on H^i(Y,For K) and H_c^i(Y,For K), for every integer i.
These are H^i of the preceding endomorphisms of coefficient complexes, using the
recorded cohomology functor on bounded finite-dimensional E-coefficient complexes.
Source: blueprint order 2061, final cohomology clause
(blueprint: def-weil-global-geometric-frobenius). -/
def globalGeometricFrobeniusOnCohomology
    (K : sfWeilComplex D c.l c.different Y₀ E.val) (i : ℤ) :=
  ((DerivedCategory.coefficientFdCohomology E.val i).map
      (globalGeometricFrobenius D c E Y₀ c₀ K).1,
    (DerivedCategory.coefficientFdCohomology E.val i).map
      (globalGeometricFrobenius D c E Y₀ c₀ K).2)


section Qbar

universe v

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (c₀ : Compactification Y₀.hom)

end Qbar

end WeilConjectures
