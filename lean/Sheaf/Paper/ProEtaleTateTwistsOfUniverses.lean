/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.Paper.ProEtaleTateTwists

/-! # Tate twists in an arbitrary derived localization universe

Source: blueprint main-20261015, sec-proetale-coefficients, sk-def-sp-tate-twist,
final derived-twist formula (blueprint: sk-def-sp-tate-twist).
All coefficient lines, finite quotient transitions and scalar actions are the
published constructions. Only the localization Hom universe is generalized.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe w u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Derived tensor with the existing signed coefficient line in degree zero, in any
chosen unbounded localization. This includes the standard localization, whose Hom
universe is u+2, while retaining the published u+1-localization specialization.
Source: blueprint final K(d) formula (blueprint: sk-def-sp-tate-twist). -/
def spComplexTwistOfUniverses (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    [HasDerivedCategory.{w} (SheafOfModules.{u + 1} (Scheme.purTwistRing X R))]
    (L : SheafOfModules.{u + 1} (Scheme.purTwistRing X R))
    (K : DerivedCategory (SheafOfModules.{u + 1} (Scheme.purTwistRing X R))) (d : ℤ) :
    DerivedCategory (SheafOfModules.{u + 1} (Scheme.purTwistRing X R)) :=
  (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u + 1, u, u + 1, w}
    (Scheme.ProEt.topology X) R).obj
    (K, (DerivedCategory.singleFunctor.{w, u + 1, u + 2}
      (SheafOfModules.{u + 1} (Scheme.purTwistRing X R)) 0).obj
      (WeilConjectures.coefficientTwistLine.{u} X (R := R) L d))

end AlgebraicGeometry.ProEtale
