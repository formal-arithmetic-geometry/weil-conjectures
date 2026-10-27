/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.Paper.LatticeSheafBasic

/-! # Integral condensed coefficient ring

Source: Hemo--Richarz--Scholbach, Example 3.1; Bhatt--Scholze, Definition 6.8.1
(blueprint: def-sfb-integral-condensed-ring).

Specialize the existing continuous-map condensed-ring construction to the existing
valuation-topology ring of integers. The ring-object structures are the same canonical
structures supplied by that construction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The condensed integral coefficient ring with sections `C(S, O_E)`.
Source: Hemo--Richarz--Scholbach, Example 3.1; Bhatt--Scholze, Definition 6.8.1
(blueprint: def-sfb-integral-condensed-ring). -/
def integralCondensedCoefficientRing (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  Profinite.continuousMapRingObjOfUniverse (latticeCoefficientIntegers l E)

/-- The canonical multiplication and unit of the continuous-map condensed ring.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: def-sfb-integral-condensed-ring). -/
instance integralCondensedCoefficientRingMonObj (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    MonObj (integralCondensedCoefficientRing l E) :=
  Profinite.continuousMapRingObjOfUniverseMonObj (latticeCoefficientIntegers l E)

/-- Commutativity inherited from pointwise multiplication on `O_E`-valued functions.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: def-sfb-integral-condensed-ring). -/
instance integralCondensedCoefficientRingComm (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    IsCommMonObj (integralCondensedCoefficientRing l E) :=
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse (latticeCoefficientIntegers l E)

end AlgebraicGeometry.ProEtale
