/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.Paper.LocallyFiniteAdicRealizationData
public import Sheaf.Paper.IntegralStratifiedPerfectModels
public import Sheaf.Paper.IntegralCompletedCoefficientTransport

/-! # Native constructibility of an ordinary integral local model

Source: Bhatt--Scholze, Definitions 6.8.3 and 6.8.10, Proposition 6.8.14(2).
(blueprint: lem-sf-native-integral-coefficient-heart).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization

/-- A stratified finitely presented integral module becomes a native constructible
sheaf under ordinary tensor extension. No assertion about derived objects occurs here.

Source: Bhatt--Scholze, Definitions 6.8.3 and 6.8.10, Proposition 6.8.14(2).
(blueprint: lem-sf-native-integral-coefficient-heart).

Proof in words: take the finite stratification and the covering sieves in hN.
Restriction along the normalized completed coefficient isomorphism identifies the
local models with completed constant realizations of finitely presented valuation-ring
modules. Tensoring with C.integralMap commutes with the actual-ring inverse images and
slice restrictions, by the scalar-extension adjunction and its balanced tensor
associator. On each covering member this gives the native coefficient tensored with the
scalar module localized to E and then extended along i. A finitely presented module over
the valuation DVR becomes a finite-dimensional E-vector space after localization;
torsion becomes zero. Choose a finite basis and extend it to identify the displayed
tensor with a finite direct sum of native units. The section-module equivalence and
scalar-forgetting equivalence identify those units and commute with inverse image;
full faithfulness lifts the trivializations through e. Replace each covering sieve by
a small pro-etale covering family. Hence the native restriction is lisse on each of the
same finitely many strata, and is therefore constructible. Empty strata, the empty
scheme, zero modules and torsion local models all use the permitted rank zero.
-/
theorem nativeIntegralCoefficient_heart
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [IsCommMonObj (abRing l X)]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) (C : CoefficientPresentation l X E i)
    (N : scalarReductionSource.{u, u} l E X)
    (hN : IsIntegralStratifiedFinitelyPresented X (pbcIntegralDatum l E)
      ((SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison X l E).hom).obj N))
    (F : ProEtale.AdicSheaf l X)
    (e : (sections l X).obj F ≅ (pbcExtend (C.integralMap l X)).obj N) :
    ProEtale.IsAdicConstructibleSheaf F := by sorry

end WeilConjectures.LocallyFiniteAdicRealization
