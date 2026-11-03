/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCupProduct

/-! # Mixed-support cup on the intrinsic finite-Tor category

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-global-duality-and-the-poincare-pairing/
sk-thm-sf-identification/def-sf-cup.md, displayed projection/counit composite
(blueprint: def-sf-cup).

The native construction accepts every commutative condensed ring, including arbitrary
finite discrete ell-primary rings. The inputs here belong to the recorded intrinsic
finite-Tor constructible category. The output remains in the native point category.
Preservation and coherence are the separately recorded properties of the operations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The native mixed-support cup for intrinsic finite-Tor constructible inputs.
The coefficient hypothesis includes every finite commutative ell-primary ring with its
discrete condensed structure, as well as the integral and field coefficients. No
valuation-ring quotient presentation of a finite coefficient is required.

This is the existing abstract cup construction specialized to the canonical native
compactification projection and derived pullback/direct-image adjunction: projection
at `(K, Ra_* L)`, followed by `Ra_!(1_K tensor counit_L)`. It uses no exceptional
right adjoint, so no operation datum is required to construct this arrow, including
for a finite coefficient outside the distinguished stages.

Construction, following the node's proof:
1. Native categories over the pulled-back rings `condensedRingObj Λ T`, the relative
   K-flat module tensor, `C(K) = Ra_! K` (`rightDerivedLowerShriekOfCompactification`)
   and `G(L) = Ra_* L` (`moduleObjectDerivedPushforward`) in the point category.
2. The native compactification projection `exceptionalProjectionMorphismOfCompactification`
   (the `pf` of def-exchange-projection) evaluated at `(K, Ra_* L)`.
3. `Ra_!` applied to `K ◁ ε_L`, with `ε` the counit of
   `derivedUpperStarLowerStarAdjunction`; composing gives the displayed cup.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-global-duality-and-the-poincare-pairing/
sk-thm-sf-identification/def-sf-cup.md, coefficient setting and displayed composite
(blueprint: def-sf-cup). -/
def intrinsicFiniteTorMixedSupportCupProduct (D : WeilConjectures.FiniteFieldDatum.{u})
    (C : D.CoefficientDatum) (_hΛ : IsLocalizingAdmissibleCoefficient C.l Λ)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of D.k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (c : Compactification a) (K L : CondensedConstructibleFiniteTor Λ X) :
    (rightDerivedLowerShriekOfCompactification Λ c).obj K.obj ⊗
        (moduleObjectDerivedPushforward Λ a).obj L.obj ⟶
      (rightDerivedLowerShriekOfCompactification Λ c).obj (K.obj ⊗ L.obj) :=
  (derivedUpperStarLowerStarAdjunction Λ a).cupProductOfProjection
    (rightDerivedLowerShriekOfCompactification Λ c)
    (exceptionalProjectionMorphismOfCompactification Λ c) K.obj L.obj

end AlgebraicGeometry.ProEtale.CondensedRing
