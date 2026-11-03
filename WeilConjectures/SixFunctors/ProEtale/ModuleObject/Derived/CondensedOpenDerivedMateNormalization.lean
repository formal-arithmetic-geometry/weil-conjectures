/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenBaseChangeArbitrary

/-!
# Normalization of the literal derived open exchange

Source: the open-extension comparison in the proof of det-prop-sf-cbc.
(blueprint: new-cbc-literal-open-derived-mate).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj
open AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.CondensedRing
open CondensedOpenProper
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Exact derived open base change, transported to total derived pullback, has the canonical
open-adjunction mate as its inverse.

Proof: the underived comparison is defined by the open unit, the tensor-pullback square
comparison, and the pulled-back open counit. Its inverse is condensedOpenBaseChangeIso.
Apply the exact termwise functors on complexes and localize at quasi-isomorphisms. The exact
composition isomorphisms identify localization of the three-factor composite with the same
unit--square--counit expression for the exact derived adjunctions. Transport the right adjoints
through leftDerivedUpperStarIsoMapDerivedCategory at both vertical maps and both opens.
The derived pullback composition comparison is normalized by the underived one, so its square
comparison is precisely compactSupportCondensedFormalism.sqIso. The adjunction transport formula
then identifies the localized expression with ExchangeFormalism.baseChange. The two inverse
equations descend through localization, giving the stated equality of natural transformations.
Source: latest blueprint det-prop-sf-cbc, condensed open base-change factor; the construction
and inverse normalization in lem-sp-condensed-open-base-change-arbitrary
(blueprint: new-cbc-literal-open-derived-mate). -/
theorem compactSupport_literal_open_mate
    {U Z Z' : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] (b : Z' ⟶ Z) :
    ((compactSupportCondensedFormalism Λ).baseChange (pullback.fst j b)
      (pullback.snd j b) j b pullback.condition).natTrans =
    (Functor.isoWhiskerLeft (J Λ j) (leftDerivedUpperStarIsoMapDerivedCategory Λ b) ≪≫
      condensedOpenBaseChangeDerivedIso (Mon.mk Λ) j b ≪≫
      Functor.isoWhiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory Λ (pullback.fst j b)).symm
        (J Λ (pullback.snd j b))).inv := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
