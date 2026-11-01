/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherenceData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Basic normalized open exchange data

The basic data and canonical open units used to assemble the open exchange laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
/-- The canonical normalized open-unit package. Full faithfulness of extension by zero gives
the underived unit isomorphism, and exact derived passage gives the displayed derived unit.
Source: the open-unit step of the composition proof
(blueprint: lem-zl-condensed-open-proper-pasting). -/
noncomputable def canonicalOpenUnits : OpenUnits Λ where
  unitIso := fun {U W} j _ => by
    let ff := (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).fullyFaithfulFunctor.comp
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).fullyFaithfulMapModLeft
    have : (openImmersionLowerShriek Λ j).Full := ff.full
    have : (openImmersionLowerShriek Λ j).Faithful := ff.faithful
    have hu : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit :=
      (openImmersionLowerShriekUpperStarAdjunction Λ j).unit_isIso_of_L_fully_faithful
    letI : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit := hu
    letI : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit :=
      Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
    exact asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit)
  normalized := by
    intro U W j _
    simp

/-- Basic data with both the open units and the Cartesian exchange pinned to their
canonical adjunction normalizations. -/
structure OpenLawsBasic where
  /-- The selected units are the canonical derived open-adjunction units. -/
  units : OpenUnits Λ
  units_normalized : units = canonicalOpenUnits Λ
  B : ∀ {U' U W' W : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ W'}
    {j : U ⟶ W} {b : W' ⟶ W} [IsOpenImmersion j] [IsOpenImmersion j'],
    IsPullback a j' j b → (J Λ j ⋙ P Λ b ≅ P Λ a ⋙ J Λ j')
  B_normalized : ∀ {U' U W' W : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ W'}
    {j : U ⟶ W} {b : W' ⟶ W} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback a j' j b), (B sq).inv = openMap Λ sq.toCommSq

/-- Existence of the canonical open-unit package.
Source: latest blueprint sk-thm-sf-comp-composition.proof.md, open-adjunction normalization.

Proof:
1. For an open immersion, the module extension-by-zero functor is fully faithful: compose
the comap equivalence with the fully faithful map supplied by the sheaf extension-by-zero
adjunction. The underived adjunction unit is therefore an isomorphism.
2. Exact derived passage transports this unit to the unbounded derived categories. Install
the resulting `IsIso` instance and use `Adjunction.isIso_mapDerivedCategoryAdjunction_unit`;
`asIso` of that derived unit is the required `unitIso`, while `asIso_hom` gives its
normalization equation.
(blueprint: new-zl-condensed-open-proper-units) -/
theorem canonicalOpenUnits_exists : Nonempty (OpenUnits Λ) :=
  ⟨canonicalOpenUnits Λ⟩

/-- The basic unit and Cartesian exchange package.
Source: latest blueprint sk-thm-sf-comp-composition.proof.md, Base change paragraph.

Proof:
1. Transport internal modules over `p_T^*Λ` to modules over the section-ring sheaf, with
pullback, direct image, open extension and their specified adjunctions. Exact diagram descent
transports units, counits and their equations to unbounded derived categories. Pullback and
open extension are exact, so `P f = D(f^*)` and `J j = D(j_!)`.
2. Apply arbitrary-scheme condensed open base change to show that `openMap` (the unit,
the square comparison, and the counit) is invertible on every Cartesian open square, without
quasi-compactness. Define `B` to be its inverse, which gives `B_normalized` by `asIso_hom`.
The transported ringed-site normalization gives the canonical invertible open units, and the
pinning equation records that the selected `units` are those canonical units.
(blueprint: new-zl-condensed-open-proper-basic) -/
theorem condensedOpenProperOpenBasic (_hΛ : IsAdmissibleCoefficient Λ) :
    Nonempty (OpenLawsBasic Λ) := by sorry
end AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper
