/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalCoefficientClosedIntegralHeart
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.CondensedFinitePresentationMatrices
public import WeilConjectures.AlgebraicGeometry.CondensedLocalModelGluing
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
public import WeilConjectures.Topology.ConstructibleIsRetrocompact
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientDerivedFunctorAPI

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry Scheme
/-! # Finite coefficient affine exchange reduction

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Proposition 5.5,
Theorem 7.7 and the proper closed-fibre calculation.
(blueprint: lem-sp-original-coefficient-finite-affine-exchange)
-/

/-- Proper closed exchange for finite rational coefficients over an affine target.
Source: Hemo--Richarz--Scholbach, Proposition 5.5 and Theorem 7.7, and the
blueprint closed-complement proper-exchange calculation.
(blueprint: lem-sp-original-coefficient-finite-affine-exchange)

Proof: a proper scheme over the affine target is qcqs. Viewing `E` as a finite
intermediate field, choose the integral constructible model supplied by
`originalCoefficientIntegralHeartModel`.
Apply `originalCoefficientClosedIntegralHeart` to its degree-zero single.
The single and its exact inverse image are bounded below; localized direct-image
continuity therefore makes both scalar/direct-image comparison maps invertible.
Apply `originalCoefficientScalarExchange` to the resulting rectangle. Exact scalar
extension identifies the scalar-extended single with the single of the rational
model, and the model isomorphism identifies that module with M. Naturality
transports invertibility to the displayed canonical exchange. The complementary
open remains quasi-compact after pullback, giving the integral theorem's closed
constructible pullback hypothesis. Empty schemes and zero modules are covered by
the same argument. -/
theorem originalCoefficientFiniteAffineExchange
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell)) [FiniteDimensional ℚ_[ell] E]
    (Y : Scheme.{u}) [IsAffine Y] (hell : IsUnit (ell : Γ(Y, ⊤)))
    (X C : Scheme.{u}) (f : X ⟶ Y) [IsProper f]
    (i : C ⟶ Y) [IsClosedImmersion i]
    (hc : ∃ (U : Scheme.{u}) (j : U ⟶ Y),
      IsOpenImmersion j ∧ QuasiCompact j ∧ Set.range i.base = (Set.range j.base)ᶜ)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E) X) M) :
    IsIso ((refinementAmbientExchange (Profinite.continuousMapRingObj E)
      (g' := pullback.fst f i) (f' := pullback.snd f i) (f := f) (g := i)
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).app
      ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
