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
/-! # Algebraic-closure coefficient affine exchange reduction

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Proposition 5.2,
Lemma 5.3(1), Lemma 7.9 and the finite coefficient proper closed-fibre calculation.
(blueprint: lem-sp-original-coefficient-qbar-affine-exchange)
-/

/-- Proper closed exchange for finite-subextension-valued Qbar coefficients over an affine target.
Source: Hemo--Richarz--Scholbach, Proposition 5.2, Lemma 5.3(1), Lemma 7.9 and
Theorem 7.7, and the blueprint closed-complement proper-exchange calculation.
(blueprint: lem-sp-original-coefficient-qbar-affine-exchange)

Proof: the proper preimage of the affine target is qcqs. Apply
`originalCoefficientQbarHeartModel` to descend M to a constructible module over
one finite coefficient field. Apply `originalCoefficientFiniteAffineExchange` to
that finite model. The single of the model and its exact inverse image are bounded
below, so filtered finite-subextension direct-image continuity makes the two
scalar/direct-image comparison maps invertible. The scalar/geometric mate
rectangle `originalCoefficientScalarExchange` identifies the scalar-extended
exchange with the literal Qbar exchange. Exact scalar extension and the supplied
module isomorphism identify its input with M[0]; naturality gives the conclusion.
The coefficient object remains the finite-subextension-valued object throughout.
Empty strata and zero modules use their zero models. -/
theorem originalCoefficientQbarAffineExchange
    (ell : ℕ) [Fact ell.Prime]
    (Y : Scheme.{u}) [IsAffine Y] (hell : IsUnit (ell : Γ(Y, ⊤)))
    (X C : Scheme.{u}) (f : X ⟶ Y) [IsProper f]
    (i : C ⟶ Y) [IsClosedImmersion i]
    (hc : ∃ (U : Scheme.{u}) (j : U ⟶ Y),
      IsOpenImmersion j ∧ QuasiCompact j ∧ Set.range i.base = (Set.range j.base)ᶜ)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ell))
    (hM : IsConstructibleModuleObject (padicAlgClRingObj X ell) M) :
    IsIso ((refinementAmbientExchange (Profinite.padicAlgClRingObj ell)
      (g' := pullback.fst f i) (f' := pullback.snd f i) (f := f) (g := i)
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).app
      ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
