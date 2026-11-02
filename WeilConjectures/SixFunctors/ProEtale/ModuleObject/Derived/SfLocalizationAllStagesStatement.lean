/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedLocalization.CondensedClosedLocalization
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimensionSupplement
public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SmoothPurity.WeilSheafComplex

/-!
# Closed-support localization at all coefficient stages

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-kunneth-formulas-and-external-duality/
sk-thm-sf-kunneth-verdier/sk-prop-sf-localization/prop-sf-localization-all-stages.md
and its `.proof.md`, clauses (1)--(4), (1')--(4') and the Weil paragraph
(blueprint: prop-sf-localization-all-stages).

The qualitative theorem uses the existing non-hollow `ClosedLocalization` interface.
The finite bound and integral reduction bounds are separate statements, so no
quantitative Tor bound is imposed at rational coefficients. The two exceptional
identifications use the published finite comparison and the current Brown restriction.
The Weil statement uses `StrictWeilCondensed.action` and the realization of the
current native Weil complexes, rather than the withdrawn `StrictWeil` model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Restrict the current exact Frobenius action to Dbc. At field coefficients its
fixed pairs are the same structures as the current Dctf strict pairs.
Source: Weil paragraph (blueprint: prop-sf-localization-all-stages). -/
def sfLocalizationAction {T : Scheme.{u}} (g : T ≅ T) :
    ConstantModelBoundedConstructible Λ T ⥤ ConstantModelBoundedConstructible Λ T :=
  (constantModelBoundedConstructible Λ T).lift
    ((constantModelBoundedConstructible Λ T).ι ⋙ StrictWeilCondensed.action Λ g)
    (fun K ↦ ((StrictWeilCondensed.action_preserves Λ g K.obj).1).mpr K.property)

/-- Pullback composition across a commuting automorphism square. This is constructed
from the actual module-derived compositors and the exact Frobenius comparison.
Source: Weil paragraph, derived pullback composition
(blueprint: prop-sf-localization-all-stages). -/
def sfLocalizationPullExchange {S T : Scheme.{u}} (f : S ⟶ T)
    (gS : S ≅ S) (gT : T ≅ T) (h : f ≫ gT.hom = gS.hom ≫ f) :
    moduleObjectDerivedPullback Λ f ⋙ StrictWeilCondensed.action Λ gS ≅
      StrictWeilCondensed.action Λ gT ⋙ moduleObjectDerivedPullback Λ f :=
  (Functor.isoWhiskerLeft (moduleObjectDerivedPullback Λ f)
      (leftDerivedUpperStarIsoMapDerivedCategory Λ gS.hom)).symm ≪≫
    (leftDerivedUpperStarComp Λ gS.hom f).symm ≪≫
    Functor.leftDerivedFunctorNatIso _ (upperStarCongr Λ h.symm) ≪≫
    leftDerivedUpperStarComp Λ f gT.hom ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ gT.hom)
      (moduleObjectDerivedPullback Λ f)

/-- Forget only the finite-Tor membership proof of a current strict Weil pair.
The Frobenius isomorphism and carrier are unchanged.
Source: Weil paragraph (blueprint: prop-sf-localization-all-stages). -/
def sfLocalizationStrictPair {T : Scheme.{u}} (g : T ≅ T)
    (K : StrictWeilCondensed.Complex Λ g) :
    Endofunctor.IsoAlgebra (sfLocalizationAction Λ g) :=
  Endofunctor.IsoAlgebra.mk ⟨K.carrier.obj, K.carrier.property.1⟩
    ((constantModelBoundedConstructible Λ T).isoMk
      ((constantModelBoundedConstructible Λ T ⊓
        _root_.DerivedCategory.finiteTorAmplitude _).ι.mapIso K.str))

/-- Realize a native Weil complex by its specified localized Frobenius structure,
then forget its finite-Tor membership proof. This uses the current native-to-strict
comparison, with no assertion that realization is faithful.
Source: Weil paragraph (blueprint: prop-sf-localization-all-stages). -/
def sfLocalizationNativePair {T : Scheme.{u}} (g : T ≅ T)
    (ell : ℕ) [Fact ell.Prime] [IsNoetherian T]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (K : StrictWeilCondensed.Native Λ g) :
    Endofunctor.IsoAlgebra (sfLocalizationAction Λ g) :=
  sfLocalizationStrictPair Λ g ((StrictWeilCondensed.nativeComparison Λ g ell hΛ).obj K)

variable {Λ} {X Z U : Scheme.{u}} {i : Z ⟶ X} {j : U ⟶ X}

variable (Λ)

end AlgebraicGeometry.ProEtale.CondensedRing
