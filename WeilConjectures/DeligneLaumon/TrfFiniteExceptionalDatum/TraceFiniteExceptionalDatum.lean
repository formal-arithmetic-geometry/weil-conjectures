/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfRfShriekPreservation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmSfCompCompositionWitnesses
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfExistence

/-! # The trace-formula exceptional datum at an arbitrary finite ring

Source: latest blueprint, lem-sf-etale-shriek-equals-pullback, in the
exceptional-adjoint setting of def-trf-admissibility
(blueprint: lem-sf-etale-shriek-equals-pullback).

This is an adapter for the existing TraceFormulaAdmissibility anchor, not a
second attachment of that node. `ofAdmissibility` constructs all its fields
from that anchor's specified witness package and finite supplied adjunction.

All categories below are the published native module-object categories. The small
category is the full Dctf subcategory of the localizing closure. The datum specifies
a right adjoint on that closure, together with its preservation proof, rather than
an ambient pro-etale right adjoint. Compact-support comparisons are the normalized
proper/open comparisons of CoherentData. No uniform bound over coefficient rings
and no FullCD hypothesis is included.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace WeilConjectures
open AlgebraicGeometry Scheme AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The already defined discrete condensed coefficient ring, with its native universe.
Source: def-trf-admissibility, pulled-back coefficients
(blueprint: lem-sf-etale-shriek-equals-pullback). -/
abbrev trfFiniteCoefficient := Profinite.continuousMapRingObj.{u} A

/-- The existing localizing category, without a change of site or coefficient objects.
Source: def-trf-admissibility, localizing construction
(blueprint: lem-sf-etale-shriek-equals-pullback). -/
abbrev trfFiniteLoc (T : Scheme.{u}) :=
  (localizingClosureProEtale (trfFiniteCoefficient A) T).FullSubcategory

/-- The published Dctf property on the localizing closure.
Source: def-trf-admissibility, constructible restriction
(blueprint: lem-sf-etale-shriek-equals-pullback). -/
abbrev trfFiniteCtfProperty (T : Scheme.{u}) :=
  localizingDctfProperty (trfFiniteCoefficient A) T

/-- The full bounded constructible finite-Tor category in native coordinates.
Source: def-trf-admissibility, displayed domains (blueprint: lem-sf-etale-shriek-equals-pullback).
-/
abbrev trfFiniteCtf (T : Scheme.{u}) := (trfFiniteCtfProperty A T).FullSubcategory

/-- The datum at a general finite ell-primary ring. The right functors and their
adjunctions are the specified localizing exceptional adjoints; preservation supplies
their constructible restriction. The comparison fields are the published CoherentData,
including its proper/open, refinement and composition/exchange normalization laws.
The supplied right adjoint
and its counit determine its constructible restriction.
Availability is supplied by sk-thm-existence and sk-prop-sf-rf-shriek-preservation;
these fields name that datum, not additional geometric hypotheses.
Source: latest def-trf-admissibility, all finite-A clauses
(blueprint: def-sf-etale-finite-exceptional-datum). -/
structure TrfFiniteExceptionalDatum (D : FiniteFieldDatum.{u}) (ell : ℕ)
    [Fact ell.Prime] (A : Type) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A] where
  different : ell ≠ D.p
  primary : ∃ n : ℕ, 1 ≤ n ∧ (ell : A) ^ n = 0
  comparisons : CompactSupportComposition.CoherentData (trfFiniteCoefficient A) D.k
  compactification : ∀ {X Y : SepFinType D.k} (f : X ⟶ Y),
    Compactification f.hom.left
  right : ∀ {X Y : SepFinType D.k} (_f : X ⟶ Y),
    trfFiniteLoc A Y.obj.left ⥤ trfFiniteLoc A X.obj.left
  adj : ∀ {X Y : SepFinType D.k} (f : X ⟶ Y),
    localizingLowerShriek (trfFiniteCoefficient A) (compactification f)
      (comparisons.preserves f (compactification f)).1 ⊣ right f
  directImagePreserves : ∀ {X Y : SepFinType D.k} (f : X ⟶ Y)
      (K : trfFiniteCtf A X.obj.left),
    constantModelBoundedConstructible (trfFiniteCoefficient A) Y.obj.left
        ((moduleObjectDerivedPushforward (trfFiniteCoefficient A) f.hom.left).obj K.obj.obj) ∧
      DerivedCategory.finiteTorAmplitude _
        ((moduleObjectDerivedPushforward (trfFiniteCoefficient A) f.hom.left).obj K.obj.obj)
  preserves : ∀ {X Y : SepFinType D.k} (f : X ⟶ Y) (K : trfFiniteLoc A Y.obj.left),
    trfFiniteCtfProperty A Y.obj.left K →
      trfFiniteCtfProperty A X.obj.left ((right f).obj K)

local instance {k : Type u} [Field k] (T : SepFinType k) :
    LocallyOfFiniteType (T.obj.left ↘ Spec (.of k)) := by
  change LocallyOfFiniteType T.obj.hom
  infer_instance
local instance {k : Type u} [Field k] (T : SepFinType k) :
    QuasiCompact (T.obj.left ↘ Spec (.of k)) := by
  change QuasiCompact T.obj.hom
  infer_instance
local instance {k : Type u} [Field k] (T : SepFinType k) :
    IsSeparated (T.obj.left ↘ Spec (.of k)) := by
  change IsSeparated T.obj.hom
  infer_instance
local instance {k : Type u} [Field k] {X Y : SepFinType k} (f : X ⟶ Y) :
    LocallyOfFiniteType f.hom.left := by
  have : LocallyOfFiniteType (f.hom.left ≫ Y.obj.hom) := by
    rw [f.hom.w]
    infer_instance
  exact locallyOfFiniteType_of_comp f.hom.left Y.obj.hom
local instance {k : Type u} [Field k] {X Y : SepFinType k} (f : X ⟶ Y) :
    IsSeparated f.hom.left := by
  have : IsSeparated (f.hom.left ≫ Y.obj.hom) := by
    rw [f.hom.w]
    infer_instance
  exact IsSeparated.of_comp f.hom.left Y.obj.hom
local instance {k : Type u} [Field k] {X Y : SepFinType k} (f : X ⟶ Y) :
    QuasiCompact f.hom.left := by
  let : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  let : QuasiSeparatedSpace Y.obj.left := quasiSeparatedSpace_of_quasiSeparated Y.obj.hom
  exact quasiCompact_of_compactSpace f.hom.left

namespace TrfFiniteExceptionalDatum
variable {A} [Finite A] [DiscreteTopology A]
  {D : FiniteFieldDatum.{u}} {ell : ℕ} [Fact ell.Prime]
  (S : TrfFiniteExceptionalDatum D ell A)

/-- Compact support on the localizing closure, with its actual ambient maps.
Source: def-trf-admissibility, specified left functor
(blueprint: lem-sf-etale-shriek-equals-pullback). -/
def localizingSupport {X Y : SepFinType D.k} (f : X ⟶ Y) :=
  localizingLowerShriek (trfFiniteCoefficient A) (S.compactification f)
    (S.comparisons.preserves f (S.compactification f)).1

/-- Restrict the actual derived pullback to the localizing categories.
Source: def-trf-admissibility, ordinary operations
(blueprint: def-sf-etale-finite-exceptional-datum). -/
def localizingPullback {X Y : SepFinType D.k} (f : X ⟶ Y) :
    trfFiniteLoc A Y.obj.left ⥤ trfFiniteLoc A X.obj.left :=
  (localizingClosureProEtale (trfFiniteCoefficient A) X.obj.left).lift
    ((localizingClosureProEtale (trfFiniteCoefficient A) Y.obj.left).ι ⋙
      moduleObjectDerivedPullback (trfFiniteCoefficient A) f.hom.left)
    (fun K ↦ (S.comparisons.pullback_preserves X Y f.hom.left).1 K.obj K.property)

/-- The constructible compact-support restriction, using the published preservation clause.
Source: def-trf-admissibility, Rf_! (blueprint: lem-sf-etale-shriek-equals-pullback). -/
def support {X Y : SepFinType D.k} (f : X ⟶ Y) :
    trfFiniteCtf A X.obj.left ⥤ trfFiniteCtf A Y.obj.left :=
  (trfFiniteCtfProperty A Y.obj.left).lift
    ((trfFiniteCtfProperty A X.obj.left).ι ⋙ S.localizingSupport f)
    (fun K ↦ (S.comparisons.preserves f (S.compactification f)).2 K.obj.obj K.property)

/-- The specified right adjoint restricted to the full constructible subcategories.
Source: def-trf-admissibility, Rf^! (blueprint: lem-sf-etale-shriek-equals-pullback). -/
def exceptional {X Y : SepFinType D.k} (f : X ⟶ Y) :
    trfFiniteCtf A Y.obj.left ⥤ trfFiniteCtf A X.obj.left :=
  (trfFiniteCtfProperty A X.obj.left).lift
    ((trfFiniteCtfProperty A Y.obj.left).ι ⋙ S.right f)
    (fun K ↦ S.preserves f K.obj K.property)

/-- The actual total derived module pullback, restricted to Dctf.
Source: def-trf-admissibility and def-weil-derived-pullback-tensor-hom
(blueprint: def-sf-etale-finite-exceptional-datum). -/
def pullback {X Y : SepFinType D.k} (f : X ⟶ Y) :
    trfFiniteCtf A Y.obj.left ⥤ trfFiniteCtf A X.obj.left :=
  (trfFiniteCtfProperty A X.obj.left).lift
    ((trfFiniteCtfProperty A Y.obj.left).ι ⋙ S.localizingPullback f)
    (fun K ↦ (S.comparisons.pullback_preserves X Y f.hom.left).2 K.obj.obj K.property)

/-- Restrict the same Hom bijections, and therefore the same unit and counit.
Source: def-trf-admissibility, adjunction (blueprint: lem-sf-etale-shriek-equals-pullback). -/
def adjunction {X Y : SepFinType D.k} (f : X ⟶ Y) : S.support f ⊣ S.exceptional f :=
  (S.adj f).restrictFullyFaithful (trfFiniteCtfProperty A X.obj.left).fullyFaithfulι
    (trfFiniteCtfProperty A Y.obj.left).fullyFaithfulι (Iso.refl _) (Iso.refl _)

/-- The ordinary native derived direct image on Dctf. Its intermediate localizing
membership follows directly from membership in the generating Dctf property.
Source: def-trf-admissibility, ordinary direct images
(blueprint: lem-sf-etale-shriek-equals-pullback). -/
def directImage {X Y : SepFinType D.k} (f : X ⟶ Y) :
    trfFiniteCtf A X.obj.left ⥤ trfFiniteCtf A Y.obj.left :=
  (trfFiniteCtfProperty A Y.obj.left).lift
    ((localizingClosureProEtale (trfFiniteCoefficient A) Y.obj.left).lift
      ((trfFiniteCtfProperty A X.obj.left).ι ⋙
        (localizingClosureProEtale (trfFiniteCoefficient A) X.obj.left).ι ⋙
          moduleObjectDerivedPushforward (trfFiniteCoefficient A) f.hom.left)
      (fun K _P _hP hgen ↦ hgen _ (S.directImagePreserves f K)))
    (fun K ↦ S.directImagePreserves f K)

/-- Restrict the published ordinary total-derived module adjunction.
Source: def-trf-admissibility, Lg* ⊣ Rg_* (blueprint: lem-sf-etale-shriek-equals-pullback). -/
def ordinaryAdjunction {X Y : SepFinType D.k} (f : X ⟶ Y) :
    S.pullback f ⊣ S.directImage f :=
  (derivedUpperStarLowerStarAdjunction (trfFiniteCoefficient A) f.hom.left).restrictFullyFaithful
    ((trfFiniteCtfProperty A Y.obj.left).fullyFaithfulι.comp
      (localizingClosureProEtale (trfFiniteCoefficient A) Y.obj.left).fullyFaithfulι)
    ((trfFiniteCtfProperty A X.obj.left).fullyFaithfulι.comp
      (localizingClosureProEtale (trfFiniteCoefficient A) X.obj.left).fullyFaithfulι)
    (Iso.refl _) (Iso.refl _)

/-- The prescribed compact-support compositor lifted through the two full inclusions.
Source: def-trf-admissibility, left comparison (blueprint: lem-sf-etale-shriek-equals-pullback). -/
def supportComposition {X Y Z : SepFinType D.k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    S.support f ⋙ S.support g ≅ S.support (f ≫ g) :=
  NatIso.ofComponents
    (fun K ↦ (trfFiniteCtfProperty A Z.obj.left).isoMk
      ((localizingClosureProEtale (trfFiniteCoefficient A) Z.obj.left).isoMk
        ((S.comparisons.comp f g (S.compactification f) (S.compactification g)
          (S.compactification (f ≫ g))).app K.obj)))
    (fun b ↦ ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _
      ((S.comparisons.comp f g (S.compactification f) (S.compactification g)
        (S.compactification (f ≫ g))).hom.naturality b.hom)))

/-- The exceptional compositor is the conjugate of that exact left comparison.
Source: def-trf-admissibility, composition paragraph
(blueprint: lem-sf-etale-shriek-equals-pullback). -/
def exceptionalComposition {X Y Z : SepFinType D.k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    S.exceptional (f ≫ g) ≅ S.exceptional g ⋙ S.exceptional f :=
  conjugateIsoEquiv (S.adjunction (f ≫ g)) ((S.adjunction f).comp (S.adjunction g))
    (S.supportComposition f g)

/-- Restrict the canonical native derived pullback compositor.
Source: def-trf-admissibility, ordinary pullbacks
(blueprint: lem-sf-etale-shriek-equals-pullback). -/
def pullbackComposition {X Y Z : SepFinType D.k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    S.pullback (f ≫ g) ≅ S.pullback g ⋙ S.pullback f :=
  NatIso.ofComponents
    (fun K ↦ (trfFiniteCtfProperty A X.obj.left).isoMk
      ((localizingClosureProEtale (trfFiniteCoefficient A) X.obj.left).isoMk
        ((leftDerivedUpperStarComp (trfFiniteCoefficient A) f.hom.left g.hom.left).app
          K.obj.obj)))
    (fun b ↦ ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _
      ((leftDerivedUpperStarComp (trfFiniteCoefficient A) f.hom.left g.hom.left).hom.naturality
        b.hom.hom)))

/-- The normalized compact-support exchange, with the actual proper/open components.
Source: def-trf-admissibility, generic compact-support base change
(blueprint: def-sf-etale-finite-exceptional-datum). -/
def supportBaseChange {X Y X' Y' : SepFinType D.k}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (a : X' ⟶ X) (v : Y' ⟶ Y)
    (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left) :
    S.support f ⋙ S.pullback v ≅ S.pullback a ⋙ S.support f' :=
  NatIso.ofComponents
    (fun K ↦ (trfFiniteCtfProperty A Y'.obj.left).isoMk
      ((localizingClosureProEtale (trfFiniteCoefficient A) Y'.obj.left).isoMk
        ((S.comparisons.exchange (a := a.hom.left) (v := v.hom.left) sq (S.compactification f)
          (S.compactification f')).app K.obj)))
    (fun b ↦ ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _
      ((S.comparisons.exchange (a := a.hom.left) (v := v.hom.left) sq (S.compactification f)
        (S.compactification f')).hom.naturality b.hom)))

/-- The exceptional exchange isomorphism with direct images, obtained by
conjugating exactly the two composite adjunctions in def-trf-admissibility.
Source: def-trf-admissibility, displayed exchange isomorphism
(blueprint: lem-sf-etale-shriek-equals-pullback). -/
def exceptionalExchange {X Y X' Y' : SepFinType D.k}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (a : X' ⟶ X) (v : Y' ⟶ Y)
    (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left) :
    S.exceptional f' ⋙ S.directImage a ≅ S.directImage v ⋙ S.exceptional f :=
  conjugateIsoEquiv ((S.ordinaryAdjunction a).comp (S.adjunction f'))
    ((S.adjunction f).comp (S.ordinaryAdjunction v)) (S.supportBaseChange a v sq)

/-- The exceptional pullback base-change arrow, the mate of inverse compact-support
exchange. Equivalently this is the ordinary-adjunction mate of the conjugate exchange
Rg'_* Rf'^! ≅ Rf^! Rg_* in the source, by mate-pasting. No invertibility of this mate
is assumed in its construction.
Source: def-trf-admissibility, base-change paragraph
(blueprint: lem-sf-etale-shriek-equals-pullback). -/
def exceptionalBaseChange {X Y X' Y' : SepFinType D.k}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (a : X' ⟶ X) (v : Y' ⟶ Y)
    (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left) :
    S.exceptional f ⋙ S.pullback a ⟶ S.pullback v ⋙ S.exceptional f' :=
  (mateEquiv (S.adjunction f) (S.adjunction f')
    (TwoSquare.mk _ _ _ _ (S.supportBaseChange a v sq).inv)).natTrans

/-- The canonical ordinary pullback comparison around the same square.
Source: def-trf-admissibility, ordinary adjunction comparison
(blueprint: lem-sf-etale-shriek-equals-pullback). -/
def pullbackBaseChange {X Y X' Y' : SepFinType D.k}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (a : X' ⟶ X) (v : Y' ⟶ Y)
    (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left) :
    S.pullback v ⋙ S.pullback f' ≅ S.pullback f ⋙ S.pullback a :=
  NatIso.ofComponents
    (fun K ↦ (trfFiniteCtfProperty A X'.obj.left).isoMk
      ((localizingClosureProEtale (trfFiniteCoefficient A) X'.obj.left).isoMk
        ((condensedAmbientPullbackComparison (trfFiniteCoefficient A)
          (CompactSupportComposition.square sq)).app K.obj.obj)))
    (fun b ↦ ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _
      ((condensedAmbientPullbackComparison (trfFiniteCoefficient A)
        (CompactSupportComposition.square sq)).hom.naturality b.hom.hom)))

/-- The canonical open adjunction for the chosen compact-support presentation.
First compare with the trivial open compactification, then restrict the native
extension-by-zero adjunction through the two full inclusions.
Source: def-trf-admissibility, unit/counit normalization
(blueprint: lem-sf-etale-shriek-equals-pullback). -/
def openAdjunction {U X : SepFinType D.k} (j : U ⟶ X) [IsOpenImmersion j.hom.left] :
    S.support j ⊣ S.pullback j := by
  let Λ := trfFiniteCoefficient A
  let l : S.localizingSupport j ≅
      localizingLowerShriek Λ (Compactification.ofIsOpenImmersion j.hom.left)
        (S.comparisons.preserves j (Compactification.ofIsOpenImmersion j.hom.left)).1 :=
    NatIso.ofComponents
      (fun K ↦ (localizingClosureProEtale Λ X.obj.left).isoMk
        ((S.comparisons.comparison j (S.compactification j)
          (Compactification.ofIsOpenImmersion j.hom.left)).app K))
      (fun b ↦ ObjectProperty.hom_ext _
        ((S.comparisons.comparison j (S.compactification j)
          (Compactification.ofIsOpenImmersion j.hom.left)).hom.naturality b))
  let adjLoc : S.localizingSupport j ⊣ S.localizingPullback j :=
    (((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.hom.left).ofNatIsoLeft
      (mateOpenTrivialLowerShriek Λ j.hom.left).symm).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory Λ j.hom.left).symm).restrictFullyFaithful
          (localizingClosureProEtale Λ U.obj.left).fullyFaithfulι
          (localizingClosureProEtale Λ X.obj.left).fullyFaithfulι (Iso.refl _) (Iso.refl _)
      |>.ofNatIsoLeft l.symm
  exact adjLoc.restrictFullyFaithful (trfFiniteCtfProperty A U.obj.left).fullyFaithfulι
    (trfFiniteCtfProperty A X.obj.left).fullyFaithfulι (Iso.refl _) (Iso.refl _)

/-- The unique open comparison preserving the specified adjunction counits.
Source: def-trf-admissibility, open normalization
(blueprint: lem-sf-etale-shriek-equals-pullback). -/
def openComparison {U X : SepFinType D.k} (j : U ⟶ X) [IsOpenImmersion j.hom.left] :
    S.exceptional j ≅ S.pullback j :=
  (S.adjunction j).rightAdjointUniq (S.openAdjunction j)

end TrfFiniteExceptionalDatum
end WeilConjectures
