/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Sheaf.AlgebraicGeometry.CompactifiableOverField

/-!
# Constructible exceptional admissibility for the trace formula

Source: blueprint main-20261015, sec-six-functors-basics/sk-def-sf-admissible,
`def-trf-admissibility.md` (blueprint: def-trf-admissibility).

We use the canonical fixed-scalar presentation of the intrinsic finite-Tor category.
The coefficient at index `n` is the positive stage `A_{E,n+1}`. The right functor is
literally `sfFiniteExceptionalAt`, never an unspecified pro-etale right adjoint.
Composition and base change below are constructions from the specified left comparisons,
using `conjugateIsoEquiv` and composite adjunctions. Availability of the datum is the
separate exceptional-existence and preservation theorem, not an extra geometric hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- The recorded intrinsic finite-Tor predicate in its canonical fixed-scalar coordinates.
This is inverse image along the published coefficient realization, not another definition
of constructibility or Tor amplitude. Source: blueprint def-trf-admissibility, finite stage
(blueprint: def-trf-admissibility). -/
def trfFiniteTorFixed (T : Scheme.{u}) :
    ObjectProperty (_root_.DerivedCategory (Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))) :=
  fun K ↦ finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) T
    ((sfIntrinsicDerivedEquivalence T (Padic.coefficientExtensionRing l E (n + 1))).functor.obj K)

/-- The specified constructible exceptional functor at the chosen compactification.
The etale left-adjoint instance is the finite-coefficient existence theorem.
Source: blueprint def-trf-admissibility and def-weil-exceptional-inverse-image
(blueprint: def-trf-admissibility). -/
abbrev trfExceptional {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :=
  letI : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
      (HasCompactification.compactification f)).IsLeftAdjoint :=
    Etale.isLeftAdjoint_rightDerivedLowerShriek f
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
  ProEtale.sfFiniteExceptionalAt
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
    (HasCompactification.compactification f)

/-- The finite-stage adjunction datum, on the actual full finite-Tor subcategories.
The origin field records the already established origin theorem needed to restrict the
canonical compositor and exchange. Both preservation fields are properties of specified
functors, not choices of replacement functors. The `adjunction` supplies natural unit and
counit and both triangle identities. Source: blueprint def-trf-admissibility, paragraph 2
(blueprint: def-trf-admissibility). -/
structure TrfExceptionalStage {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] where
  origin : trfFiniteTorFixed l E n X ≤
    ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X
  supportPreserves (K : (trfFiniteTorFixed l E n X).FullSubcategory) :
    trfFiniteTorFixed l E n Y
      ((ProEtale.rightDerivedLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
        f).obj K.obj)
  exceptionalPreserves (K : (trfFiniteTorFixed l E n Y).FullSubcategory) :
    trfFiniteTorFixed l E n X ((trfExceptional l E n f).obj K.obj)
  adjunction :
    (trfFiniteTorFixed l E n Y).lift
        ((trfFiniteTorFixed l E n X).ι ⋙ ProEtale.rightDerivedLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
          f) supportPreserves ⊣
      (trfFiniteTorFixed l E n X).lift
        ((trfFiniteTorFixed l E n Y).ι ⋙ trfExceptional l E n f) exceptionalPreserves

namespace TrfExceptionalStage

variable {l E n} {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f]

/-- The actual restriction of compact support; maps are all ambient derived maps.
Source: blueprint def-trf-admissibility (blueprint: def-trf-admissibility). -/
def support (D : TrfExceptionalStage l E n f) :=
  (trfFiniteTorFixed l E n Y).lift
    ((trfFiniteTorFixed l E n X).ι ⋙ ProEtale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) f)
    D.supportPreserves

/-- The restriction of the specified exceptional inverse image.
Source: blueprint def-trf-admissibility (blueprint: def-trf-admissibility). -/
def exceptional (D : TrfExceptionalStage l E n f) :=
  (trfFiniteTorFixed l E n X).lift
    ((trfFiniteTorFixed l E n Y).ι ⋙ trfExceptional l E n f) D.exceptionalPreserves

/-- Restrict the specified origin compositor and take its adjunction conjugate.
Its direction is `R(hf)^! ≅ Rf^! Rh^!`. No isomorphism is chosen freely.
The arguments for `h` and `hf` are the same finite-stage data for those morphisms.
Source: blueprint def-trf-admissibility, composition paragraph
(blueprint: def-trf-admissibility). -/
def composition (D : TrfExceptionalStage l E n f) {Z : Scheme.{u}} (h : Y ⟶ Z)
    [HasCompactification h] [HasCompactification (f ≫ h)] [QuasiCompact f] [QuasiCompact h]
    (H : TrfExceptionalStage l E n h) (C : TrfExceptionalStage l E n (f ≫ h)) :
    C.exceptional ≅ H.exceptional ⋙ D.exceptional :=
  conjugateIsoEquiv C.adjunction (D.adjunction.comp H.adjunction)
    (((trfFiniteTorFixed l E n Z).fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft (ObjectProperty.ιOfLE D.origin)
        (ProEtale.originCompositionAmbient
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) f h)))

end TrfExceptionalStage

/-- Restrictions of the ordinary pullback/direct-image pair, with its actual derived
module adjunction. Only preservation proofs are stored; the adjunction below is obtained
by fully faithful restriction of the published derived adjunction.
Source: blueprint def-trf-admissibility, base-change paragraph
(blueprint: def-trf-admissibility). -/
structure TrfOrdinaryStage {U V : Scheme.{u}} (g : U ⟶ V) where
  pullbackPreserves (K : (trfFiniteTorFixed l E n V).FullSubcategory) :
    trfFiniteTorFixed l E n U
      (((ProEtale.upperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
        g).leftDerivedFunctor).obj K.obj)
  directImagePreserves (K : (trfFiniteTorFixed l E n U).FullSubcategory) :
    trfFiniteTorFixed l E n V
      (((ProEtale.lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
        g).rightDerivedFunctor).obj K.obj)

namespace TrfOrdinaryStage
variable {l E n} {U V : Scheme.{u}} {g : U ⟶ V}

/-- The actual restricted ordinary derived pullback.
Source: blueprint def-trf-admissibility (blueprint: def-trf-admissibility). -/
def pullback (D : TrfOrdinaryStage l E n g) :=
  (trfFiniteTorFixed l E n U).lift
    ((trfFiniteTorFixed l E n V).ι ⋙ (ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
      g).leftDerivedFunctor) D.pullbackPreserves

/-- The actual restricted ordinary derived direct image.
Source: blueprint def-trf-admissibility (blueprint: def-trf-admissibility). -/
def directImage (D : TrfOrdinaryStage l E n g) :=
  (trfFiniteTorFixed l E n V).lift
    ((trfFiniteTorFixed l E n U).ι ⋙ (ProEtale.lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
      g).rightDerivedFunctor) D.directImagePreserves

/-- Restrict the canonical ordinary derived module adjunction, including its maps.
Source: blueprint def-trf-admissibility (blueprint: def-trf-admissibility). -/
def adjunction (D : TrfOrdinaryStage l E n g) : D.pullback ⊣ D.directImage :=
  (ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
    g).restrictFullyFaithful (trfFiniteTorFixed l E n V).fullyFaithfulι
      (trfFiniteTorFixed l E n U).fullyFaithfulι (Iso.refl _) (Iso.refl _)

end TrfOrdinaryStage

/-- Descend the specified compactification comparison along the origin equivalence.
Full faithfulness fixes its components on all ambient morphisms between origin objects.
Source: blueprint def-trf-admissibility, compact-support comparisons
(blueprint: def-trf-admissibility). -/
def trfOriginCompactificationComparison {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) :
    (ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
      X).ι ⋙ ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) c ≅
    (ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
      X).ι ⋙ ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) d :=
  ((ProEtale.comparisonUpperStarPlusEtaleOrigin
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
    X).asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso
      (ProEtale.compactSupportSiteComparison
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) c ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) c d) _ ≪≫
        Functor.associator _ _ _ ≪≫
        (ProEtale.compactSupportSiteComparison
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) d).symm)

namespace TrfExceptionalStage
variable {l E n} {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  [HasCompactification f] [HasCompactification f'] [QuasiCompact f] [QuasiCompact f']

/-- The conjugate of compact-support exchange under the two composite adjunctions.
Its type is `Rg'_* Rf'^! ≅ Rf^! Rg_*`, rather than the other exceptional mate.
The left comparison is the specified proper/open compactification exchange, followed
by the canonical comparison to the chosen primed compactification. Its invertibility
on each input is finite-level base change applied to the origin field.
Source: blueprint def-trf-admissibility, base-change paragraph
(blueprint: def-trf-admissibility). -/
def baseChange (D : TrfExceptionalStage l E n f) (sq : IsPullback g' f' f g)
    (D' : TrfExceptionalStage l E n f')
    (G : TrfOrdinaryStage l E n g) (G' : TrfOrdinaryStage l E n g') :
    D'.exceptional ⋙ G'.directImage ≅ G.directImage ⋙ D.exceptional := by
  let α := ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
    sq (HasCompactification.compactification f)
  let β := Functor.whiskerLeft (trfFiniteTorFixed l E n X).ι α
  letI (K : (trfFiniteTorFixed l E n X).FullSubcategory) : IsIso (β.app K) :=
    ProEtale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) sq
      (HasCompactification.compactification f) K.obj (D.origin K.obj K.property)
  letI := NatIso.isIso_of_isIso_app β
  let γ := asIso β ≪≫ Functor.isoWhiskerLeft
    (G'.pullback ⋙ ObjectProperty.ιOfLE D'.origin)
    (trfOriginCompactificationComparison l E n
      ((HasCompactification.compactification f).ofIsPullback sq)
      (HasCompactification.compactification f'))
  exact conjugateIsoEquiv (G'.adjunction.comp D'.adjunction)
    (D.adjunction.comp G.adjunction)
    (((trfFiniteTorFixed l E n Y').fullyFaithfulι.whiskeringRight _).preimageIso γ)

end TrfExceptionalStage

/-- Exceptional admissibility at the positive coefficient stage `A_{E,n+1}`.
All geometry is the node's geometry: finite type over `k`, and separated finite type
for `f`; the target need not be separated. Compactifications name the representative
of the already specified functor. The preceding methods supply its canonical composition
and base-change exchange when applied to the corresponding data for the other arrows.
Source: blueprint def-trf-admissibility (blueprint: def-trf-admissibility). -/
def IsExceptionallyAdmissibleAt (F : FiniteFieldDatum.{u}) (_hl : l ≠ F.p)
    (X Y : Over (Spec (.of F.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    : Prop :=
  letI := @hasCompactification_of_finiteType_over_field F.k inferInstance X.left Y.left
    ⟨X.hom⟩ ⟨Y.hom⟩ (inferInstance : LocallyOfFiniteType X.hom)
    (inferInstance : QuasiCompact X.hom) (inferInstance : LocallyOfFiniteType Y.hom)
    (inferInstance : QuasiCompact Y.hom) f.left inferInstance inferInstance inferInstance
  Nonempty (TrfExceptionalStage l E n f.left)

/-- Exceptional admissibility at all finite coefficient stages, with one pair of signed
bounds independent of `n`. Cohomological intervals concern every constructible input;
Tor intervals concern finite-Tor constructible inputs. Both predicates are the recorded
intrinsic predicates, evaluated through the canonical realization. No ambient FullCD
condition or unbounded pro-etale right adjoint enters.
Source: blueprint def-trf-admissibility, uniform-bounds paragraph
(blueprint: def-trf-admissibility). -/
def IsExceptionallyAdmissible (F : FiniteFieldDatum.{u}) (_hl : l ≠ F.p)
    (X Y : Over (Spec (.of F.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    : Prop :=
  letI := @hasCompactification_of_finiteType_over_field F.k inferInstance X.left Y.left
    ⟨X.hom⟩ ⟨Y.hom⟩ (inferInstance : LocallyOfFiniteType X.hom)
    (inferInstance : QuasiCompact X.hom) (inferInstance : LocallyOfFiniteType Y.hom)
    (inferInstance : QuasiCompact Y.hom) f.left inferInstance inferInstance inferInstance
  ∃ cminus cplus : ℤ, ∀ m : ℕ,
    Nonempty (TrfExceptionalStage l E m f.left) ∧
    ∀ (a b : ℤ), a ≤ b →
      (∀ K, constructibleInterval l E (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) Y.left a b
          ((sfIntrinsicDerivedEquivalence Y.left
            (Padic.coefficientExtensionRing l E (m + 1))).functor.obj K) →
        constructibleInterval l E (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) X.left
          (a + cminus) (b + cplus)
          ((sfIntrinsicDerivedEquivalence X.left
            (Padic.coefficientExtensionRing l E (m + 1))).functor.obj
              ((trfExceptional l E m f.left).obj K))) ∧
      (∀ K, trfFiniteTorFixed l E m Y.left K →
        HasProEtaleTorAmplitude Y.left (Padic.coefficientExtensionRing l E (m + 1))
          ((sfIntrinsicDerivedEquivalence Y.left
            (Padic.coefficientExtensionRing l E (m + 1))).functor.obj K) a b →
        HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (m + 1))
          ((sfIntrinsicDerivedEquivalence X.left
            (Padic.coefficientExtensionRing l E (m + 1))).functor.obj
              ((trfExceptional l E m f.left).obj K)) (a + cminus) (b + cplus))

end WeilConjectures
