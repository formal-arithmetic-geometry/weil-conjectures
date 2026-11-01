/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SmoothPurity.Supporting.ConstructibleIntervalsUnordered
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField

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

namespace TrfExceptionalStage

variable {l E n} {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f]

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

namespace TrfExceptionalStage
variable {l E n} {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  [HasCompactification f] [HasCompactification f'] [QuasiCompact f] [QuasiCompact f']

end TrfExceptionalStage

end WeilConjectures
