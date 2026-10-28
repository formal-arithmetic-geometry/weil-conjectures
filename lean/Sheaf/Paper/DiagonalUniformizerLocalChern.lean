/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.Paper.DiagonalUniformizerAdjunctConditions

/-! # Reduction of a local completed Chern class

Source: diagonal tower coefficient changes proof (1), reduction of the section class.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint RestrictionSquare.mate CompletedRealization.singleUnit
  CompletedRealization.shiftedLine FiniteRealization.derivedUnit

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
  [DiagonalTraceLocalizations l Y]
  [DiagonalTraceLocalizations l (ProjectiveLine Y)]


namespace UniformizerChernNormalizationData

abbrev LocalFiniteArrow (s : UniformizerChernNormalizationData l Y) :=
  Etale.ordinaryFiniteUnit (ULift.{u + 1} (completedResidue l s.E s.π s.n))
      (ProjectiveLine Y) ⟶
    Etale.p1DecompositionTwist (ULift.{u + 1} (completedResidue l s.E s.π s.n))
      (l ^ (s.n + 1)) s.hA (ProjectiveLine Y) 1 2

abbrev LocalComposite (s : UniformizerChernNormalizationData l Y)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧) :=
  (s.localUnitInv l Y ≫ (s.localFunctor l Y).map z) ≫ s.localLine l Y

abbrev FiniteComparison (s : UniformizerChernNormalizationData l Y)
    (k : LocalFiniteArrow l Y s) :=
  (geoP1Comparison (ULift.{u + 1} (completedResidue l s.E s.π s.n))
    (ProjectiveLine Y)).map k

end UniformizerChernNormalizationData

@[irreducible]
def LocalFiniteChernSpec
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (X : Scheme.{u})
    (hP : IsUnit (N : Γ(ProjectiveLine X, ⊤)))
    (k : Etale.ordinaryFiniteUnit A (ProjectiveLine X) ⟶
      Etale.p1DecompositionTwist A N hA (ProjectiveLine X) 1 2) : Prop :=
  Etale.ordinaryFiniteP1ChernSpec A N hA X hP k

namespace UniformizerChernNormalizationData

abbrev LocalFiniteChernSpecCanonical
    (s : UniformizerChernNormalizationData l Y)
    (k : LocalFiniteArrow l Y s) : Prop :=
  LocalFiniteChernSpec
    (ULift.{u + 1} (completedResidue l s.E s.π s.n))
    (l ^ (s.n + 1)) s.hA Y
    (by simpa only [map_natCast] using
      s.hYpow.map (ProjectiveLine Y ↘ Y).appTop.hom) k

/-- The completed normalized arrow has a finite comparison factor.
Source: diagonal tower coefficient changes proof (1), reduction of the section class.
(blueprint: lem-diagonal-uniformizer-local-chern-transport).

The proof uses a common K-flat model and the coefficient and root cone endpoint
normalizations to construct the finite arrow. The displayed statement is only
the existence part; identification of the arrow is a separate theorem below. -/
theorem localChern_transport_exists
    (s : UniformizerChernNormalizationData l Y)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧)
    (hz : s.LocalNormalized l Y
      (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) s.tq.chernX
        (SpTowerClasses.hyperplanePic Y)) z) :
    ∃ k : LocalFiniteArrow l Y s,
      LocalComposite l Y s z = FiniteComparison l Y s k := by
  sorry

/-- The finite factor has the normalized finite Kummer specification.

Source: diagonal tower coefficient changes proof (1), finite Kummer normalization.
(blueprint: lem-diagonal-uniformizer-local-chern-finite-spec).

The completed transport equality is evaluated at the integral adjunct. The
coefficient-one equation for the completed factor descends through the ordinary
finite quotient, while the endpoint normalization identifies the resulting
arrow with the ordinary finite Kummer specification. -/
theorem localChern_transport_finite_spec
    {s : UniformizerChernNormalizationData l Y}
    {z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧}
    {k : LocalFiniteArrow l Y s}
    (hk : LocalComposite l Y s z = FiniteComparison l Y s k) :
    LocalFiniteChernSpecCanonical l Y s k := by
  sorry

/-- A finite normalized factor has the canonical comparison image.

Source: diagonal tower coefficient changes proof (1), finite Kummer normalization.
(blueprint: lem-diagonal-uniformizer-local-chern-finite-spec-unique-map).

The ordinary finite class comparison is bijective. Applying its uniqueness to
`hk` identifies the finite arrow with the canonical projective-line trace arrow;
functoriality of `geoP1Comparison` maps this equality to the displayed result. -/
theorem localChern_transport_finite_spec_unique_map
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hY : IsUnit (N : Γ(Y, ⊤)))
    (hP : IsUnit (N : Γ(ProjectiveLine Y, ⊤)))
    {k : Etale.ordinaryFiniteUnit A (ProjectiveLine Y) ⟶
      Etale.p1DecompositionTwist A N hA (ProjectiveLine Y) 1 2}
    (hk : LocalFiniteChernSpec A N hA Y hP k) :
    (geoP1Comparison A (ProjectiveLine Y)).map k =
      (geoP1Comparison A (ProjectiveLine Y)).map
        (geoP1EtaleChern A N hN hA Y hY) := by
  sorry

/-- The finite factor is the positive finite Kummer class.
Source: diagonal tower coefficient changes proof (1), reduction of the section class.
(blueprint: lem-diagonal-uniformizer-local-chern-identification).

The coefficient-one and integral-root equations identify the finite factor with
the Kummer boundary of the hyperplane class. This is a finite-level statement,
strictly below the completed local Chern equality. -/
theorem localChern_transport_identification
    (s : UniformizerChernNormalizationData l Y)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧)
    (hz : s.LocalNormalized l Y
      (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) s.tq.chernX
        (SpTowerClasses.hyperplanePic Y)) z)
    {k : LocalFiniteArrow l Y s}
    (hk : LocalComposite l Y s z = FiniteComparison l Y s k) :
    FiniteComparison l Y s k =
      (geoP1Comparison (ULift.{u + 1} (completedResidue l s.E s.π s.n))
        (ProjectiveLine Y)).map
        (geoP1EtaleChern (ULift.{u + 1} (completedResidue l s.E s.π s.n))
          (l ^ (s.n + 1)) (pow_pos (Fact.out : l.Prime).pos _) s.hA Y s.hYpow) := by
  let _ := hz
  have hspec := localChern_transport_finite_spec l Y (s := s) (z := z) (k := k) hk
  unfold FiniteComparison
  apply localChern_transport_finite_spec_unique_map (Y := Y)
    (A := ULift.{u + 1} (completedResidue l s.E s.π s.n))
    (N := l ^ (s.n + 1)) (hN := pow_pos (Fact.out : l.Prime).pos _)
    (hA := s.hA) (hY := s.hYpow)
    (hP := by simpa only [map_natCast] using
      s.hYpow.map (ProjectiveLine Y ↘ Y).appTop.hom) (k := k)
  simpa only [LocalFiniteChernSpecCanonical] using hspec

theorem localChern
    (s : UniformizerChernNormalizationData l Y)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧)
    (hz : s.LocalNormalized l Y
      (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) s.tq.chernX
        (SpTowerClasses.hyperplanePic Y)) z) : s.LocalChernNormalized l Y z := by
  obtain ⟨k, hk⟩ := localChern_transport_exists l Y s z hz
  unfold UniformizerChernNormalizationData.LocalChernNormalized
  simpa only [LocalComposite, FiniteComparison] using
    hk.trans (localChern_transport_identification (l := l) (Y := Y) s z hz hk)


end UniformizerChernNormalizationData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients


