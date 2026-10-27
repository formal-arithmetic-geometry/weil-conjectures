/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.CategoryTheory.SystemLevelLeftExtensionBasic
public import Sheaf.Paper.ExceptionalSystemTransport
public import Sheaf.Paper.ExceptionalFiniteScalarMates
public import Sheaf.SixFunctors.IntegralSystemOperations
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.EtaleSystemCofinalMate
public import Sheaf.Paper.CompletedScalarShiftCoordinates
public import Sheaf.Paper.CoefficientExtensionReductionData
public import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus

public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
import Sheaf.CategoryTheory.SystemSelectedAdjunctionIsos
import Sheaf.CategoryTheory.SystemSelectedNormalization
import Sheaf.Paper.RamifiedSystemRecoveryBounds
import Sheaf.Paper.FiniteCtfTriangulated

/-! # Integral scalar mates for the exceptional adjunction

Source: Zheng, Constructions 4.1 and 5.15, Lemma 5.22 and Propositions 5.24, 5.26
(blueprint: lem-sf-exceptional-integral-scalar-mates).

## Main definitions and statements

- `systemBounds`, `systemProperty`, `Recovery`: normalized ramified strict towers.
- `sequenceProperty`, `Reconstruction`, `Transported`: actual reduction/limit transport.
- `Mates`, `ReductionMates`, `SystemMates`: normalized scalar comparisons and equations.
- `exceptionalIntegralScalarMates`, `ramifiedRecovery`: the two clauses of the node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme Opposite SheafOfModules
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
attribute [instance] ConstructibleExceptionalCoefficients.Scalar.commShift
  ConstructibleExceptionalCoefficients.Scalar.additive
  ConstructibleExceptionalCoefficients.Operation.leftShift
  ConstructibleExceptionalCoefficients.Operation.rightShift

/-- The inherited shift on the actual finite or integral full inclusion.
Source: blueprint full finite-Tor categories
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
instance inclusionShift (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{u}) (s : RingStage.{u} l) :
    (RingStage.inclusion.{u} l Ω T s).CommShift ℤ :=
  match s with
  | .finite _ _ => inferInstance
  | .integral _ => inferInstance

variable (l : ℕ) [Fact l.Prime]

/-- The actual selected coefficient sheaves. Natural index n means exponent n+1.
Source: Zheng, Construction 4.1
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
abbrev rings (E : FieldStage.{u} l) (T : Scheme.{u}) (r : ℕ ↪o ℕ) :=
  selectedSystemRings.{u + 1, u, u + 1} (coefficientSequenceCommRingSystem l E.carrier T) r

/-- Evaluation on the actual selected strict-system localization.
Source: Zheng, Construction 4.1
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
abbrev evaluation (E : FieldStage.{u} l) (T : Scheme.{u}) (r : ℕ ↪o ℕ) (n : ℕ) :=
  derivedSystemEvaluation.{u + 1, u, u + 1} (rings l E T r) n

/-- The same four endpoints at every selected level, without enlarging an interval.
Source: Zheng, Proposition 5.24
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
def systemBounds (E : FieldStage.{u} l) (T : Scheme.{u}) (r : ℕ ↪o ℕ)
    (a b c d : ℤ) (M : DerivedCategory
      (StrictRingSystem.{u + 1, u, u + 1} (rings l E T r))) : Prop :=
  ∀ n : ℕ,
    finiteTorConstructible l E.carrier (r n + 1) (Nat.succ_pos _) T
      ((evaluation l E T r n).obj M) ∧
    ((evaluation l E T r n).obj M).IsGE a ∧
    ((evaluation l E T r n).obj M).IsLE b ∧
    HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E.carrier (r n + 1))
      ((evaluation l E T r n).obj M) c d

/-- Normalized strict quotient systems with common cohomological and Tor bounds.
Source: Zheng, Construction 4.1 and Proposition 5.24
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
def systemProperty (E : FieldStage.{u} l) (T : Scheme.{u})
    (S : SystemLevelLeftExtensionTheory.{u + 1, u, u + 1} (J := Scheme.ProEt.topology T))
    (r : ℕ ↪o ℕ) : ObjectProperty (DerivedCategory
      (StrictRingSystem.{u + 1, u, u + 1} (rings l E T r))) :=
  fun M ↦
    (∀ {m n : ℕ} (h : m ≤ n),
      IsIso (((systemDerivedTensorAdj.{u + 1, u, u + 1} S.scalar (rings l E T r) h).homEquiv
        _ _).symm ((S.transition (rings l E T r) h).app M))) ∧
    ∃ a b c d : ℤ, a ≤ b ∧ c ≤ d ∧ systemBounds l E T r a b c d M

/-- Canonical cofinal restriction and left recovery on normalized constructible systems.
The left functor is the existing selected derived extension: its evaluation,
transition and counit are exactly `selectedDerivedBelow`, `selectedTransition` and
`selectedDerivedTranspose`, with `systemNextSelected` the least admissible index.
Source: Zheng, Construction 4.1
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
structure Recovery (E : FieldStage.{u} l) (T : Scheme.{u})
    (S : SystemLevelLeftExtensionTheory.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology T)) (r : ℕ ↪o ℕ) where
  restricts : ∀ M,
    systemProperty l E T S ((OrderIso.refl ℕ).toOrderEmbedding) M →
      systemProperty l E T S r
        ((derivedSystemSubsequence (coefficientSequenceCommRingSystem l E.carrier T) r).obj M)
  recovers : ∀ N, systemProperty l E T S r N →
    systemProperty l E T S ((OrderIso.refl ℕ).toOrderEmbedding)
      ((S.selected (coefficientSequenceCommRingSystem l E.carrier T) r).derived.obj N)
  unit : ∀ N, systemProperty l E T S r N →
    IsIso ((S.selected (coefficientSequenceCommRingSystem l E.carrier T) r).adjunction.unit.app N)
  counit : ∀ M, systemProperty l E T S ((OrderIso.refl ℕ).toOrderEmbedding) M →
    IsIso ((S.selected (coefficientSequenceCommRingSystem l E.carrier T) r).adjunction.counit.app M)
  restriction_bounds : ∀ M (a b c d : ℤ),
    systemBounds l E T (OrderIso.refl ℕ).toOrderEmbedding a b c d M →
      systemBounds l E T r a b c d
        ((derivedSystemSubsequence (coefficientSequenceCommRingSystem l E.carrier T) r).obj M)
  recovery_bounds : ∀ N (a b c d : ℤ), systemProperty l E T S r N →
    systemBounds l E T r a b c d N →
      systemBounds l E T (OrderIso.refl ℕ).toOrderEmbedding a b c d
        ((S.selected (coefficientSequenceCommRingSystem l E.carrier T) r).derived.obj N)


/-- Normalized sequence-site modules, with one cohomological and one Tor interval.
This is the sequence-site presentation of the strict-system predicate above.
Source: Zheng, Construction 4.1 and Proposition 5.24
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
def sequenceProperty (E : FieldStage.{u} l) (T : Scheme.{u}) :
    ObjectProperty (coefficientSequenceDerived l E.carrier T) :=
  fun N ↦ IsNormalizedCoefficientSequence l E.carrier T N ∧
    ∃ a b c d : ℤ, a ≤ b ∧ c ≤ d ∧ ∀ n : ℕ,
      finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos _) T
        ((coefficientSequenceDerivedEvaluation l E.carrier T n).obj N) ∧
      ((coefficientSequenceDerivedEvaluation l E.carrier T n).obj N).IsGE a ∧
      ((coefficientSequenceDerivedEvaluation l E.carrier T n).obj N).IsLE b ∧
      HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E.carrier (n + 1))
        ((coefficientSequenceDerivedEvaluation l E.carrier T n).obj N) c d

/-- The specified reduction/limit equivalence with its actual unit and counit.
These equations specify the transport named in the hypothesis; they assume no
coefficient comparison or mate to be constructed by this lemma.
Source: Zheng, Construction 5.25 and Proposition 5.26
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
structure Reconstruction (E : FieldStage.{u} l) (T : Scheme.{u}) where
  calculus : CoefficientDerivedSystemCalculus l E.carrier T
  equivalence : finiteTorConstructibleIntegralCategory l E.carrier T ≌
    (sequenceProperty l E T).FullSubcategory
  reduction : equivalence.functor ⋙ (sequenceProperty l E T).ι =
    (finiteTorConstructibleIntegral l E.carrier T).ι ⋙ calculus.reduction
  limit : equivalence.inverse ⋙ (finiteTorConstructibleIntegral l E.carrier T).ι =
    (sequenceProperty l E T).ι ⋙ coefficientSequenceLimit l E.carrier T
  unit : ∀ K, HEq
    ((finiteTorConstructibleIntegral l E.carrier T).ι.map (equivalence.unit.app K))
    (calculus.adjunction.unit.app K.obj)
  counit : ∀ N, HEq ((sequenceProperty l E T).ι.map (equivalence.counit.app N))
    (calculus.adjunction.counit.app N.obj)
  evaluation (n : ℕ) : (sequenceProperty l E T).FullSubcategory ⥤
    finiteTorConstructibleCategory l E.carrier (n + 1) (Nat.succ_pos _) T
  evaluation_eq (n : ℕ) : evaluation n ⋙
      (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos _) T).ι =
    (sequenceProperty l E T).ι ⋙ coefficientSequenceDerivedEvaluation l E.carrier T n

variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Scalar comparisons for the fixed proper/open adjunctions. All scalars are
conclusions, with the exact published finite and completed realizations.
Source: Zheng, Lemma 5.22 and Proposition 5.26
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
structure Mates {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)) where
  scalar {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) (side : Bool) : Scalar.{u} l Ω a (endpoint X Y side)
  scalarShift {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) (side : Bool) : (scalar a ha side).realization.hom.CommShift ℤ
  finiteScalar_eq {s : RingStage.{u} l} (E : FieldStage.{u} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) (side : Bool) :
    (scalar (s := s) (t := .finite E n) a ha side).functor ⋙
        RingStage.inclusion.{u} l Ω (endpoint X Y side) (RingStage.finite E n) =
      RingStage.inclusion.{u} l Ω (endpoint X Y side) s ⋙
        pbcDerivedExtend (a.map (endpoint X Y side))
  finiteScalar_normalized {s : RingStage.{u} l} (E : FieldStage.{u} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) (side : Bool) :
    (scalar (s := s) (t := .finite E n) a ha side).realization =
      eqToIso (finiteScalar_eq (s := s) E n a ha side)
  integralScalar_eq (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (side : Bool) :
    (scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) side).functor ⋙
        RingStage.inclusion.{u} l Ω (endpoint X Y side) (RingStage.integral L) =
      RingStage.inclusion.{u} l Ω (endpoint X Y side) (RingStage.integral E) ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i (endpoint X Y side)
  integralScalar_normalized (E L : FieldStage.{u} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (side : Bool)
      (K : C.{u} l Ω (endpoint X Y side) (.integral E)) :
    HEq ((scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) side).realization.inv.app K)
      ((completedScalarComparison l E.carrier L.carrier i (endpoint X Y side)).app K.obj)
  comparison {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) :
    Comparison.{u} l Ω (operation s) (operation t)
      (scalar a ha true).functor (scalar a ha false).functor
  comparison_normalized {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) :
    QNormalized.{u} l Ω c a (scalar a ha true) (scalar a ha false)
      (left s) (left t) (comparison a ha)
  scalarComposition {s t r : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
      (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T ≫ b.map T = d.map T)
      (ha : Allowed l a) (hb : Allowed l b) (hd : Allowed l d) (side : Bool) :
    ScalarComposition.{u} l Ω h (endpoint X Y side)
      (scalar a ha side) (scalar b hb side) (scalar d hd side)
  cocycle {s t r : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
      (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T ≫ b.map T = d.map T)
      (ha : Allowed l a) (hb : Allowed l b) (hd : Allowed l d) :
    Cocycle.{u} l Ω (comparison a ha) (comparison b hb) (comparison d hd)
      (scalarComposition a b d h ha hb hd true).iso
      (scalarComposition a b d h ha hb hd false).iso
  scalarIdentity {s : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T = 𝟙 _) (ha : Allowed l a) (side : Bool) :
    ScalarIdentity.{u} l Ω h (endpoint X Y side) (scalar a ha side)
  identityLeft {s : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T = 𝟙 _) (ha : Allowed l a)
      (K : C.{u} l Ω X (s.stage l)) :
    (comparison a ha).q.hom.app K ≫
        (operation s).F.map ((scalarIdentity a h ha true).iso.hom.app K) =
      (scalarIdentity a h ha false).iso.hom.app ((operation s).F.obj K)
  identityRight {s : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T = 𝟙 _) (ha : Allowed l a)
      (L : C.{u} l Ω Y (s.stage l)) :
    (comparison a ha).b.hom.app L ≫
        (operation s).G.map ((scalarIdentity a h ha false).iso.hom.app L) =
      (scalarIdentity a h ha true).iso.hom.app ((operation s).G.obj L)

  tor_interval (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (side : Bool) (K : C.{u} l Ω (endpoint X Y side) (.integral E)) (a b : ℤ)
      (h : ∀ n : ℕ, HasProEtaleTorAmplitude (endpoint X Y side)
        (Padic.coefficientExtensionRing l E.carrier (n + 1))
        ((scalarReductionDerivedExtension l E.carrier (endpoint X Y side) n).obj K.obj) a b) :
    ∀ n : ℕ, HasProEtaleTorAmplitude (endpoint X Y side)
      (Padic.coefficientExtensionRing l L.carrier (n + 1))
      ((scalarReductionDerivedExtension l L.carrier (endpoint X Y side) n).obj
        ((scalar (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i) side).functor.obj K).obj) a b
  completed_shift (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (side : Bool) :
    ∃ eC : (integralScalarComplexFunctor l E.carrier L.carrier i
        (endpoint X Y side)).CommShift ℤ,
      (∀ (P : CochainComplex (integralTowerModules l E.carrier (endpoint X Y side)) ℤ)
        (m : ℤ), completedScalarShiftConeFormula i (endpoint X Y side) eC P m) ∧
      ∀ (P : CochainComplex (integralTowerModules l E.carrier (endpoint X Y side)) ℤ)
        (m : ℤ),
        (((completedOrdinaryScalarExtension l E.carrier L.carrier i
            (endpoint X Y side)).mapCochainComplexShiftIso m).hom.app P) ≫
            ((completedScalarChainComparison l E.carrier L.carrier i
              (endpoint X Y side)).app P)⟦m⟧' =
          (completedScalarChainComparison l E.carrier L.carrier i
            (endpoint X Y side)).app (P⟦m⟧) ≫
            (Functor.commShiftIso (integralScalarComplexFunctor l E.carrier L.carrier i
              (endpoint X Y side)) (self := eC) m).hom.app P

/-- The q arrow with the scalar shift witnesses supplied from its owning record.
Source: Zheng, Lemma 5.22
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
def Mates.q {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l)}
    {left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)}
    (d : Mates l Ω c operation left) {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)) (ha : Allowed l a) :=
  letI := (d.scalar a ha true).commShift
  letI := (d.scalar a ha false).commShift
  (d.comparison a ha).q

/-- The b arrow with the same explicitly supplied scalar shift witnesses.
Source: Zheng, Lemma 5.22
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
def Mates.b {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l)}
    {left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)}
    (d : Mates l Ω c operation left) {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)) (ha : Allowed l a) :=
  letI := (d.scalar a ha true).commShift
  letI := (d.scalar a ha false).commShift
  (d.comparison a ha).b

/-- The fixed system adjunction and its actual reconstruction, not scalar mates.
The evaluations include both adjunction equations; the proper/open word and the
prescribed integral compact support are fixed by their named realization maps.
Source: Zheng, Lemma 5.22, Construction 5.25 and Proposition 5.26
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
structure Transported (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)) where
  leftShift (s : RingStage.{u} l) : (left s).hom.CommShift ℤ
  reconstruction (E : FieldStage.{u} l) (side : Bool) :
    Reconstruction l E (endpoint X Y side)
  operations (E : FieldStage.{u} l) : IntegralSystemRealization.Operations l E.carrier
  realizations (E : FieldStage.{u} l) :
    IntegralSystemRealization.Realizations l E.carrier D (operations E)
  F (E : FieldStage.{u} l) : (sequenceProperty l E X).FullSubcategory ⥤
    (sequenceProperty l E Y).FullSubcategory
  G (E : FieldStage.{u} l) : (sequenceProperty l E Y).FullSubcategory ⥤
    (sequenceProperty l E X).FullSubcategory
  adjunction (E : FieldStage.{u} l) : F E ⊣ G E
  support (E : FieldStage.{u} l) : F E ⋙ (sequenceProperty l E Y).ι =
    (sequenceProperty l E X).ι ⋙
      (IntegralSystemRealization.Operations.shriek l E.carrier (operations E) c.i ⋙
        IntegralSystemRealization.Operations.push l E.carrier (operations E) c.g)
  realizeF (E : FieldStage.{u} l) : (operation (.integral E)).F ≅
    PurReconstruction.realized (reconstruction E true).equivalence
      (reconstruction E false).equivalence (F E)
  realizeG (E : FieldStage.{u} l) : (operation (.integral E)).G ≅
    PurReconstruction.realized (reconstruction E false).equivalence
      (reconstruction E true).equivalence (G E)
  adjunction_eq (E : FieldStage.{u} l) : (operation (.integral E)).adjunction =
    ((PurReconstruction.realizedAdjunction (reconstruction E true).equivalence
      (reconstruction E false).equivalence (adjunction E)).ofNatIsoLeft
        (realizeF E).symm).ofNatIsoRight (realizeG E).symm
  reductionF (E : FieldStage.{u} l) :
    (operation (.integral E)).F ⋙ (reconstruction E false).equivalence.functor ≅
      (reconstruction E true).equivalence.functor ⋙ F E
  reductionF_eq (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    (reductionF E).hom.app K =
      (reconstruction E false).equivalence.functor.map ((realizeF E).hom.app K) ≫
        (reconstruction E false).equivalence.counit.app
          ((F E).obj ((reconstruction E true).equivalence.functor.obj K))
  reductionG (E : FieldStage.{u} l) :
    (operation (.integral E)).G ⋙ (reconstruction E true).equivalence.functor ≅
      (reconstruction E false).equivalence.functor ⋙ G E
  reductionG_eq (E : FieldStage.{u} l) (K : C.{u} l Ω Y (.integral E)) :
    (reductionG E).hom.app K =
      (reconstruction E true).equivalence.functor.map ((realizeG E).hom.app K) ≫
        (reconstruction E true).equivalence.counit.app
          ((G E).obj ((reconstruction E false).equivalence.functor.obj K))
  evaluationF (E : FieldStage.{u} l) (n : ℕ) :
    F E ⋙ (reconstruction E false).evaluation n ≅
      (reconstruction E true).evaluation n ⋙ (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F
  evaluationG (E : FieldStage.{u} l) (n : ℕ) :
    G E ⋙ (reconstruction E true).evaluation n ≅
      (reconstruction E false).evaluation n ⋙ (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G
  evaluation_unit (E : FieldStage.{u} l) (n : ℕ)
      (K : (sequenceProperty l E X).FullSubcategory) :
    ((reconstruction E true).evaluation n).map ((adjunction E).unit.app K) ≫
      (evaluationG E n).hom.app ((F E).obj K) ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G.map
        ((evaluationF E n).hom.app K) =
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.unit.app
        (((reconstruction E true).evaluation n).obj K)
  evaluation_counit (E : FieldStage.{u} l) (n : ℕ)
      (K : (sequenceProperty l E Y).FullSubcategory) :
    (evaluationF E n).hom.app ((G E).obj K) ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F.map
        ((evaluationG E n).hom.app K) ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.counit.app
        (((reconstruction E false).evaluation n).obj K) =
      ((reconstruction E false).evaluation n).map ((adjunction E).counit.app K)
  evaluation_support (E : FieldStage.{u} l) (n : ℕ)
      (K : (sequenceProperty l E X).FullSubcategory) :
    HEq ((finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) Y).ι.map
        ((evaluationF E n).hom.app K) ≫
      (left (.finite E ⟨n + 1, Nat.succ_pos n⟩)).hom.app
        (((reconstruction E true).evaluation n).obj K))
      ((IntegralSystemRealization.supportEvaluation l E.carrier (operations E) c n).hom.app K.obj)
  integralLeft (E : FieldStage.{u} l) :
    (operation (.integral E)).F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
      PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier
  integralLeft_normalized (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    (sfIntegralConstructible l E.carrier Y).ι.map ((integralLeft E).hom.app K) =
      (left (.integral E)).hom.app K ≫
        (sfQcqsCompactSupportRealization l E.carrier D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app
          ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K)
  /-- The canonical realization of the input and its open extension is defined
      on precisely the normalized constructible finite-Tor transport domain. -/
  inputGood (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    IntegralSystemRealization.Good l E.carrier X
      (((reconstruction E true).equivalence.functor.obj K).obj)
  openGood (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    IntegralSystemRealization.Good l E.carrier c.Z
      ((IntegralSystemRealization.Operations.shriek l E.carrier (operations E) c.i).obj
        (((reconstruction E true).equivalence.functor.obj K).obj))
  /-- This square fixes the integral left realization, including its sign, by the
      canonical proper conjugate, normalized open mate and reconstruction unit. -/
  integral_system_normalized (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    HEq ((finiteTorConstructibleIntegral l E.carrier Y).ι.map
        ((realizeF E).inv.app K) ≫ (left (.integral E)).hom.app K)
      (((realizations E).realizationModel.push l E.carrier c.g).hom.app
          ((IntegralSystemRealization.Operations.shriek l E.carrier (operations E) c.i).obj
            (((reconstruction E true).equivalence.functor.obj K).obj)) ≫
        (PurCompactSupport.push (PurCompactSupport.completed l E.carrier) c.g).map
          (((realizations E).openRealization c.i
              (IntegralSystemRealization.compactOpenQuasiCompact c inferInstance)
              (((reconstruction E true).equivalence.functor.obj K).obj)
              (inputGood E K) (openGood E K)).hom ≫
            ((PurCompactSupport.openExtension (PurCompactSupport.completed l E.carrier)
              c.i).mapDerivedCategory).map
              ((eqToIso (congrArg
                  (fun H ↦ H.obj ((reconstruction E true).equivalence.functor.obj K))
                  (reconstruction E true).limit)).inv ≫
                (finiteTorConstructibleIntegral l E.carrier X).ι.map
                  ((reconstruction E true).equivalence.unitIso.inv.app K))))

/-- One actual ramified finite map, allowing any zero-based target index m
whose positive exponent is e(n+1). The heterogeneous equality is only the
transport across this explicit exponent equality, never an identification en=n.
Source: Zheng, Construction 4.1
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
structure RamifiedMap (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e) where
  n : ℕ
  m : ℕ
  exponent : m + 1 = e * (n + 1)
  change : PurCompactSupport.Change
    ((RingStage.finite E ⟨n + 1, Nat.succ_pos n⟩).coefficients l)
    ((RingStage.finite L ⟨m + 1, Nat.succ_pos m⟩).coefficients l)
  allowed : Allowed l change
  actual : ∀ T : Scheme.{u}, HEq (change.map T)
    ((PurCompactSupport.finiteChange l E.carrier L.carrier i e he e.pos
      (n + 1) (Nat.succ_pos n)).map T)

/-- Evaluation is the integral reduction comparison, including the given system
adjunction's unit and counit, with the actual reduction/limit projection counit.
Source: Zheng, Lemma 5.22 and Proposition 5.26
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
structure ReductionMates (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (tr : Transported l Ω D hl c operation left) (d : Mates l Ω c operation left)
    (E : FieldStage.{u} l) (n : ℕ) where
  evaluation (side : Bool) :
    (d.scalar (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
      (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) side).functor ≅
    (tr.reconstruction E side).equivalence.functor ⋙ (tr.reconstruction E side).evaluation n
  evaluation_normalized (side : Bool)
      (K : C.{u} l Ω (endpoint X Y side) (.integral E)) :
    HEq ((finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n)
      (endpoint X Y side)).ι.map ((evaluation side).inv.app K))
      (((tr.reconstruction E side).calculus.reductionEvaluation n).hom.app K.obj)
  q_evaluation (K : C.{u} l Ω X (.integral E)) :
    (Mates.q l Ω d (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
      (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩)).hom.app K ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F.map
        ((evaluation true).hom.app K) =
    (evaluation false).hom.app ((operation (.integral E)).F.obj K) ≫
      ((tr.reconstruction E false).evaluation n).map ((tr.reductionF E).hom.app K) ≫
      (tr.evaluationF E n).hom.app ((tr.reconstruction E true).equivalence.functor.obj K)
  b_evaluation (N : C.{u} l Ω Y (.integral E)) :
    (Mates.b l Ω d (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
      (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩)).hom.app N ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G.map
        ((evaluation false).hom.app N) =
    (evaluation true).hom.app ((operation (.integral E)).G.obj N) ≫
      ((tr.reconstruction E true).evaluation n).map ((tr.reductionG E).hom.app N) ≫
      (tr.evaluationG E n).hom.app ((tr.reconstruction E false).equivalence.functor.obj N)

/-- The whole-system completed coefficient comparisons, before any total limit.
The scalar realization is the existing representative-normalized coherent counit,
so these are comparisons for the published strict-tower functor, not arbitrary maps.
Source: Zheng, Construction 4.1, Lemma 5.22 and Proposition 5.26
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
structure SystemMates (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (tr : Transported l Ω D hl c operation left) (d : Mates l Ω c operation left)
    (red : ∀ (E : FieldStage.{u} l) (n : ℕ),
      ReductionMates l Ω D hl c operation left tr d E n)
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) where
  coefficient (side : Bool) : CoefficientExtensionSystems l E.carrier L.carrier i
    (endpoint X Y side)
  coefficient_model (side : Bool) : CoefficientExtensionReductionData
    l E.carrier L.carrier i (endpoint X Y side)
    (tr.reconstruction E side).calculus (tr.reconstruction L side).calculus (coefficient side)
  scalar (side : Bool) : (sequenceProperty l E (endpoint X Y side)).FullSubcategory ⥤
    (sequenceProperty l L (endpoint X Y side)).FullSubcategory
  scalar_eq (side : Bool) : scalar side ⋙ (sequenceProperty l L (endpoint X Y side)).ι =
    (sequenceProperty l E (endpoint X Y side)).ι ⋙ (coefficient side).scalar.T
  reduction (side : Bool) :
    (d.scalar (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i)
      (Allowed.integral E L i) side).functor ⋙
        (tr.reconstruction L side).equivalence.functor ≅
      (tr.reconstruction E side).equivalence.functor ⋙ scalar side
  reduction_normalized (side : Bool)
      (K : C.{u} l Ω (endpoint X Y side) (.integral E)) :
    HEq ((sequenceProperty l L (endpoint X Y side)).ι.map ((reduction side).hom.app K))
      ((coefficientExtensionReductionIso l E.carrier L.carrier i (endpoint X Y side)
        (tr.reconstruction E side).calculus (tr.reconstruction L side).calculus
        (coefficient side) (coefficient_model side)).hom.app K.obj)
  q : tr.F E ⋙ scalar false ≅ scalar true ⋙ tr.F L
  b : tr.G E ⋙ scalar true ≅ scalar false ⋙ tr.G L
  counit (N : (sequenceProperty l E Y).FullSubcategory) :
    q.hom.app ((tr.G E).obj N) ≫ (tr.F L).map (b.hom.app N) ≫
      (tr.adjunction L).counit.app ((scalar false).obj N) =
        (scalar false).map ((tr.adjunction E).counit.app N)
  q_reduction (K : C.{u} l Ω X (.integral E)) :
    (tr.reconstruction L false).equivalence.functor.map
        ((Mates.q l Ω d (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i)).hom.app K) ≫
      (tr.reductionF L).hom.app
        ((d.scalar (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i) true).functor.obj K) ≫
      (tr.F L).map ((reduction true).hom.app K) =
    (reduction false).hom.app ((operation (.integral E)).F.obj K) ≫
      (scalar false).map ((tr.reductionF E).hom.app K) ≫
        q.hom.app ((tr.reconstruction E true).equivalence.functor.obj K)
  b_reduction (N : C.{u} l Ω Y (.integral E)) :
    (tr.reconstruction L true).equivalence.functor.map
        ((Mates.b l Ω d (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i)).hom.app N) ≫
      (tr.reductionG L).hom.app
        ((d.scalar (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i) false).functor.obj N) ≫
      (tr.G L).map ((reduction false).hom.app N) =
    (reduction true).hom.app ((operation (.integral E)).G.obj N) ≫
      (scalar true).map ((tr.reductionG E).hom.app N) ≫
        b.hom.app ((tr.reconstruction E false).equivalence.functor.obj N)

  selected (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (side : Bool) :
    scalar side ⋙ (tr.reconstruction L side).evaluation z.m ≅
      (tr.reconstruction E side).evaluation z.n ⋙
        (d.scalar z.change z.allowed side).functor
  selected_square (e : ℕ+)
      (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (T : Scheme.{u}) :
    (PurCompactSupport.completedChange l E.carrier L.carrier i).map T ≫
        (PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m)).map T =
      (PurCompactSupport.reduction l E.carrier (z.n + 1) (Nat.succ_pos z.n)).map T ≫
        z.change.map T
  selected_balanced (e : ℕ+)
      (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (side : Bool)
      (K : C.{u} l Ω (endpoint X Y side) (.integral E)) :
    HEq ((finiteTorConstructible l L.carrier (z.m + 1) (Nat.succ_pos z.m)
      (endpoint X Y side)).ι.map
        ((red L z.m).evaluation side |>.hom.app
            ((d.scalar (s := .integral E) (t := .integral L)
              (PurCompactSupport.completedChange l E.carrier L.carrier i)
              (Allowed.integral E L i) side).functor.obj K)) ≫
      (finiteTorConstructible l L.carrier (z.m + 1) (Nat.succ_pos z.m)
        (endpoint X Y side)).ι.map
        (((tr.reconstruction L side).evaluation z.m).map ((reduction side).hom.app K) ≫
          (selected e he z side).hom.app
            ((tr.reconstruction E side).equivalence.functor.obj K) ≫
          (d.scalar z.change z.allowed side).functor.map
            (((red E z.n).evaluation side).inv.app K)))
      ((pbcDerivedExtend ((PurCompactSupport.reduction l L.carrier
          (z.m + 1) (Nat.succ_pos z.m)).map (endpoint X Y side))).map
        ((d.scalar (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i) side).realization.hom.app K) ≫
        (PurCompactSupport.tensorSquare
          ((PurCompactSupport.completedChange l E.carrier L.carrier i).map
            (endpoint X Y side)) (z.change.map (endpoint X Y side))
          ((PurCompactSupport.reduction l E.carrier (z.n + 1) (Nat.succ_pos z.n)).map
            (endpoint X Y side))
          ((PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m)).map
            (endpoint X Y side)) (selected_square e he z (endpoint X Y side))).hom.app K.obj)
  q_selected (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (N : (sequenceProperty l E X).FullSubcategory) :
    ((tr.reconstruction L false).evaluation z.m).map (q.hom.app N) ≫
      (tr.evaluationF L z.m).hom.app ((scalar true).obj N) ≫
      (operation (.finite L ⟨z.m + 1, Nat.succ_pos z.m⟩)).F.map
        ((selected e he z true).hom.app N) =
    (selected e he z false).hom.app ((tr.F E).obj N) ≫
      (d.scalar z.change z.allowed false).functor.map
        ((tr.evaluationF E z.n).hom.app N) ≫
      (Mates.q l Ω d z.change z.allowed).hom.app
        (((tr.reconstruction E true).evaluation z.n).obj N)
  b_selected (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (N : (sequenceProperty l E Y).FullSubcategory) :
    ((tr.reconstruction L true).evaluation z.m).map (b.hom.app N) ≫
      (tr.evaluationG L z.m).hom.app ((scalar false).obj N) ≫
      (operation (.finite L ⟨z.m + 1, Nat.succ_pos z.m⟩)).G.map
        ((selected e he z false).hom.app N) =
    (selected e he z true).hom.app ((tr.G E).obj N) ≫
      (d.scalar z.change z.allowed true).functor.map
        ((tr.evaluationG E z.n).hom.app N) ≫
      (Mates.b l Ω d z.change z.allowed).hom.app
        (((tr.reconstruction E false).evaluation z.n).obj N)

/-- Construction of the mate and finite-reduction data used by the integral scalar comparison.
Source: Zheng, Lemma 5.22 and Proposition 5.26; the finite reduction and completed scalar
transport steps of the exceptional coefficient construction.
(blueprint: lem-sf-exceptional-integral-scalar-mates-data).
The proof constructs the finite scalar maps from the ordinary etale adjunction, transports them
through the reduction/limit reconstruction, and assembles the integral scalar functor using the
published completed scalar comparison. The counit transpose and all shift witnesses are retained.
-/
theorem exceptionalIntegralScalarMates_data
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (transport : Transported l Ω D hl c operation left) :
    ∃ d : Mates l Ω c operation left,
      ∃ red : ∀ (E : FieldStage.{u} l) (n : ℕ),
        ReductionMates l Ω D hl c operation left transport d E n, True := by
  sorry

/-- Construction of the whole-system scalar mate from the integral mate data.
Source: Zheng, Construction 4.1, Lemma 5.22 and Proposition 5.26; the cofinal ramified
subsequence, finite-free comparison, and normalized system transport steps.
(blueprint: lem-sf-exceptional-integral-scalar-mates-system).
The proof transports finite-level mates along the normalized subsequence equivalence, uses the
completed scalar comparison to identify the chosen integral functor, and conjugates the system
counit equation through reconstruction. Balanced associativity supplies transitions and shifts.
-/
theorem exceptionalIntegralScalarMates_system
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (transport : Transported l Ω D hl c operation left)
    (d : Mates l Ω c operation left)
    (red : ∀ (E : FieldStage.{u} l) (n : ℕ),
      ReductionMates l Ω D hl c operation left transport d E n)
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    Nonempty (SystemMates l Ω D hl c operation left transport d red E L i) := by
  sorry

/-- Core integral scalar mate data before the arithmetic ramified-index witness.
Source: Zheng, Lemma 5.22 and Proposition 5.26. The proof follows the parent's
system transport, finite reduction, completed scalar comparison, reconstruction,
realization, and shift-coherence steps, omitting only the final explicit index choice.
(blueprint: lem-sf-exceptional-integral-scalar-mates-core). -/
theorem exceptionalIntegralScalarMates_core
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (transport : Transported l Ω D hl c operation left) :
    ∃ d : Mates l Ω c operation left,
      ∃ red : ∀ (E : FieldStage.{u} l) (n : ℕ),
        ReductionMates l Ω D hl c operation left transport d E n,
      ∀ (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier),
        Nonempty (SystemMates l Ω D hl c operation left transport d red E L i) := by
  obtain ⟨d, red, _⟩ := exceptionalIntegralScalarMates_data l Ω D hl c operation left transport
  refine ⟨d, red, ?_⟩
  intro E L i
  exact exceptionalIntegralScalarMates_system l Ω D hl c operation left transport d red E L i

private theorem restrictionBounds (E : FieldStage.{u} l) (T : Scheme.{u})
    (S : SystemLevelLeftExtensionTheory.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology T)) (r : ℕ ↪o ℕ)
    (M : DerivedCategory (StrictRingSystem.{u + 1, u, u + 1}
      (coefficientSequenceCommRingSystem l E.carrier T))) (a b c d : ℤ)
    (h : systemBounds l E T (OrderIso.refl ℕ).toOrderEmbedding a b c d M) :
    systemBounds l E T r a b c d
      ((derivedSystemSubsequence (coefficientSequenceCommRingSystem l E.carrier T) r).obj M) := by
  intro n
  obtain ⟨hf, hge, hle, htor⟩ := h (r n)
  let e := (S.selectedEvaluation (coefficientSequenceCommRingSystem l E.carrier T) r n).app M
  let : ObjectProperty.IsClosedUnderIsomorphisms
      (finiteTorConstructible l E.carrier (r n + 1) (Nat.succ_pos _) T) :=
    (finite_ctf_isTriangulated l E.carrier (r n + 1) (Nat.succ_pos _) T).1
  refine ⟨(finiteTorConstructible l E.carrier (r n + 1) (Nat.succ_pos _) T).prop_of_iso
    e.symm hf, ⟨(DerivedCategory.TStructure.t.ge a).prop_of_iso e.symm hge.ge⟩,
    ⟨(DerivedCategory.TStructure.t.le b).prop_of_iso e.symm hle.le⟩, htor.1, ?_⟩
  rintro N P ⟨q⟩ f hf hP A i hi
  exact htor.2 N P ⟨q ≪≫ e⟩ f hf hP A i hi

/-- Ramified restriction is an equivalence with the specified selected left extension.
Source: Zheng, Construction 4.1
(blueprint: lem-sf-exceptional-integral-scalar-mates).
Proof: at level m the counit is the normalization map from the least selected level
above m, and at selected level en the unit is the tensor unitor. Joint conservativity
makes both invertible. The transition formula preserves normalization; scalar extension
preserves finite constructibility and the original common cohomological and Tor bounds. -/
theorem ramifiedRecovery (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
    (S : SystemLevelLeftExtensionTheory.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology T)) :
    Nonempty (Recovery l L T S
      (Etale.SystemProjection.cofinalRamification e (Nat.one_le_iff_ne_zero.mpr e.ne_zero))) := by
  let B := coefficientSequenceCommRingSystem l L.carrier T
  let r := Etale.SystemProjection.cofinalRamification e
    (Nat.one_le_iff_ne_zero.mpr e.ne_zero)
  obtain ⟨hrestrict, hrecover⟩ := systemSelectedNormalization S B r
  obtain ⟨hunit, hcounit⟩ := systemSelectedAdjunctionIsos S B r
  have hbounds := ramifiedSystemRecoveryBounds l D hl E L i e he T S
  refine ⟨{
    restricts := ?_
    recovers := ?_
    unit := fun N _ ↦ hunit N
    counit := fun M hM ↦ hcounit M hM.1
    restriction_bounds := restrictionBounds l L T S r
    recovery_bounds := fun N a b c d hN hb ↦ hbounds N a b c d hN.1 hb }⟩
  · intro M hM
    obtain ⟨hnorm, a, b, c, d, hab, hcd, hb⟩ := hM
    exact ⟨hrestrict M hnorm, a, b, c, d, hab, hcd,
      restrictionBounds l L T S r M a b c d hb⟩
  · intro N hN
    obtain ⟨hnorm, a, b, c, d, hab, hcd, hb⟩ := hN
    exact ⟨hrecover N hnorm, a, b, c, d, hab, hcd, hbounds N a b c d hnorm hb⟩

/-- Integral scalar mates for the chosen proper/open adjunction and its realization.
Source: Zheng, Constructions 4.1 and 5.15, Lemma 5.22, Propositions 5.24 and 5.26
(blueprint: lem-sf-exceptional-integral-scalar-mates).

Proof, following the ten steps of the DAG node:

1. Use the given reduction/limit transport with the actual unit and counit specified by integral
reconstruction. For $a:R_E\to A_{E,n}$ let $T_{a,T}$ be the literal restriction of ordinary
derived tensor. Its output is the defining reduction of an integral finite-Tor object. The
evaluation comparisons identify $T_{a,Y}F_R$ with $F_{A_{E,n}}T_{a,X}$ and $T_{a,X}G_R$ with
$G_{A_{E,n}}T_{a,Y}$, with their units and counits. Call these maps $q_a,b_a$. The system-
transport theorem gives these as transported system adjunction maps, so the evaluated counit
equation is precisely $\epsilon_tF_t(b_a)q_{a,G_R}=T_{a,Y}\epsilon_R$. The reduction/limit counit
is the scalar adjunct of the actual limit projection, rather than an unspecified identification of
objects. The proper/open realization intertwines these units, counits and tensor maps; hence the
left realization of $q_a$ is the ambient proper scalar mate followed by the open tensor map. Uses:
lem-sf-exceptional-integral-reconstruction, lem-sf-exceptional-system-transport, lem-coef-derived-
system-evaluation-calculus, def-weil-finite-tor-amplitude, lem-sf-integral-compactification-
system-realization.

2. Put $B_m=A_{L,m}$ and $r(n)=en$. Apply the subsequence adjunction $L_r\dashv U_r$ to strict
systems, with $t(m)=\min\{n:en\ge m\}$. Its evaluation is
$e_mL_rN=B_m\otimes^L_{B_{et(m)}}N_{t(m)}$ with the stated selected-level transitions. On a
normalized $M$, the counit $L_rU_rM\to M$ evaluates to the normalization isomorphism
$B_m\otimes^L_{B_{et(m)}}M_{et(m)}\to M_m$. On a selected system $N$, $t(en)=n$, so the unit $N\to
U_rL_rN$ evaluates to the tensor unitor. Joint conservativity proves these are isomorphisms. The
transition formula shows $L_rN$ is normalized whenever $N$ is; testing its $m$th tensor with a
$B_m$-module is the same test on $N_{t(m)}$, so the common Tor interval is preserved. Its unit
test gives the same common cohomological interval, and its finite coefficients preserve
constructibility by the finite scalar lemma. Thus these adjunction maps restrict to inverse
equivalences on the normalized categories in the statement. Uses: lem-pur-system-level-left-
extension, lem-sf-exceptional-finite-scalar-mates.

3. At selected levels $R_L/\varpi_E^nR_L=A_{L,en}$ use the finite-free scalar comparison of the
ordinary etale system adjunction. The left map is the actual system coefficient projection $q$,
and the right map is the counit-normalized system transpose $b$; both are invertible and include
every transition. The cofinal-mate theorem identifies the right adjoint restricted from the full
$L$-tower with this selected-level right adjoint, preserving counits. Use the equivalence of Step
2 to recover the full tower; no level $en$ is identified with level $n$. Transport along the
etale/pro-etale system equivalence, with its actual units and counits. Tensor/pullback and
proper/open realization give the same scalar arrows there: finite-free coefficient extension is
tensor by the coefficient system, so it is among the tensor expressions of the realization
theorem. This produces an invertible system $q,b$ on the normalized pro-etale inputs, and its
counit equation holds as a derived-system equation before any total limit. Uses: lem-pur-etale-
coefficient-system-adjoint, lem-pur-etale-system-coefficient-projection, lem-pur-etale-system-
scalar-mate-coherence, lem-pur-etale-system-cofinal-mate, lem-sf-exceptional-system-transport,
lem-sf-integral-compactification-system-realization.

4. For completed extension choose exactly the published strict-tower functor $T_{L/E}$. The
canonical $\chi_{L/E}:S_{L/E}\to I_LT_{L/E}$ is a natural isomorphism on derived-complete inputs
by the finite-free completed-scalar comparison, where $S_{L/E}$ is ordinary derived extension
after inclusion. Constructibility is preserved by the integral scalar-extension theorem. The adic
Tor-bound theorem gives, at arbitrary level $m$ and any $n$ with $en\ge m$, the reduction
$K_n\otimes^L_{A_{E,n}}A_{L,m}$ and the same interval $[a,b]$. These facts verify that this chosen
functor restricts to the required categories. Set $\theta=\chi^{-1}$; the completed-scalar
normalization is then the specified one, without changing the scalar functor. Uses: lem-weil-
finite-free-completed-scalar-comparison, lem-weil-integral-scalar-extension-constructible, lem-
pur-adic-scalar-extension-tor-bound.

5. Apply the reconstruction equivalences to the actual system transformations of Step 3. Use their
units and counits to identify the resulting integral operations with the given $F_R,G_R$, and
identify their scalar functors with the choice in Step 4 as follows. For integral $K$ with flat-
term K-flat representative, $\chi$ gives $T_{L/E}K\cong K\otimes^L_{\widehat R_E}\widehat R_L$,
which is derived complete and lies in the integral category, so the reconstruction unit identifies
it with $\mathcal L_L\mathcal R_L$ of itself. Balanced associativity identifies $U_r\mathcal
R_L(K\otimes^L\widehat R_L)$ with the selected-level finite-free extension
$(K_n\otimes^L_{A_{E,n}}A_{L,en})_n$ of $\mathcal R_EK$, as systems, since that comparison is
natural in the composable ring maps and so respects transitions; the counit of $L_r\dashv U_r$
then identifies $\mathcal R_L(K\otimes^L\widehat R_L)$ with $L_r$ of it, the Step 2 recovery of
the full tower. Conjugating the system counit identity by these isomorphisms gives
$\epsilon_{t,T_YL}F_t(b_L)q_{G_sL}=T_Y(\epsilon_{s,L})$; functors and conjugation preserve
composition. Each comparison is invertible because its system comparison and every conjugating map
are invertible. For the left realization apply $c_V$ to the tensor-by-coefficients and proper/open
expressions: its generator-map clause identifies the tensor/pullback map and proper counit with
the corresponding integral maps. The open map is the unique open-adjunction transpose of the
scalar extension of the open unit. Consequently the realized $q$ is exactly the ambient proper
scalar mate followed by that open tensor map, with the prescribed $\chi$ and proper/open
realization. This proves equality of these normalized integral maps through the coherent system
construction, rather than through faithfulness of finite evaluations. Uses: lem-sf-exceptional-
integral-reconstruction, lem-weil-finite-free-completed-scalar-comparison, lem-sf-integral-
compactification-system-realization, lem-sf-open-tensor-normalization, lem-sfb-successive-derived-
quotient-normalization, lem-pur-system-level-left-extension.

6. Give scalar extension its canonical cochain shift. Proper mates are made from shift-compatible
derived units/counits and tensor/pullback maps; the open tensor map is degreewise the same
balanced tensor map. The realization shift theorem applies to these same bounded normalized
expressions and their generator maps, and to Steps 1 and 5. For $\chi$ the completed-scalar chain-
shift theorem gives the product shift on the first cone coordinate and $(-1)^r$ times it on the
second coordinate for shift $r$; the zero second component of the quotient comparison stays zero.
Thus $\theta=\chi^{-1}$ also preserves these canonical Roos-cone shifts. Right-adjoint shift
structures are the unique ones compatible with unit and counit. Taking the transpose of a shifted
left comparison therefore gives the shifted $b$, by its defining counit equation and injectivity
of adjunction. All generator $q,b$ are shift-compatible for these specified shifts. Uses: lem-pur-
integral-realization-shift-coherence, lem-weil-completed-scalar-chain-shift, lem-weil-pbc-
adjunction-shift-compatibility-unique, lem-weil-pbc-commshift-nattrans-comp-whisker.

7. For each allowed actual coefficient-sheaf map choose the scalar functor according to its
target: literal ambient restriction at a finite target, the published completed extension at an
integral target. Finite generators use the finite scalar lemma; integral generators use Steps 1–6.
Balanced derived associativity gives $(S_bS_a)\cong S_{ba}$, represented by $(x\otimes s)\otimes
t\mapsto x\otimes b(s)t$, and scalar units give $S_{\mathrm{id}}\cong\mathrm{id}$, represented by
$x\otimes r\mapsto rx$. Conjugate these ambient maps through the scalar realizations $\theta$ and
lift through the full inclusions. Fullness supplies the maps, faithfulness gives their naturality
and the identities for their inverses. This constructs the scalar identity and composition
isomorphisms with exactly the asserted ambient realizations, including mixed finite-
quotient/completed-extension composites. Uses: lem-sf-exceptional-finite-scalar-mates, lem-sfb-
successive-derived-quotient-normalization, lem-pur-coefficient-scalar-units.

8. For composable allowed maps $a:s\to t$, $c:t\to u$, write $V=T_c$, $T=T_a$ and suppress the
balanced scalar associators. Define $q_{ca}=(q_cT_X)\circ V_Y(q_a)$ and $b_{ca}=(b_cT_Y)\circ
V_X(b_a)$. For the proper factor, the coefficient-projection cocycle identifies this pasted $q$
with the canonical proper scalar mate for the composite coefficient map; its identity clause gives
the proper unitor. For the open factor, restrict both composites to the open. The open-unit
normalization identifies both with the same balanced tensor associator; injectivity of the open-
adjunction bijection gives equality before restriction. Hence the pasted proper/open $q$ is the
specified one for the actual composite, including identities. The cocycle and open normalization
are statements on ringed diagram sites, so this conclusion holds for system maps before total
limit and is carried to the integral realization by its generator-map clause. Uses: lem-pur-
ringed-coefficient-projection-cocycle, lem-sf-open-tensor-normalization, lem-sf-integral-
compactification-system-realization.

9. Check the right composite explicitly. With the notation of Step 8 and composition read right to
left, its counit composite is $$\epsilon_u F_u(b_cT_Y)F_uV_X(b_a)q_{c,T_XG_s}V_Y(q_{a,G_s}).$$
Naturality of $q_c$ moves $F_uV_X(b_a)$ past $q_c$, replacing their product by
$q_{c,G_tT_Y}V_YF_t(b_a)$. The equation for $c$ changes the first three factors into
$V_Y(\epsilon_tF_t(b_a))$; the equation for $a$ then gives $V_YT_Y(\epsilon_s)$. Reinsert the
scalar associators of Step 7 to obtain exactly the required composite counit equation. This also
proves that $b_{ca}$ is the counit-normalized transpose of $q_{ca}^{-1}$, by the adjunction
bijection. For identities the same equation is the triangle identity under the multiplication
unitor. Uses: elementary naturality and triangle identities.

10. Induct on an allowed witness, using the generator comparisons, the identity unitors and the
composite construction of Steps 7–9. Every resulting $q,b$ is invertible as a composite of
isomorphisms. The balanced associators preserve shifts, and composition, inversion and whiskering
preserve shift-compatible transformations, so these properties hold for every witness. The
proper/open cocycle fixes the realized left map for its actual coefficient map; Step 9 fixes the
right map by the counit equation. At each stage use actual system transformations and only then
their total-limit images. This proves every asserted normalization and preserves the canonical
termwise and cone shifts. Uses: lem-pur-coefficient-associator-shifts, lem-weil-pbc-commshift-
nattrans-comp-whisker. -/
theorem exceptionalIntegralScalarMates
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (transport : Transported l Ω D hl c operation left) :
    ∃ d : Mates l Ω c operation left,
      ∃ red : ∀ (E : FieldStage.{u} l) (n : ℕ),
        ReductionMates l Ω D hl c operation left transport d E n,
      (∀ (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier),
        Nonempty (SystemMates l Ω D hl c operation left transport d red E L i)) ∧
      (∀ (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
        (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e) (n : ℕ),
        ∃ z : RamifiedMap l E L i e he, z.n = n) := by
  obtain ⟨d, red, sys⟩ :=
    exceptionalIntegralScalarMates_core l Ω D hl c operation left transport
  refine ⟨d, red, sys, ?_⟩
  intro E L i e he n
  have witness (p : ℕ+) (hp : (p : ℕ) = (e : ℕ) * (n + 1))
      (a : PurCompactSupport.Change
        ((RingStage.finite E ⟨n + 1, Nat.succ_pos n⟩).coefficients l)
        ((RingStage.finite L p).coefficients l))
      (ha : Allowed l (s := .finite E ⟨n + 1, Nat.succ_pos n⟩) (t := .finite L p) a)
      (hactual : ∀ T : Scheme.{u}, HEq (a.map T)
        ((PurCompactSupport.finiteChange l E.carrier L.carrier i e he e.pos
          (n + 1) (Nat.succ_pos n)).map T)) :
      ∃ z : RamifiedMap l E L i e he, z.n = n := by
    rcases p with ⟨p, hp0⟩
    cases p with
    | zero => exact False.elim (Nat.not_lt_zero _ hp0)
    | succ m =>
      exact ⟨{
        n := n
        m := m
        exponent := hp
        change := a
        allowed := ha
        actual := hactual }, rfl⟩
  exact witness ⟨(e : ℕ) * (n + 1), Nat.mul_pos e.pos (Nat.succ_pos n)⟩ rfl
    (PurCompactSupport.finiteChange l E.carrier L.carrier i e he e.pos
      (n + 1) (Nat.succ_pos n))
    (Allowed.ramified (l := l) E L i e he ⟨n + 1, Nat.succ_pos n⟩)
    (fun _ ↦ HEq.rfl)

end WeilConjectures.ExceptionalIntegralScalar
