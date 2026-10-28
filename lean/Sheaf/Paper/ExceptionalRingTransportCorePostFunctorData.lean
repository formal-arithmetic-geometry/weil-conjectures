/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ExceptionalRingTransportCoreReconstruction

/-! # Functor and comparison fields for exceptional integral transport

This module isolates the transported functors and comparison maps from the
reconstruction and integral realization choices.  It is the strictly smaller
assembly package used by `TransportCorePostData`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

/-- The transported functors and comparison fields, with the reconstruction and
integral realization choices supplied as parameters.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24 and 5.26.
(blueprint: new-lem-sf-exceptional-ring-transport-post-functor-data)
-/
structure TransportCorePostFunctorData
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l,
      LeftRealization.{u} l Ω c s (operation s))
    (reconstruction : ∀ E : FieldStage.{u} l, ∀ side : Bool,
      Reconstruction l E (endpoint X Y side))
    (operations : ∀ E : FieldStage.{u} l,
      IntegralSystemRealization.Operations l E.carrier)
    (realizations : ∀ E : FieldStage.{u} l,
      IntegralSystemRealization.Realizations l E.carrier D (operations E)) where
  F (E : FieldStage.{u} l) : (sequenceProperty l E X).FullSubcategory ⥤
    (sequenceProperty l E Y).FullSubcategory
  G (E : FieldStage.{u} l) : (sequenceProperty l E Y).FullSubcategory ⥤
    (sequenceProperty l E X).FullSubcategory
  adjunction (E : FieldStage.{u} l) : F E ⊣ G E
  realizeF (E : FieldStage.{u} l) : (operation (.integral E)).F ≅
    PurReconstruction.realized (reconstruction E true).equivalence
      (reconstruction E false).equivalence (F E)
  realizeG (E : FieldStage.{u} l) : (operation (.integral E)).G ≅
    PurReconstruction.realized (reconstruction E false).equivalence
      (reconstruction E true).equivalence (G E)
  reductionF (E : FieldStage.{u} l) :
    (operation (.integral E)).F ⋙ (reconstruction E false).equivalence.functor ≅
      (reconstruction E true).equivalence.functor ⋙ F E
  reductionG (E : FieldStage.{u} l) :
    (operation (.integral E)).G ⋙ (reconstruction E true).equivalence.functor ≅
      (reconstruction E false).equivalence.functor ⋙ G E
  evaluationF (E : FieldStage.{u} l) (n : ℕ) :
    F E ⋙ (reconstruction E false).evaluation n ≅
      (reconstruction E true).evaluation n ⋙
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F
  evaluationG (E : FieldStage.{u} l) (n : ℕ) :
    G E ⋙ (reconstruction E true).evaluation n ≅
      (reconstruction E false).evaluation n ⋙
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G

/-- The strict-system transport and normalized reconstruction calculus produce
all transported functors, adjunctions, evaluations, and the integral-left
comparison once the reconstruction and realization choices are fixed.
The proof is the construction in Zheng, Constructions 4.1 and 5.25,
Lemma 5.22 and Propositions 5.24 and 5.26: transport the strict adjunction,
conjugate it through the two reconstruction equivalences, identify finite
evaluations, and apply the coherent integral compactification realization.
(blueprint: new-lem-sf-exceptional-ring-transport-post-functor-data)
-/
theorem exists_exceptional_transport_post_functor_data
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l,
      LeftRealization.{u} l Ω c s (operation s))
    (reconstruction : ∀ E : FieldStage.{u} l, ∀ side : Bool,
      Reconstruction l E (endpoint X Y side))
    (operations : ∀ E : FieldStage.{u} l,
      IntegralSystemRealization.Operations l E.carrier)
    (realizations : ∀ E : FieldStage.{u} l,
      IntegralSystemRealization.Realizations l E.carrier D (operations E)) :
    Nonempty (TransportCorePostFunctorData l Ω D hl c operation left reconstruction
      operations realizations) := by
  sorry

/-- The coherent integral realization supplies the remaining integral-left
comparison for each field stage.  This is the one-field remainder of the
transport package isolated above.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Proposition 5.26.
(blueprint: new-lem-sf-exceptional-ring-transport-integral-left)
-/
theorem exists_exceptional_transport_integral_left
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l,
      LeftRealization.{u} l Ω c s (operation s))
    (reconstruction : ∀ E : FieldStage.{u} l, ∀ side : Bool,
      Reconstruction l E (endpoint X Y side))
    (operations : ∀ E : FieldStage.{u} l,
      IntegralSystemRealization.Operations l E.carrier)
    (realizations : ∀ E : FieldStage.{u} l,
      IntegralSystemRealization.Realizations l E.carrier D (operations E)) :
    Nonempty (∀ E : FieldStage.{u} l,
      (operation (.integral E)).F ⋙
          PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
        PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
          sfCompactSupportFiniteIntegralFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier) := by
  sorry


end WeilConjectures.ExceptionalIntegralScalar
