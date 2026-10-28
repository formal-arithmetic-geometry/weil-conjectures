/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ExceptionalRingTransportCoreData
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-! The adjunction comparison part of the exceptional integral transport system laws.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core-system-adjunction-law).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

section RightComparison

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
  (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
  (d : TransportCoreData l Ω D hl c operation left)

/-- The right realization dictated by the specified adjunction and left realization.
It is the inverse of Mathlib's uniqueness isomorphism between right adjoints of
`(operation (.integral E)).F`. This is a concrete construction from the two
adjunctions, without choosing an arbitrary witness of an existence theorem.
Source: Zheng, Construction 5.25; expanded by uniqueness of right adjoints.
(blueprint: lem-sf-exceptional-system-adjunction-normalized-comparison) -/
def normalizedRealizeG (E : FieldStage.{u} l) :
    (operation (.integral E)).G ≅
      PurReconstruction.realized (d.reconstruction E false).equivalence
        (d.reconstruction E true).equivalence (d.G E) :=
  (Adjunction.rightAdjointUniq
    ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
      (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
        (d.realizeF E).symm)
    (operation (.integral E)).adjunction).symm

/-- The constructed right realization makes the adjunction comparison exact.
Proof: transporting by the uniqueness isomorphism recovers the specified unit,
and equality of units implies equality of adjunctions.
Source: Zheng, Construction 5.25, with Mathlib's right-adjoint uniqueness formula.
(blueprint: lem-sf-exceptional-system-adjunction-normalized-comparison) -/
theorem normalizedRealizeG_adjunction (E : FieldStage.{u} l) :
    (operation (.integral E)).adjunction =
      ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
        (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
        (d.realizeF E).symm).ofNatIsoRight
          (normalizedRealizeG l Ω D hl c operation left d E).symm := by
  exact ((Adjunction.ofNatIsoRight_eq_iff _ _ _).2 rfl).symm

/-- The original adjunction equation is equivalent to choosing the canonical comparison.
Proof: transport along right comparisons is injective, so compare with the already
proved canonical transport; take inverse isomorphisms to recover `realizeG`.
Source: Zheng, Construction 5.25; uniqueness of adjunction-compatible comparisons.
(blueprint: lem-sf-exceptional-system-adjunction-normalized-comparison) -/
theorem adjunction_law_iff_realizeG_eq (E : FieldStage.{u} l) :
    ((operation (.integral E)).adjunction =
      ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
        (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
        (d.realizeF E).symm).ofNatIsoRight (d.realizeG E).symm) ↔
    d.realizeG E = normalizedRealizeG l Ω D hl c operation left d E := by
  constructor
  · intro h
    exact congrArg Iso.symm ((Adjunction.ofNatIsoRight_eq_iff
      ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
        (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
        (d.realizeF E).symm) (operation (.integral E)).adjunction
      (d.realizeG E).symm).1 h.symm)
  · intro h
    rw [h]
    exact normalizedRealizeG_adjunction l Ω D hl c operation left d E

/-- Replace the freely chosen right comparison by the adjunction-compatible one.
Source: Zheng, Construction 5.25; the concrete right-adjoint uniqueness construction.
(blueprint: lem-sf-exceptional-system-adjunction-normalized-comparison) -/
def TransportCoreData.normalizeRealizeG : TransportCoreData l Ω D hl c operation left :=
  { d with realizeG := normalizedRealizeG l Ω D hl c operation left d }

/-- The explicit structure update satisfies the complete system adjunction equation.
Proof: every field occurring in the transported adjunction is unchanged, and the
new `realizeG` is exactly the canonical comparison of the preceding theorem.
Source: Zheng, Construction 5.25; normalization of the right realization.
(blueprint: lem-sf-exceptional-system-adjunction-normalized-comparison) -/
theorem TransportCoreData.normalizeRealizeG_adjunction (E : FieldStage.{u} l) :
    let d' := d.normalizeRealizeG l Ω D hl c operation left
    (operation (.integral E)).adjunction =
      ((PurReconstruction.realizedAdjunction (d'.reconstruction E true).equivalence
        (d'.reconstruction E false).equivalence (d'.adjunction E)).ofNatIsoLeft
        (d'.realizeF E).symm).ofNatIsoRight (d'.realizeG E).symm := by
  exact normalizedRealizeG_adjunction l Ω D hl c operation left d E

/-- There is exactly one family of right comparisons preserving the specified adjunctions.
This is the constructive replacement for an equation about an arbitrary family.
Proof: use `normalizedRealizeG` at every field stage. If another family transports
the same adjunction, `ofNatIsoRight_eq_iff` identifies its inverse component with
the same uniqueness isomorphism. Function extensionality identifies the families.
Source: Zheng, Construction 5.25; uniqueness of right adjoints with their adjunctions.
(blueprint: lem-sf-exceptional-system-adjunction-normalized-comparison) -/
theorem existsUnique_system_adjunction_right_comparison :
    ∃! e : ∀ E : FieldStage.{u} l,
        (operation (.integral E)).G ≅
          PurReconstruction.realized (d.reconstruction E false).equivalence
            (d.reconstruction E true).equivalence (d.G E),
      ∀ E : FieldStage.{u} l,
        (operation (.integral E)).adjunction =
          ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
            (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
            (d.realizeF E).symm).ofNatIsoRight (e E).symm := by
  refine ⟨normalizedRealizeG l Ω D hl c operation left d,
    normalizedRealizeG_adjunction l Ω D hl c operation left d, ?_⟩
  intro e he
  funext E
  exact congrArg Iso.symm ((Adjunction.ofNatIsoRight_eq_iff
    ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
      (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
      (d.realizeF E).symm) (operation (.integral E)).adjunction (e E).symm).1 (he E).symm)

/-- Any noncanonical right comparison obstructs the displayed adjunction equation.
Proof: the equation characterizes the canonical comparison by the preceding iff.
Source: the right-adjoint uniqueness calculation of Zheng, Construction 5.25.
(blueprint: lem-sf-exceptional-system-adjunction-comparison-obstruction) -/
theorem not_adjunction_law_of_realizeG_ne (E : FieldStage.{u} l)
    (h : d.realizeG E ≠ normalizedRealizeG l Ω D hl c operation left d E) :
    (operation (.integral E)).adjunction ≠
      ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
        (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
        (d.realizeF E).symm).ofNatIsoRight (d.realizeG E).symm := by
  exact fun he ↦ h ((adjunction_law_iff_realizeG_eq l Ω D hl c operation left d E).1 he)

include d

/-- A nonidentity automorphism of the given right functor rules out laws for every datum.
Proof: replace the right comparison at every stage by the canonical comparison
precomposed with the given automorphism. The claimed universal law would identify
this with the canonical comparison. Cancel that isomorphism at the stage where the
automorphism is nonidentity. No other field of the datum is changed.
Source: right-adjoint uniqueness, applied to the comparison in Zheng, Construction 5.25.
(blueprint: lem-sf-exceptional-system-adjunction-comparison-obstruction) -/
theorem not_forall_adjunction_law_of_realizeG_twist
    (α : ∀ E : FieldStage.{u} l,
      (operation (.integral E)).G ≅ (operation (.integral E)).G)
    (E : FieldStage.{u} l) (hα : α E ≠ Iso.refl _) :
    ¬ ∀ d' : TransportCoreData l Ω D hl c operation left,
      Nonempty (∀ E : FieldStage.{u} l,
        (operation (.integral E)).adjunction =
          ((PurReconstruction.realizedAdjunction (d'.reconstruction E true).equivalence
            (d'.reconstruction E false).equivalence (d'.adjunction E)).ofNatIsoLeft
            (d'.realizeF E).symm).ofNatIsoRight (d'.realizeG E).symm) := by
  intro h
  let d' : TransportCoreData l Ω D hl c operation left :=
    { d with realizeG := fun E ↦ α E ≪≫ normalizedRealizeG l Ω D hl c operation left d E }
  obtain ⟨hd'⟩ := h d'
  have he := (adjunction_law_iff_realizeG_eq l Ω D hl c operation left d' E).1 (hd' E)
  change α E ≪≫ normalizedRealizeG l Ω D hl c operation left d E =
    normalizedRealizeG l Ω D hl c operation left d E at he
  apply hα
  have hh := congrArg
    (fun e ↦ e ≪≫ (normalizedRealizeG l Ω D hl c operation left d E).symm) he
  simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hh

/-- The sign twist gives an obstruction whenever minus identity differs from identity.
Proof: use the preceding obstruction with the negative identity natural isomorphism
at every stage. If that isomorphism were the identity at the specified stage, its
component at K would contradict the supplied hypothesis.
Source: the comparison uniqueness calculation of Zheng, Construction 5.25, with
negation in the actual preadditive integral categories.
(blueprint: lem-sf-exceptional-system-adjunction-comparison-obstruction) -/
theorem not_forall_adjunction_law_of_neg_id_ne (E : FieldStage.{u} l)
    (K : C.{u} l Ω Y (.integral E))
    (hne : -(𝟙 ((operation (.integral E)).G.obj K)) ≠
      𝟙 ((operation (.integral E)).G.obj K)) :
    ¬ ∀ d' : TransportCoreData l Ω D hl c operation left,
      Nonempty (∀ E : FieldStage.{u} l,
        (operation (.integral E)).adjunction =
          ((PurReconstruction.realizedAdjunction (d'.reconstruction E true).equivalence
            (d'.reconstruction E false).equivalence (d'.adjunction E)).ofNatIsoLeft
            (d'.realizeF E).symm).ofNatIsoRight (d'.realizeG E).symm) := by
  apply not_forall_adjunction_law_of_realizeG_twist l Ω D hl c operation left d
    (fun E ↦ -Iso.refl (operation (.integral E)).G) E
  intro he
  apply hne
  exact congrArg (fun e ↦ e.hom.app K) he

end RightComparison

/- STATEMENT-DISPUTED: TransportCoreData allows `realizeG` independently of its
adjunction and `realizeF`. The claimed equality holds exactly when `realizeG`
is the uniqueness comparison, as proved in `adjunction_law_iff_realizeG_eq`.
The explicit update `TransportCoreData.normalizeRealizeG` satisfies it, but
nothing in the hypotheses requires the supplied datum to have that field. -/

/--
The strict-system adjunction comparison, transported through the two chosen
reconstruction equivalences, is the adjunction component of the system laws.
The displayed equality is obtained by conjugating the strict-system adjunction
through `realizeF` and `realizeG` and retaining the resulting natural
isomorphism equality.  This theorem isolates that single component so the
remaining reduction equations can be handled independently.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core-system-adjunction-law).
-/
theorem exists_exceptional_transport_core_system_adjunction_law
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l,
      LeftRealization.{u} l Ω c s (operation s))
    (d : TransportCoreData l Ω D hl c operation left) :
    Nonempty (∀ E : FieldStage.{u} l,
      (operation (.integral E)).adjunction =
        ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
          (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
          (d.realizeF E).symm).ofNatIsoRight (d.realizeG E).symm) := by
  sorry

end WeilConjectures.ExceptionalIntegralScalar
