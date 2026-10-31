/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalRingTransportCoreData
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
abbrev normalizedRealizeG (E : FieldStage.{u} l) :
    (operation (.integral E)).G ≅
      PurReconstruction.realized (d.reconstruction E false).equivalence
        (d.reconstruction E true).equivalence (d.G E) :=
  d.realizeG E

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

/-- The datum is already normalized: its right comparison is constructed canonically.
Source: Zheng, Construction 5.25; the concrete right-adjoint uniqueness construction.
(blueprint: lem-sf-exceptional-system-adjunction-normalized-comparison) -/
def TransportCoreData.normalizeRealizeG : TransportCoreData l Ω D hl c operation left :=
  d

/-- The already normalized datum satisfies the complete system adjunction equation.
Proof: the normalization is the identity and `realizeG` is by definition
the canonical comparison of the preceding theorem.
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
    (e : (operation (.integral E)).G ≅
      PurReconstruction.realized (d.reconstruction E false).equivalence
        (d.reconstruction E true).equivalence (d.G E))
    (h : e ≠ normalizedRealizeG l Ω D hl c operation left d E) :
    (operation (.integral E)).adjunction ≠
      ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
        (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
        (d.realizeF E).symm).ofNatIsoRight e.symm := by
  intro he
  apply h
  exact congrArg Iso.symm ((Adjunction.ofNatIsoRight_eq_iff
    ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
      (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
      (d.realizeF E).symm) (operation (.integral E)).adjunction e.symm).1 he.symm)

/-- A nonidentity automorphism rules out adjunction laws for every comparison family.
Proof: twist the canonical comparison by the given automorphism. The claimed law
would identify the twist with the canonical comparison. Cancel it at the stage
where the automorphism is nonidentity. The canonical `d.realizeG` is unchanged.
Source: right-adjoint uniqueness in Zheng, Construction 5.25.
(blueprint: lem-sf-exceptional-system-adjunction-comparison-obstruction) -/
theorem not_forall_adjunction_law_of_realizeG_twist
    (α : ∀ E : FieldStage.{u} l,
      (operation (.integral E)).G ≅ (operation (.integral E)).G)
    (E : FieldStage.{u} l) (hα : α E ≠ Iso.refl _) :
    ¬ ∀ e : ∀ E : FieldStage.{u} l,
        (operation (.integral E)).G ≅
          PurReconstruction.realized (d.reconstruction E false).equivalence
            (d.reconstruction E true).equivalence (d.G E),
      ∀ E : FieldStage.{u} l,
        (operation (.integral E)).adjunction =
          ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
            (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
            (d.realizeF E).symm).ofNatIsoRight (e E).symm := by
  intro h
  have he := (Adjunction.ofNatIsoRight_eq_iff
    ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
      (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
      (d.realizeF E).symm) (operation (.integral E)).adjunction
    (α E ≪≫ normalizedRealizeG l Ω D hl c operation left d E).symm).1
    (h (fun E ↦ α E ≪≫ normalizedRealizeG l Ω D hl c operation left d E) E).symm
  have he' := congrArg Iso.symm he
  change α E ≪≫ normalizedRealizeG l Ω D hl c operation left d E =
    normalizedRealizeG l Ω D hl c operation left d E at he'
  apply hα
  have hh := congrArg
    (fun e ↦ e ≪≫ (normalizedRealizeG l Ω D hl c operation left d E).symm) he'
  simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hh

/-- The sign twist obstructs laws for every comparison when minus identity is nonidentity.
Proof: use the preceding result with the negative identity natural isomorphism
at every stage. Its component at K differs from the identity by hypothesis.
Source: Zheng, Construction 5.25; negation in the integral preadditive categories.
(blueprint: lem-sf-exceptional-system-adjunction-comparison-obstruction) -/
theorem not_forall_adjunction_law_of_neg_id_ne (E : FieldStage.{u} l)
    (K : C.{u} l Ω Y (.integral E))
    (hne : -(𝟙 ((operation (.integral E)).G.obj K)) ≠
      𝟙 ((operation (.integral E)).G.obj K)) :
    ¬ ∀ e : ∀ E : FieldStage.{u} l,
        (operation (.integral E)).G ≅
          PurReconstruction.realized (d.reconstruction E false).equivalence
            (d.reconstruction E true).equivalence (d.G E),
      ∀ E : FieldStage.{u} l,
        (operation (.integral E)).adjunction =
          ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
            (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
            (d.realizeF E).symm).ofNatIsoRight (e E).symm := by
  apply not_forall_adjunction_law_of_realizeG_twist l Ω D hl c operation left d
    (fun E ↦ -Iso.refl (operation (.integral E)).G) E
  intro he
  apply hne
  exact congrArg (fun e ↦ e.hom.app K) he

end RightComparison

/--
The strict-system adjunction comparison, transported through the two chosen
reconstruction equivalences, is the adjunction component of the system laws.
The right comparison is constructed from the two adjunctions by
`Adjunction.rightAdjointUniq`. Transporting along its inverse recovers the
specified integral adjunction by `Adjunction.ofNatIsoRight_eq_iff`. This theorem
isolates that single component so the reduction equations can be handled independently.
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
  exact ⟨normalizedRealizeG_adjunction l Ω D hl c operation left d⟩

end WeilConjectures.ExceptionalIntegralScalar
