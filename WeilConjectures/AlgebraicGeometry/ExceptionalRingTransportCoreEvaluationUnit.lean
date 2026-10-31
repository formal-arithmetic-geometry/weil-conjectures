/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ExceptionalRingTransportCoreData
public import Mathlib.CategoryTheory.Adjunction.Mates
/-! The evaluated unit equation for exceptional integral transport.
Source: Zheng, Lemma 5.22 and Proposition 5.24.
(blueprint: new-lem-sf-exceptional-ring-transport-core-evaluation-unit) -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
private theorem right_mate_of_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') {U : A ⥤ C} {V : B ⥤ D}
    (χ : R ⋙ U ⟶ V ⋙ R') (ρ : L ⋙ V ≅ U ⋙ L')
    (h : ∀ K, U.map (a.unit.app K) ≫ χ.app (L.obj K) ≫
      R'.map (ρ.hom.app K) = b.unit.app (U.obj K)) :
    χ = (mateEquiv a b (TwoSquare.mk _ _ _ _ ρ.inv)).natTrans := by
  ext N
  simp only [mateEquiv, Equiv.coe_fn_mk, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.id_obj, Functor.comp_obj, Functor.comp_map, Category.id_comp, Category.comp_id]
  rw [← h (R.obj N)]
  simp only [TwoSquare.natTrans, Category.assoc, ← R'.map_comp_assoc,
    Functor.id_obj, Functor.comp_obj]
  simp only [Iso.hom_inv_id_app]
  simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := χ.naturality (a.counit.app N)
  dsimp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hn
  rw [← hn, ← U.map_comp_assoc, a.right_triangle_components,
    U.map_id, Category.id_comp]

private theorem right_mate_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') {U : A ⥤ C} {V : B ⥤ D}
    (ρ : L ⋙ V ≅ U ⋙ L') (K : A) :
    U.map (a.unit.app K) ≫
      (mateEquiv a b (TwoSquare.mk _ _ _ _ ρ.inv)).natTrans.app (L.obj K) ≫
      R'.map (ρ.hom.app K) = b.unit.app (U.obj K) := by
  rw [← Category.assoc, unit_mateEquiv a b (TwoSquare.mk _ _ _ _ ρ.inv) K,
    Category.assoc, ← R'.map_comp]
  simp only [TwoSquare.mk, Functor.id_obj, Functor.comp_obj, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id,
    Category.comp_id]

section EvaluationMate

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

/-- The canonical right evaluation map, constructed as the mate of inverse left evaluation.
This is a natural transformation; invertibility of a general mate requires a separate proof.
Source: Zheng, Lemma 5.22, whose comparison is induced by adjunction; Mathlib `mateEquiv`.
(blueprint: lem-sf-exceptional-evaluation-right-mate) -/
def evaluationRightMate (E : FieldStage.{u} l) (n : ℕ) :
    d.G E ⋙ (d.reconstruction E true).evaluation n ⟶
      (d.reconstruction E false).evaluation n ⋙
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G :=
  (mateEquiv (d.adjunction E)
    (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction
    (TwoSquare.mk _ _ _ _ (d.evaluationF E n).inv)).natTrans

/-- The canonical mate satisfies the evaluated unit equation.
Proof: apply `unit_mateEquiv` to inverse left evaluation and cancel its inverse with
left evaluation after applying the finite right functor.
Source: Zheng, Lemma 5.22; the unit identity for adjunction mates.
(blueprint: lem-sf-exceptional-evaluation-right-mate) -/
theorem evaluationRightMate_unit (E : FieldStage.{u} l) (n : ℕ)
    (K : (sequenceProperty l E X).FullSubcategory) :
    ((d.reconstruction E true).evaluation n).map ((d.adjunction E).unit.app K) ≫
      (evaluationRightMate l Ω D hl c operation left d E n).app ((d.F E).obj K) ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G.map
        ((d.evaluationF E n).hom.app K) =
    (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.unit.app
      (((d.reconstruction E true).evaluation n).obj K) := by
  exact right_mate_unit (d.adjunction E)
    (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction
    (d.evaluationF E n) K

private theorem evaluation_unit_of_evaluationG_eq_mate (E : FieldStage.{u} l) (n : ℕ)
    (h : (d.evaluationG E n).hom = evaluationRightMate l Ω D hl c operation left d E n)
    (K : (sequenceProperty l E X).FullSubcategory) :
    ((d.reconstruction E true).evaluation n).map ((d.adjunction E).unit.app K) ≫
      (d.evaluationG E n).hom.app ((d.F E).obj K) ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G.map
        ((d.evaluationF E n).hom.app K) =
    (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.unit.app
      (((d.reconstruction E true).evaluation n).obj K) := by
  rw [h]
  exact evaluationRightMate_unit l Ω D hl c operation left d E n K

/-- The evaluated unit equation holds exactly when the given right evaluation is its mate.
Proof: the forward implication expands the mate, substitutes the unit equation at G(N),
uses naturality at the counit, and cancels the right triangle. The reverse implication
is the canonical mate's unit identity.
Source: Zheng, Lemma 5.22; Mathlib's mate correspondence and triangle identities.
(blueprint: lem-sf-exceptional-evaluation-right-mate) -/
theorem evaluation_unit_iff_evaluationG_eq_mate (E : FieldStage.{u} l) (n : ℕ) :
    (∀ K : (sequenceProperty l E X).FullSubcategory,
      ((d.reconstruction E true).evaluation n).map ((d.adjunction E).unit.app K) ≫
        (d.evaluationG E n).hom.app ((d.F E).obj K) ≫
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G.map
          ((d.evaluationF E n).hom.app K) =
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.unit.app
        (((d.reconstruction E true).evaluation n).obj K)) ↔
    (d.evaluationG E n).hom = evaluationRightMate l Ω D hl c operation left d E n := by
  constructor
  · exact right_mate_of_unit (d.adjunction E)
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction
      (d.evaluationG E n).hom (d.evaluationF E n)
  · intro h K
    exact evaluation_unit_of_evaluationG_eq_mate l Ω D hl c operation left d E n h K

/-- A noncanonical evaluation comparison cannot satisfy the unit equation.
Proof: the unit equation characterizes the mate by the preceding equivalence.
Source: Zheng, Lemma 5.22; uniqueness in the mates correspondence.
(blueprint: lem-sf-exceptional-evaluation-unit-obstruction) -/
theorem not_evaluation_unit_of_evaluationG_ne_mate (E : FieldStage.{u} l) (n : ℕ)
    (h : (d.evaluationG E n).hom ≠
      evaluationRightMate l Ω D hl c operation left d E n) :
    ¬ ∀ K : (sequenceProperty l E X).FullSubcategory,
      ((d.reconstruction E true).evaluation n).map ((d.adjunction E).unit.app K) ≫
        (d.evaluationG E n).hom.app ((d.F E).obj K) ≫
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G.map
          ((d.evaluationF E n).hom.app K) =
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.unit.app
        (((d.reconstruction E true).evaluation n).obj K) := by
  exact fun he ↦ h ((evaluation_unit_iff_evaluationG_eq_mate
    l Ω D hl c operation left d E n).1 he)

/-- An invertible canonical mate determines a unique right evaluation isomorphism
preserving units. Proof: package the mate as `asIso`, use its unit identity, and apply
`right_mate_of_unit` to identify the hom of any other such isomorphism.
Source: Zheng, Lemma 5.22, and the adjunction mates correspondence.
(blueprint: lem-sf-exceptional-evaluation-right-mate) -/
theorem existsUnique_evaluation_right_comparison (E : FieldStage.{u} l) (n : ℕ)
    (hi : IsIso (evaluationRightMate l Ω D hl c operation left d E n)) :
    ∃! e : d.G E ⋙ (d.reconstruction E true).evaluation n ≅
        (d.reconstruction E false).evaluation n ⋙
          (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G,
      ∀ K : (sequenceProperty l E X).FullSubcategory,
        ((d.reconstruction E true).evaluation n).map ((d.adjunction E).unit.app K) ≫
          e.hom.app ((d.F E).obj K) ≫
          (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G.map
            ((d.evaluationF E n).hom.app K) =
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.unit.app
          (((d.reconstruction E true).evaluation n).obj K) := by
  let := hi
  refine ⟨asIso (evaluationRightMate l Ω D hl c operation left d E n),
    evaluationRightMate_unit l Ω D hl c operation left d E n, ?_⟩
  intro e he
  apply Iso.ext
  exact right_mate_of_unit (d.adjunction E)
    (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction e.hom (d.evaluationF E n) he

/-- Normalize the right evaluation comparisons when their explicitly constructed mates
are invertible. All other fields are retained; `asIso` uses the specified mate as its hom.
Source: Zheng, Lemma 5.22 and Construction 5.25; the comparison induced by adjunction.
(blueprint: lem-sf-exceptional-evaluation-right-mate) -/
def TransportCoreData.normalizeEvaluationG
    (hi : ∀ (E : FieldStage.{u} l) (n : ℕ),
      IsIso (evaluationRightMate l Ω D hl c operation left d E n)) :
    TransportCoreData l Ω D hl c operation left :=
  { d with evaluationG := fun E n ↦
      { hom := (@asIso _ _ _ _
          (evaluationRightMate l Ω D hl c operation left d E n) (hi E n)).hom
        unit := evaluationRightMate_unit l Ω D hl c operation left d E n
        counit := (Adjunction.compatibleRightComparison (d.adjunction E)
          (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction
          (d.evaluationF E n)).counit } }

/-- The concrete normalization satisfies the evaluated unit equation at every stage.
Proof: its right evaluation hom is the canonical mate, while its adjunction and left
evaluation are unchanged. Apply the canonical mate's unit identity.
Source: Zheng, Lemma 5.22 and Construction 5.25; the unit identity of mates.
(blueprint: lem-sf-exceptional-evaluation-right-mate) -/
theorem TransportCoreData.normalizeEvaluationG_unit
    (hi : ∀ (E : FieldStage.{u} l) (n : ℕ),
      IsIso (evaluationRightMate l Ω D hl c operation left d E n))
    (E : FieldStage.{u} l) (n : ℕ) (K : (sequenceProperty l E X).FullSubcategory) :
    let d' := d.normalizeEvaluationG l Ω D hl c operation left hi
    ((d'.reconstruction E true).evaluation n).map ((d'.adjunction E).unit.app K) ≫
      (d'.evaluationG E n).hom.app ((d'.F E).obj K) ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G.map
        ((d'.evaluationF E n).hom.app K) =
    (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.unit.app
      (((d'.reconstruction E true).evaluation n).obj K) := by
  exact evaluationRightMate_unit l Ω D hl c operation left d E n K

/-- A finite unit distinct from its negative obstructs unit laws for every independent
right comparison.
Proof: test the given right evaluation map and its negative. The two unit laws
would say that the same finite unit equals its own negative, by bilinearity of composition.
Source: Zheng, Lemma 5.22; the sign test for an independently specified comparison.
(blueprint: lem-sf-exceptional-evaluation-unit-obstruction) -/
theorem not_forall_evaluation_unit_of_neg_unit_ne (E : FieldStage.{u} l) (n : ℕ)
    (K : (sequenceProperty l E X).FullSubcategory)
    (hne : -((operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.unit.app
        (((d.reconstruction E true).evaluation n).obj K)) ≠
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.unit.app
        (((d.reconstruction E true).evaluation n).obj K)) :
    ¬ ∀ b : d.G E ⋙ (d.reconstruction E true).evaluation n ⟶
        (d.reconstruction E false).evaluation n ⋙
          (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G,
      ∀ K : (sequenceProperty l E X).FullSubcategory,
        ((d.reconstruction E true).evaluation n).map ((d.adjunction E).unit.app K) ≫
          b.app ((d.F E).obj K) ≫
          (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G.map
            ((d.evaluationF E n).hom.app K) =
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.unit.app
          (((d.reconstruction E true).evaluation n).obj K) := by
  intro h
  have hd := h (d.evaluationG E n).hom K
  have hd' := h (-(d.evaluationG E n).hom) K
  change ((d.reconstruction E true).evaluation n).map ((d.adjunction E).unit.app K) ≫
    (-((d.evaluationG E n).hom.app ((d.F E).obj K))) ≫
    (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G.map
      ((d.evaluationF E n).hom.app K) = _ at hd'
  simp only [Preadditive.comp_neg, Preadditive.neg_comp] at hd'
  rw [hd] at hd'
  exact hne hd'

end EvaluationMate

/-- The finite evaluation of the transported adjunction unit satisfies the
finite-stage adjunction-unit equation.  This is the unit clause in the strict
system transport calculation of Zheng, Lemma 5.22.
(blueprint: new-lem-sf-exceptional-ring-transport-core-evaluation-unit) -/
theorem exceptional_transport_core_evaluation_unit
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l,
      Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l,
      LeftRealization.{u} l Ω c s (operation s))
    (d : TransportCoreData l Ω D hl c operation left) :
    ∀ (E : FieldStage.{u} l) (n : ℕ)
      (K : (sequenceProperty l E X).FullSubcategory),
      ((d.reconstruction E true).evaluation n).map ((d.adjunction E).unit.app K) ≫
        (d.evaluationG E n).hom.app ((d.F E).obj K) ≫
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G.map
          ((d.evaluationF E n).hom.app K) =
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.unit.app
        (((d.reconstruction E true).evaluation n).obj K) := by
  intro E n K
  exact (d.evaluationG E n).unit K
end WeilConjectures.ExceptionalIntegralScalar
