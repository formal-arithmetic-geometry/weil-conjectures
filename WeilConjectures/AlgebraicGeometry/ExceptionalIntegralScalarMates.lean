/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalIntegralScalarMatesData


import WeilConjectures.CategoryTheory.SystemSelectedAdjunctionIsos
import WeilConjectures.CategoryTheory.SystemSelectedNormalization
import WeilConjectures.AlgebraicGeometry.RamifiedSystemRecoveryBounds
import WeilConjectures.AlgebraicGeometry.FiniteCtfTriangulated
import WeilConjectures.CategoryTheory.AdjointEquivalenceConjugation
import WeilConjectures.AlgebraicGeometry.ExceptionalIntegralReductionLeftCompatibility
import WeilConjectures.AlgebraicGeometry.ExceptionalIntegralLeftScalarMates
import WeilConjectures.AlgebraicGeometry.ExceptionalIntegralRightScalarInvertibility
import WeilConjectures.AlgebraicGeometry.ExceptionalIntegralScalarMateCompletion
import WeilConjectures.AlgebraicGeometry.ExceptionalIntegralSystemScalarCore
import WeilConjectures.AlgebraicGeometry.ExceptionalIntegralSystemSelectedLeft

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
set_option linter.unusedVariables false
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

variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

section
universe a b x y av bv xv yv
open CategoryTheory CategoryTheory.Functor
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {X : Type x} [Category.{xv} X] {Y : Type y} [Category.{yv} Y]
  (eX : A ≌ X) (eY : B ≌ Y) {F : X ⥤ Y} {G : Y ⥤ X} (adj : F ⊣ G)
  {F₀ : A ⥤ B} {G₀ : B ⥤ A}
  (rF : F₀ ≅ eX.functor ⋙ F ⋙ eY.inverse)
  (rG : G₀ ≅ eY.functor ⋙ G ⋙ eX.inverse)

private theorem conjugatedCounit (N : B) :
    (eY.functor.map (rF.hom.app (G₀.obj N)) ≫
      eY.counit.app (F.obj (eX.functor.obj (G₀.obj N)))) ≫
      F.map (eX.functor.map (rG.hom.app N) ≫
        eX.counit.app (G.obj (eY.functor.obj N))) ≫
      adj.counit.app (eY.functor.obj N) =
    eY.functor.map
      (((((eX.toAdjunction.comp adj).comp eY.symm.toAdjunction).ofNatIsoLeft
        rF.symm).ofNatIsoRight rG.symm).counit.app N) := by
  simp only [Adjunction.ofNatIsoRight_counit, Adjunction.ofNatIsoLeft_counit,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Iso.symm_inv,
    AdjointEquivalenceConjugation.conjugation_counit, Functor.map_comp,
    Equivalence.counit, Equivalence.symm_inverse]
  have hr := rF.hom.naturality (rG.hom.app N)
  dsimp only [Functor.comp_map] at hr
  have hc (Z : Y) (k : Z ⟶ eY.functor.obj N) :
      eY.functor.map (eY.inverse.map k) ≫ eY.functor.map (eY.unitIso.inv.app N) =
        eY.counit.app Z ≫ k := by
    rw [← eY.counit_app_functor N]
    exact eY.counit_naturality k
  symm
  calc
    _ = eY.functor.map (rF.hom.app (G₀.obj N)) ≫
        eY.functor.map (eY.inverse.map
          (F.map (eX.functor.map (rG.hom.app N)) ≫
            F.map (eX.counit.app (G.obj (eY.functor.obj N))) ≫
              adj.counit.app (eY.functor.obj N))) ≫
        eY.functor.map (eY.unitIso.inv.app N) := by
      simpa only [Functor.map_comp, Category.assoc, Functor.comp_map] using
        congrArg (fun k ↦ eY.functor.map k ≫
          eY.functor.map (eY.inverse.map
            (F.map (eX.counit.app (G.obj (eY.functor.obj N))))) ≫
          eY.functor.map (eY.inverse.map (adj.counit.app (eY.functor.obj N))) ≫
          eY.functor.map (eY.unitIso.inv.app N)) hr
    _ = _ := by rw [hc]; simp only [Category.assoc]

end

section
universe a b x y av bv xv yv
open CategoryTheory CategoryTheory.Functor
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {X : Type x} [Category.{xv} X] {Y : Type y} [Category.{yv} Y]
  {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
  {F' : X ⥤ Y} {G' : Y ⥤ X} (adj' : F' ⊣ G')
  {TX U : A ⥤ X} {TY V : B ⥤ Y}
  (q₀ : F ⋙ TY ≅ TX ⋙ F') (b₀ : G ⋙ TX ⟶ TY ⋙ G')
  (q₁ : F ⋙ V ≅ U ⋙ F') (b₁ : G ⋙ U ⟶ V ⋙ G')
  (eX : TX ≅ U) (eY : TY ≅ V)
  (h₀ : ∀ N, q₀.hom.app (G.obj N) ≫ F'.map (b₀.app N) ≫
    adj'.counit.app (TY.obj N) = TY.map (adj.counit.app N))
  (h₁ : ∀ N, q₁.hom.app (G.obj N) ≫ F'.map (b₁.app N) ≫
    adj'.counit.app (V.obj N) = V.map (adj.counit.app N))
  (hq : ∀ K, q₀.hom.app K ≫ F'.map (eX.hom.app K) =
    eY.hom.app (F.obj K) ≫ q₁.hom.app K)

include adj adj' h₀ h₁ hq in
private theorem scalarMateIntertwines (N : B) :
    b₀.app N ≫ G'.map (eY.hom.app N) = eX.hom.app (G.obj N) ≫ b₁.app N := by
  apply ((adj'.homEquiv _ _).symm).injective
  change F'.map _ ≫ _ = F'.map _ ≫ _
  simp only [Functor.map_comp, Category.assoc]
  apply (cancel_epi (q₀.hom.app (G.obj N))).mp
  have hε := adj'.counit.naturality (eY.hom.app N)
  dsimp only [Functor.comp_map, Functor.id_map] at hε
  calc
    _ = q₀.hom.app (G.obj N) ≫ F'.map (b₀.app N) ≫
        adj'.counit.app (TY.obj N) ≫ eY.hom.app N := by rw [hε]
    _ = TY.map (adj.counit.app N) ≫ eY.hom.app N := by
      simpa only [Category.assoc] using congrArg (· ≫ eY.hom.app N) (h₀ N)
    _ = eY.hom.app (F.obj (G.obj N)) ≫ V.map (adj.counit.app N) :=
      eY.hom.naturality (adj.counit.app N)
    _ = eY.hom.app (F.obj (G.obj N)) ≫ q₁.hom.app (G.obj N) ≫
        F'.map (b₁.app N) ≫ adj'.counit.app (V.obj N) := by rw [h₁]
    _ = _ := by rw [← Category.assoc, ← hq]; simp only [Category.assoc]

end

section
universe a b x y p q av bv xv yv pv qv
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {X : Type x} [Category.{xv} X] {Y : Type y} [Category.{yv} Y]
  {P : Type p} [Category.{pv} P] {Q : Type q} [Category.{qv} Q]
  {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
  {F' : X ⥤ Y} {G' : Y ⥤ X} (adj' : F' ⊣ G')
  {F'' : P ⥤ Q} {G'' : Q ⥤ P} (adj'' : F'' ⊣ G'')
  {TX : A ⥤ X} {TY : B ⥤ Y} {VX : X ⥤ P} {VY : Y ⥤ Q}
  (q₁ : F ⋙ TY ≅ TX ⋙ F') (b₁ : G ⋙ TX ⟶ TY ⋙ G')
  (q₂ : F' ⋙ VY ≅ VX ⋙ F'') (b₂ : G' ⋙ VX ⟶ VY ⋙ G'')
  (h₁ : ∀ N, q₁.hom.app (G.obj N) ≫ F'.map (b₁.app N) ≫
    adj'.counit.app (TY.obj N) = TY.map (adj.counit.app N))
  (h₂ : ∀ N, q₂.hom.app (G'.obj N) ≫ F''.map (b₂.app N) ≫
    adj''.counit.app (VY.obj N) = VY.map (adj'.counit.app N))
include h₁ h₂ in
private theorem pasteCounit (N : B) :
    VY.map (q₁.hom.app (G.obj N)) ≫ q₂.hom.app (TX.obj (G.obj N)) ≫
      F''.map (VX.map (b₁.app N) ≫ b₂.app (TY.obj N)) ≫
      adj''.counit.app (VY.obj (TY.obj N)) =
      VY.map (TY.map (adj.counit.app N)) := by
  simp only [Functor.map_comp, Category.assoc]
  have hn := q₂.hom.naturality (b₁.app N)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [h₂ (TY.obj N)]
  rw [← VY.map_comp_assoc, ← VY.map_comp, Category.assoc, h₁]
end

/-- Construction of the mate data used by the integral scalar comparison.  This is the
first strictly smaller part of the construction; the remaining reduction maps are
recorded separately below because they require the same chosen mate.
Source: Zheng, Lemma 5.22 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-mates).
The finite scalar constructions are transported through the specified reconstruction,
and the completed scalar comparison supplies the integral component.  The resulting
record contains the fixed scalar functors, their realizations, and all mate equations.
-/
theorem exceptionalIntegralScalarMates_data_mates
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
    Nonempty (Mates l Ω c operation left) := by
  obtain ⟨z⟩ := exceptionalIntegralLeftScalarMates l Ω D hl c operation left transport
  exact exceptionalIntegralScalarMateCompletion l Ω z
    (exceptionalIntegralRightScalarInvertibility l Ω D hl c operation left transport z)

private theorem reductionCounit
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
    (E : FieldStage.{u} l) (N : C.{u} l Ω Y (.integral E)) :
    (transport.reductionF E).hom.app ((operation (.integral E)).G.obj N) ≫
      (transport.F E).map ((transport.reductionG E).hom.app N) ≫
      (transport.adjunction E).counit.app
        ((transport.reconstruction E false).equivalence.functor.obj N) =
      (transport.reconstruction E false).equivalence.functor.map
        ((operation (.integral E)).adjunction.counit.app N) := by
  rw [transport.reductionF_eq, transport.reductionG_eq, transport.adjunction_eq]
  exact conjugatedCounit (transport.reconstruction E true).equivalence
    (transport.reconstruction E false).equivalence (transport.adjunction E)
    (transport.realizeF E) (transport.realizeG E) N

/-! The pointwise reduction construction is the remaining independent part of the
    reduction-data theorem.  Isolating one coefficient stage and one level keeps the
    unresolved construction strictly below the quantified assertion above it.
    Source: Zheng, Lemma 5.22 and Proposition 5.26.
    (blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise).
    The finite-level adjunction units and counits are transported through the chosen
    reconstruction, and their normalized evaluation equations give the four fields of
    `ReductionMates` for this fixed `E` and `n`. -/
theorem exceptionalIntegralScalarMates_data_reduction_pointwise
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
    (d : Mates l Ω c operation left) (E : FieldStage.{u} l) (n : ℕ) :
    Nonempty (ReductionMates l Ω D hl c operation left transport d E n) := by
  let ex := (transport.reconstruction E true).equivalence.functor
  let ey := (transport.reconstruction E false).equivalence.functor
  let vx := (transport.reconstruction E true).evaluation n
  let vy := (transport.reconstruction E false).evaluation n
  let ev (side : Bool) := integralReductionEvaluation l Ω d E n side
    (transport.reconstruction E side)
  let q := isoWhiskerRight (transport.reductionF E) vy ≪≫
    isoWhiskerLeft ex (transport.evaluationF E n)
  let b := whiskerRight (transport.reductionG E).hom vx ≫
    whiskerLeft ey (transport.evaluationG E n).hom
  have hq := integralReductionLeftCompatibility l Ω D hl c operation left transport d E n
  have hc (N : C.{u} l Ω Y (.integral E)) :
      q.hom.app ((operation (.integral E)).G.obj N) ≫
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F.map (b.app N) ≫
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.counit.app
          ((ey ⋙ vy).obj N) = (ey ⋙ vy).map
            ((operation (.integral E)).adjunction.counit.app N) := by
    dsimp only [q, b, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Functor.comp_obj,
      Functor.comp_map]
    simp only [Functor.map_comp, Category.assoc]
    have hn := (transport.evaluationF E n).hom.naturality
      ((transport.reductionG E).hom.app N)
    dsimp only [Functor.comp_map] at hn
    calc
      _ = vy.map ((transport.reductionF E).hom.app
            ((operation (.integral E)).G.obj N)) ≫
          vy.map ((transport.F E).map ((transport.reductionG E).hom.app N)) ≫
          (transport.evaluationF E n).hom.app ((transport.G E).obj (ey.obj N)) ≫
          (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F.map
            ((transport.evaluationG E n).hom.app (ey.obj N)) ≫
          (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.counit.app
            (vy.obj (ey.obj N)) := by
        simpa only [ex, ey, vx, vy, Functor.comp_obj, Category.assoc] using
          congrArg (fun k ↦ vy.map ((transport.reductionF E).hom.app
            ((operation (.integral E)).G.obj N)) ≫ k ≫
          (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F.map
            ((transport.evaluationG E n).hom.app (ey.obj N)) ≫
          (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.counit.app
            (vy.obj (ey.obj N))) hn.symm
      _ = vy.map ((transport.reductionF E).hom.app
            ((operation (.integral E)).G.obj N)) ≫
          vy.map ((transport.F E).map ((transport.reductionG E).hom.app N)) ≫
          vy.map ((transport.adjunction E).counit.app (ey.obj N)) := by
        rw [transport.evaluation_counit]
      _ = _ := by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg vy.map (reductionCounit l Ω D hl c operation left transport E N)
  refine ⟨{
    evaluation := ev
    evaluation_normalized := fun side K ↦
      integralReductionEvaluation_normalized l Ω d E n side
        (transport.reconstruction E side) K
    q_evaluation := hq
    b_evaluation := ?_ }⟩
  intro N
  let := (d.scalar (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
    (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
    (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) true).commShift
  let := (d.scalar (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
    (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
    (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) false).commShift
  exact scalarMateIntertwines (operation (.integral E)).adjunction
    (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction
    (U := ex ⋙ vx) (V := ey ⋙ vy)
    (Mates.q l Ω d _ (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩))
    (Mates.b l Ω d _ (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩)).hom q b
    (ev true) (ev false)
    (d.comparison (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
      (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩)).counit hc hq N


/-
The reduction part is a separate strictly smaller assertion: once the scalar mate
record is fixed, it supplies the reduction comparison at every finite level.
Source: Zheng, Lemma 5.22 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction).
The system evaluation and counit maps are obtained by applying the actual finite
scalar maps to the reconstruction unit and counit; their equations are the transported
adjunction equations.  The statement is parameterized by the chosen mate record.
-/
theorem exceptionalIntegralScalarMates_data_reduction
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
    (d : Mates l Ω c operation left) :
    Nonempty (∀ (E : FieldStage.{u} l) (n : ℕ),
      ReductionMates l Ω D hl c operation left transport d E n) := by
  classical
  exact ⟨fun E n =>
    Classical.choice (exceptionalIntegralScalarMates_data_reduction_pointwise
      l Ω D hl c operation left transport d E n)⟩

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
  obtain ⟨d⟩ := exceptionalIntegralScalarMates_data_mates l Ω D hl c operation left transport
  obtain ⟨red⟩ := exceptionalIntegralScalarMates_data_reduction
    l Ω D hl c operation left transport d
  exact ⟨d, red, trivial⟩

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
  obtain ⟨core⟩ := exceptionalIntegralSystemScalarCore
    l Ω D hl c operation left transport d E L i
  obtain ⟨sel⟩ := exceptionalIntegralSystemSelectedLeft
    l Ω D hl c operation left transport d red E L i core
  refine ⟨{ coefficient := core.coefficient, coefficient_model := core.coefficient_model
            scalar := core.scalar, scalar_eq := core.scalar_eq
            reduction := core.reduction, reduction_normalized := core.reduction_normalized
            q := core.q, b := core.b, counit := core.counit
            q_reduction := core.q_reduction, b_reduction := core.b_reduction
            selected := sel.selected, selected_square := sel.selected_square
            selected_balanced := sel.selected_balanced, q_selected := sel.q_selected
            b_selected := ?_ }⟩
  intro e he z N
  let := (d.scalar z.change z.allowed true).commShift
  let := (d.scalar z.change z.allowed false).commShift
  let TX := (transport.reconstruction E true).evaluation z.n
  let TY := (transport.reconstruction E false).evaluation z.n
  let VX := (transport.reconstruction L true).evaluation z.m
  let VY := (transport.reconstruction L false).evaluation z.m
  let SX := (d.scalar z.change z.allowed true).functor
  let SY := (d.scalar z.change z.allowed false).functor
  let q₀ := isoWhiskerRight core.q VY ≪≫
    isoWhiskerLeft (core.scalar true) (transport.evaluationF L z.m)
  let b₀ := whiskerRight core.b.hom VX ≫
    whiskerLeft (core.scalar false) (transport.evaluationG L z.m).hom
  let q₁ := isoWhiskerRight (transport.evaluationF E z.n) SY ≪≫
    isoWhiskerLeft TX (Mates.q l Ω d z.change z.allowed)
  let b₁ := whiskerRight (transport.evaluationG E z.n).hom SX ≫
    whiskerLeft TY (Mates.b l Ω d z.change z.allowed).hom
  have h₀ := pasteCounit (transport.adjunction E) (transport.adjunction L)
    (operation (.finite L ⟨z.m + 1, Nat.succ_pos z.m⟩)).adjunction
    core.q core.b.hom (transport.evaluationF L z.m) (transport.evaluationG L z.m).hom
    core.counit (transport.evaluation_counit L z.m)
  have h₁ := pasteCounit (transport.adjunction E)
    (operation (.finite E ⟨z.n + 1, Nat.succ_pos z.n⟩)).adjunction
    (operation (.finite L ⟨z.m + 1, Nat.succ_pos z.m⟩)).adjunction
    (transport.evaluationF E z.n) (transport.evaluationG E z.n).hom
    (Mates.q l Ω d z.change z.allowed) (Mates.b l Ω d z.change z.allowed).hom
    (transport.evaluation_counit E z.n) (d.comparison z.change z.allowed).counit
  have hr := scalarMateIntertwines (transport.adjunction E)
    (operation (.finite L ⟨z.m + 1, Nat.succ_pos z.m⟩)).adjunction
    (TX := core.scalar true ⋙ VX) (TY := core.scalar false ⋙ VY)
    (U := (transport.reconstruction E true).evaluation z.n ⋙ SX)
    (V := (transport.reconstruction E false).evaluation z.n ⋙ SY)
    q₀ b₀ q₁ b₁ (sel.selected e he z true) (sel.selected e he z false)
    (by
      intro N
      simpa only [q₀, b₀, VX, VY, Functor.comp_map, Functor.comp_obj, Iso.trans_hom,
        NatTrans.comp_app, isoWhiskerRight_hom,
        isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Category.assoc] using h₀ N)
    (by
      intro N
      simpa only [q₁, b₁, TX, TY, SX, SY, Functor.comp_map, Functor.comp_obj,
        Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
        isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Category.assoc] using h₁ N)
    (by
      intro K
      simpa only [q₀, q₁, TX, TY, SX, SY, VX, VY, Functor.comp_map,
        Functor.comp_obj, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
        isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Category.assoc] using
        sel.q_selected e he z K) N
  simpa only [b₀, b₁, TX, TY, SX, SY, VX, VY, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Functor.map_comp,
    Functor.comp_map, Functor.comp_obj, Category.assoc] using hr

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
