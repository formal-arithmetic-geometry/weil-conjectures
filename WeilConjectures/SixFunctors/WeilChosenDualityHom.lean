/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefVerdierWeilEquivariance
public import WeilConjectures.AlgebraicGeometry.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SfWeilSheafComplex
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist

/-! # Verdier Hom bijections for chosen structure right adjoints

Source: latest Weil blueprint, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance.proof.md, paragraphs 1--2; normalization of
chosen structure adjoints (blueprint: lem-sf-weil-chosen-duality-hom).

All categories below are fixed-pair categories, without a triangulation on pairs.
The object and arrow equations retain the specified internal Hom operation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Endofunctor

namespace WeilConjectures.SfWeilChosenDuality

/-- Lift the canonical contravariant dual using its specified Frobenius comparison.
Source: blueprint equivariance proof paragraph 1
(blueprint: lem-sf-weil-chosen-duality-hom). -/
def pairDual {C : Type a} [Category.{b} C] (P : C ⥤ C) (V : Cᵒᵖ ⥤ C)
    (c : V ⋙ P ≅ P.op ⋙ V) : (IsoAlgebra P)ᵒᵖ ⥤ IsoAlgebra P :=
  IsoAlgebra.opFunctor ⋙ IsoAlgebra.mapOfNatIso c

section Transport
variable {X : Type a} {Y : Type v} [Category.{b} X] [Category.{u} Y]
  (P : Y ⥤ Y) (H : X ⥤ Y) (V : X ⥤ IsoAlgebra P)
  (e : H ≅ V ⋙ IsoAlgebra.forget P)

-- Keep H literal on objects and arrows; conjugate only its Frobenius structure.
private def transportLift : X ⥤ IsoAlgebra P where
  obj K := IsoAlgebra.mk (H.obj K)
    (P.mapIso (e.app K) ≪≫ (V.obj K).str ≪≫ (e.app K).symm)
  map {K M} f := ObjectProperty.homMk
    { f := H.map f
      h := by
        dsimp
        simp only [Category.assoc]
        rw [← P.map_comp_assoc, e.hom.naturality f]
        simp only [Functor.comp_map, P.map_comp, IsoAlgebra.forget_map, Category.assoc]
        rw [reassoc_of% (V.map f).hom.h]
        rw [← e.inv.naturality f]
        rfl }
  map_id K := IsoAlgebra.hom_ext (H.map_id K)
  map_comp f g := IsoAlgebra.hom_ext (H.map_comp f g)

private def transportLiftIso : transportLift P H V e ≅ V :=
  NatIso.ofComponents (fun K ↦ IsoAlgebra.isoMk (e.app K) (by
    dsimp [transportLift]
    simp)) (fun f ↦ IsoAlgebra.hom_ext (e.hom.naturality f))

end Transport

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom]
  [QuasiCompact T₀.hom] [IsSeparated T₀.hom]

/-- The geometric common-stage category used by the assertion, with no completion.
Source: blueprint common-stage convention
(blueprint: lem-sf-weil-chosen-duality-hom). -/
abbrev Carrier := generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber T₀).left

/-- The actual fixed-pair category at algebraically closed coefficients.
Source: blueprint chosen-duality assertion
(blueprint: lem-sf-weil-chosen-duality-hom). -/
abbrev Pairs := sfCommonStageWeilComplex D l hl T₀ Ω

/-- The canonical duality functor on fixed pairs, with dual Frobenius structure.
Source: blueprint equivariance proof paragraphs 1--2
(blueprint: lem-sf-weil-chosen-duality-hom). -/
def geometricDual (B : CoefVerdierWeil.FiberDuality D l hl Ω T₀)
    (W : CoefVerdierWeil.Coefficients D l hl Ω T₀ B) :
    (Pairs D l hl Ω T₀)ᵒᵖ ⥤ Pairs D l hl Ω T₀ :=
  letI := CoefVerdierWeil.fiberStructureLocallyFiniteType D T₀
  letI := CoefVerdierWeil.fiberStructureQuasiCompact D T₀
  letI := CoefVerdierWeil.fiberStructureSeparated D T₀
  pairDual (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω)
    B.duality.dual W.common.comparison

/-- The canonical dualizing pair carries the exceptional-adjoint Weil structure.
Source: blueprint equivariance proof paragraph 1
(blueprint: lem-sf-weil-chosen-duality-hom). -/
def geometricOmega (B : CoefVerdierWeil.FiberDuality D l hl Ω T₀)
    (W : CoefVerdierWeil.Coefficients D l hl Ω T₀ B) : Pairs D l hl Ω T₀ :=
  letI := CoefVerdierWeil.fiberStructureLocallyFiniteType D T₀
  letI := CoefVerdierWeil.fiberStructureQuasiCompact D T₀
  letI := CoefVerdierWeil.fiberStructureSeparated D T₀
  IsoAlgebra.mk B.omega W.common.omegaStructure

/-- The coefficient unit has its canonical Frobenius structure, normalized by the
specified left unitor. This is the unit equation in the dependency's DualizingMate.
Source: blueprint equivariance proof paragraph 1
(blueprint: lem-sf-weil-chosen-duality-hom). -/
def IsCoefficientUnit (unit : Pairs D l hl Ω (CoefVerdierWeil.pointModel D)) : Prop :=
  ∃ theta :
      (sfCommonStageWeilFrobeniusPullback D l hl (CoefVerdierWeil.pointModel D) Ω).obj
        (CoefVerdierWeil.commonUnit D l hl Ω (CoefVerdierWeil.pointModel D)) ≅
      CoefVerdierWeil.commonUnit D l hl Ω (CoefVerdierWeil.pointModel D),
    unit = IsoAlgebra.mk _ theta ∧
    ∀ M : Carrier D l Ω (CoefVerdierWeil.pointModel D),
      (CoefVerdierWeil.commonMu D l hl Ω (CoefVerdierWeil.pointModel D)
        (CoefVerdierWeil.commonUnit D l hl Ω (CoefVerdierWeil.pointModel D)) M).hom ≫
      (@commonStageDerivedTensor l _ Ω _ _ _
        (D.geometricFiber (CoefVerdierWeil.pointModel D)).left
        (fun x ↦ sfWeilPrimeInvertible D l hl (CoefVerdierWeil.pointModel D) x)).map
          (Prod.mkHom theta.hom (𝟙 _)) ≫
      (CoefVerdierWeil.commonUnitor D l hl Ω (CoefVerdierWeil.pointModel D)
        ((sfCommonStageWeilFrobeniusPullback D l hl
          (CoefVerdierWeil.pointModel D) Ω).obj M)).hom =
      (sfCommonStageWeilFrobeniusPullback D l hl (CoefVerdierWeil.pointModel D) Ω).map
        (CoefVerdierWeil.commonUnitor D l hl Ω (CoefVerdierWeil.pointModel D) M).hom

/-- A lifted Hom functor has exactly the recorded internal-Hom objects and arrow maps.
The Frobenius structure is fixed below by its componentwise postcomposition comparison
with the canonical dual, whose standard Weil lift is already recorded.
Source: blueprint chosen-duality assertion and proof step 2
(blueprint: lem-sf-weil-chosen-duality-hom). -/
def IsHomLift (omega : Pairs D l hl Ω T₀)
    (permitted : ∀ K : Carrier D l Ω T₀,
      commonStageHomPairs l Ω (D.geometricFiber T₀).left (op K, omega.carrier))
    (V : (Pairs D l hl Ω T₀)ᵒᵖ ⥤ Pairs D l hl Ω T₀) : Prop :=
  (∀ K : Pairs D l hl Ω T₀,
    (V.obj (op K)).carrier =
      (CoefQbarVerdier.homDual l Ω (D.geometricFiber T₀).left
        omega.carrier permitted).obj (op K.carrier)) ∧
  (∀ (K M : Pairs D l hl Ω T₀) (f : K ⟶ M),
    HEq (V.map f.op).hom.f
      ((CoefQbarVerdier.homDual l Ω (D.geometricFiber T₀).left
        omega.carrier permitted).map f.hom.f.op))

section Structure
open CoefVerdierWeil

variable (c₀ : Compactification (structureModel D T₀).left)
  (A : FiberExceptional D l hl Ω T₀ (structureModel D T₀)
    (FrobeniusExchange.geometricCompactification D (structureModel D T₀) c₀))
  (Z : FrobeniusAdjunctions D l hl Ω T₀ (structureModel D T₀) c₀ A)

/-- The compact-support functor with its canonical geometric Frobenius lift.
Source: blueprint equivariance proof paragraph 2
(blueprint: lem-sf-weil-chosen-duality-hom). -/
def structureLeft : Pairs D l hl Ω T₀ ⥤ Pairs D l hl Ω (pointModel D) :=
  IsoAlgebra.mapOfNatIso Z.common.left

/-- The exceptional structure right adjoint with its canonical mate lift.
Source: blueprint equivariance proof paragraph 2
(blueprint: lem-sf-weil-chosen-duality-hom). -/
def structureRight : Pairs D l hl Ω (pointModel D) ⥤ Pairs D l hl Ω T₀ :=
  IsoAlgebra.mapOfNatIso Z.common.right

/-- All conclusions for an arbitrary chosen right adjoint. The internal-Hom object
and arrow equations specify D itself; the comparison equation specifies postcomposition
by n itself. Biduality and the Hom bijection are on fixed pairs. The last equation records
both-variable naturality.
Source: blueprint equivariance proof paragraphs 1--2 and chosen-adjoint normalization
(blueprint: lem-sf-weil-chosen-duality-hom). -/
def ChosenConclusion
    (adjCan : structureLeft D l hl Ω T₀ c₀ A Z ⊣ structureRight D l hl Ω T₀ c₀ A Z)
    (unit : Pairs D l hl Ω (pointModel D))
    (canonicalPermitted : ∀ K : Carrier D l Ω T₀,
      commonStageHomPairs l Ω (D.geometricFiber T₀).left
        (op K, ((structureRight D l hl Ω T₀ c₀ A Z).obj unit).carrier))
    (C : (Pairs D l hl Ω T₀)ᵒᵖ ⥤ Pairs D l hl Ω T₀)
    (J : Pairs D l hl Ω (pointModel D) ⥤ Pairs D l hl Ω T₀)
    (adj : structureLeft D l hl Ω T₀ c₀ A Z ⊣ J) : Prop :=
  ∃ (n : J.obj unit ≅ (structureRight D l hl Ω T₀ c₀ A Z).obj unit),
    n = (adj.rightAdjointUniq adjCan).app unit ∧
    ∃ (permitted : ∀ K : Carrier D l Ω T₀,
      commonStageHomPairs l Ω (D.geometricFiber T₀).left (op K, (J.obj unit).carrier)),
    ∃ (V : (Pairs D l hl Ω T₀)ᵒᵖ ⥤ Pairs D l hl Ω T₀),
      IsHomLift D l hl Ω T₀ (J.obj unit) permitted V ∧
      ∃ (c : V ≅ C),
        (∀ K : Pairs D l hl Ω T₀,
          HEq (c.hom.app (op K)).hom.f
            ((commonStageDerivedInternalHom l Ω (D.geometricFiber T₀).left).map
              (ObjectProperty.homMk
                (X := ⟨(op K.carrier, (J.obj unit).carrier), permitted K.carrier⟩)
                (Y := ⟨(op K.carrier,
                  ((structureRight D l hl Ω T₀ c₀ A Z).obj unit).carrier),
                    canonicalPermitted K.carrier⟩)
                (Prod.mkHom (𝟙 (op K.carrier)) n.hom.hom.f)))) ∧
        V.IsEquivalence ∧
        Nonempty (𝟭 (Pairs D l hl Ω T₀) ≅ V.rightOp ⋙ V) ∧
        (∀ K M : Pairs D l hl Ω T₀,
          Function.Bijective (fun f : K ⟶ M ↦ V.map f.op)) ∧
        (∀ (K' K M M' : Pairs D l hl Ω T₀)
          (a₁ : K' ⟶ K) (f : K ⟶ M) (b₁ : M ⟶ M'),
          V.map (a₁ ≫ f ≫ b₁).op = V.map b₁.op ≫ V.map f.op ≫ V.map a₁.op)

/-- The literal canonical-adjoint Hom lift is identified with geometric duality
by internal-Hom postcomposition with the dualizing identification iω inverse.
Source: blueprint equivariance proof paragraphs 1--2
(blueprint: lem-sf-weil-chosen-duality-hom). -/
def CanonicalHomComparison (B : FiberDuality D l hl Ω T₀)
    (IH : FiberInternalHom D l hl Ω T₀ B)
    (W : Coefficients D l hl Ω T₀ B)
    (unit : Pairs D l hl Ω (pointModel D))
    (iω : geometricOmega D l hl Ω T₀ B W ≅
      (structureRight D l hl Ω T₀ c₀ A Z).obj unit)
    (permitted : ∀ K : Carrier D l Ω T₀,
      commonStageHomPairs l Ω (D.geometricFiber T₀).left
        (op K, ((structureRight D l hl Ω T₀ c₀ A Z).obj unit).carrier))
    (C : (Pairs D l hl Ω T₀)ᵒᵖ ⥤ Pairs D l hl Ω T₀) : Prop :=
  letI := fiberStructureLocallyFiniteType D T₀
  letI := fiberStructureQuasiCompact D T₀
  letI := fiberStructureSeparated D T₀
  ∃ d : C ≅ geometricDual D l hl Ω T₀ B W,
    ∀ K : Pairs D l hl Ω T₀,
      HEq (d.hom.app (op K)).hom.f
        ((commonStageDerivedInternalHom l Ω (D.geometricFiber T₀).left).map
          (ObjectProperty.homMk
            (X := ⟨(op K.carrier,
              ((structureRight D l hl Ω T₀ c₀ A Z).obj unit).carrier), permitted K.carrier⟩)
            (Y := ⟨(op K.carrier, B.omega), IH.permitted K.carrier⟩)
            (Prod.mkHom (𝟙 (op K.carrier)) iω.inv.hom.f)) ≫
          IH.comparison.inv.app (op K.carrier))

end Structure

private def homTargetIso
    (_B : CoefVerdierWeil.FiberDuality D l hl Ω T₀)
    (omega omega' : Carrier D l Ω T₀)
    (h : ∀ K : Carrier D l Ω T₀,
      commonStageHomPairs l Ω (D.geometricFiber T₀).left (op K, omega))
    (h' : ∀ K : Carrier D l Ω T₀,
      commonStageHomPairs l Ω (D.geometricFiber T₀).left (op K, omega'))
    (n : omega ≅ omega') :
    CoefQbarVerdier.homDual l Ω (D.geometricFiber T₀).left omega h ≅
      CoefQbarVerdier.homDual l Ω (D.geometricFiber T₀).left omega' h' :=
  NatIso.ofComponents (fun K ↦
    (commonStageDerivedInternalHom l Ω (D.geometricFiber T₀).left).mapIso
      (ObjectProperty.isoMk _ (Iso.prod (Iso.refl K) n))) (by
    intro K M f
    dsimp [CoefQbarVerdier.homDual]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply ObjectProperty.hom_ext
    ext <;> simp)

private theorem homPermitted
    (B : CoefVerdierWeil.FiberDuality D l hl Ω T₀) (K M : Carrier D l Ω T₀) :
    commonStageHomPairs l Ω (D.geometricFiber T₀).left (op K, M) := by
  let := CoefVerdierWeil.fiberStructureLocallyFiniteType D T₀
  let := CoefVerdierWeil.fiberStructureQuasiCompact D T₀
  let := CoefVerdierWeil.fiberStructureSeparated D T₀
  -- commonStageHomPairs asks for exactly this predicate at the compositum.
  exact (B.finite.hom _).permitted _ _

private def geometricBiduality
    (B : CoefVerdierWeil.FiberDuality D l hl Ω T₀)
    (W : CoefVerdierWeil.Coefficients D l hl Ω T₀ B) :
    𝟭 (Pairs D l hl Ω T₀) ≅
      (geometricDual D l hl Ω T₀ B W).rightOp ⋙ geometricDual D l hl Ω T₀ B W := by
  letI := CoefVerdierWeil.fiberStructureLocallyFiniteType D T₀
  letI := CoefVerdierWeil.fiberStructureQuasiCompact D T₀
  letI := CoefVerdierWeil.fiberStructureSeparated D T₀
  exact NatIso.ofComponents (fun K ↦ IsoAlgebra.isoMk (B.duality.bidual.app K.carrier)
    (W.common.biduality_equivariant K).symm) (by
      intro K M f
      exact IsoAlgebra.hom_ext (B.duality.bidual.hom.naturality f.hom.f))

private theorem antiEquivalence {X : Type a} [Category.{b} X]
    (V : Xᵒᵖ ⥤ X) (d : 𝟭 X ≅ V.rightOp ⋙ V) : V.IsEquivalence := by
  let c : V ⋙ V.rightOp ≅ 𝟭 Xᵒᵖ :=
    NatIso.ofComponents (fun K ↦ (d.app K.unop).op) (by
      intro K M f
      apply Quiver.Hom.unop_inj
      exact (d.hom.naturality f.unop).symm)
  exact Functor.IsEquivalence.mk' V.rightOp c.symm d.symm

private def transportBiduality {X : Type a} [Category.{b} X]
    {V C : Xᵒᵖ ⥤ X} (c : V ≅ C) (d : 𝟭 X ≅ C.rightOp ⋙ C) :
    𝟭 X ≅ V.rightOp ⋙ V := by
  let rc : C.rightOp ≅ V.rightOp :=
    NatIso.ofComponents (fun K ↦ (c.app (op K)).op) (by
      intro K M f
      apply Quiver.Hom.unop_inj
      exact (c.hom.naturality f.op).symm)
  exact d ≪≫ Functor.isoWhiskerRight rc C ≪≫ Functor.isoWhiskerLeft V.rightOp c.symm

/-- Chosen structure adjoints give the specified Verdier anti-equivalence, natural
Weil biduality, and Hom bijections whose forward map is exactly the dual arrow action.
Source: latest blueprint cor-coef-verdier-weil-equivariance.proof.md, paragraphs 1--2;
chosen-adjoint normalization (blueprint: lem-sf-weil-chosen-duality-hom).

Proof:
1. cor-coef-verdier-weil-equivariance supplies B, its internal-Hom identification,
Weil structures W, the canonical exceptional structure adjunction and Weil biduality.
Lift the actual adjunction unit and counit to pairs. Its dualizing normalization gives
the coefficient unit and iω. Biduality makes the canonical pair dual an anti-equivalence.
Apply det-sp-unique-right-adjoint: alpha = adj.rightAdjointUniq adjCan is the unique
counit-compatible comparison. Set n = alpha at the unit. Identify the canonical Hom dual
with geometric duality by postcomposition with iω inverse and the recorded IH comparison.
2. Apply internal Hom to (identity,n). Its inverse is internal Hom of (identity,n inverse).
Constructibility follows from the canonical dual. Use the standard lift of
lem-fix-weil-operations: theta_H(K,W) = H(theta_K inverse,theta_W) followed by the
Frobenius comparison. The Weil equation for n and naturality of that comparison show
that H(identity,n) commutes with the two dual structures. Bifunctoriality gives
c_A D(u) = C(u) c_B, so c is a natural Weil isomorphism, with the displayed component.
3. If b is canonical biduality, set delta_K = b_K followed by c_(C K) inverse and
D(c_K). All factors are Weil isomorphisms. Naturality of b and c proves naturality
of delta. Delta and its opposite make D and its opposite quasi-inverses.
4. Conjugation v by c_A and c_B inverse identifies maps D B to D A with maps C B
to C A. Compose with the canonical dual's Hom bijection. The equation from step 2
identifies the forward map with D(u). Contravariant functoriality gives the stated
both-variable naturality equation. -/
theorem chosen_duality_hom :
    ∃ (B : CoefVerdierWeil.FiberDuality D l hl Ω T₀)
      (IH : CoefVerdierWeil.FiberInternalHom D l hl Ω T₀ B)
      (W : CoefVerdierWeil.Coefficients D l hl Ω T₀ B),
      CoefVerdierWeil.DualizingNormalization D l hl Ω T₀ B W ∧
      ∀ c₀ : Compactification (CoefVerdierWeil.structureModel D T₀).left,
      ∃ (A : CoefVerdierWeil.FiberExceptional D l hl Ω T₀
          (CoefVerdierWeil.structureModel D T₀)
          (FrobeniusExchange.geometricCompactification D
            (CoefVerdierWeil.structureModel D T₀) c₀))
        (Z : CoefVerdierWeil.FrobeniusAdjunctions D l hl Ω T₀
          (CoefVerdierWeil.structureModel D T₀) c₀ A)
        (adjCan : structureLeft D l hl Ω T₀ c₀ A Z ⊣ structureRight D l hl Ω T₀ c₀ A Z),
        (∀ K : Pairs D l hl Ω T₀,
          HEq (adjCan.unit.app K).hom.f (A.adjunction.unit.app K.carrier)) ∧
        (∀ M : Pairs D l hl Ω (CoefVerdierWeil.pointModel D),
          HEq (adjCan.counit.app M).hom.f (A.adjunction.counit.app M.carrier)) ∧
        ∃ (unit : Pairs D l hl Ω (CoefVerdierWeil.pointModel D)),
          IsCoefficientUnit D l hl Ω unit ∧
          ∃ iω : geometricOmega D l hl Ω T₀ B W ≅
            (structureRight D l hl Ω T₀ c₀ A Z).obj unit,
          ∃ (permitted : ∀ K : Carrier D l Ω T₀,
            commonStageHomPairs l Ω (D.geometricFiber T₀).left
              (op K, ((structureRight D l hl Ω T₀ c₀ A Z).obj unit).carrier))
            (C : (Pairs D l hl Ω T₀)ᵒᵖ ⥤ Pairs D l hl Ω T₀),
            IsHomLift D l hl Ω T₀ ((structureRight D l hl Ω T₀ c₀ A Z).obj unit)
              permitted C ∧
            CanonicalHomComparison D l hl Ω T₀ c₀ A Z B IH W unit iω permitted C ∧
            ∀ (J : Pairs D l hl Ω (CoefVerdierWeil.pointModel D) ⥤ Pairs D l hl Ω T₀)
              (adj : structureLeft D l hl Ω T₀ c₀ A Z ⊣ J),
              ChosenConclusion D l hl Ω T₀ c₀ A Z adjCan unit permitted C J adj := by
  classical
  let := CoefVerdierWeil.fiberStructureLocallyFiniteType D T₀
  let := CoefVerdierWeil.fiberStructureQuasiCompact D T₀
  let := CoefVerdierWeil.fiberStructureSeparated D T₀
  obtain ⟨B, ⟨IH⟩, _, W, norm, _⟩ := coef_verdier_weil_equivariance D l hl Ω T₀
  refine ⟨B, IH, W, norm, ?_⟩
  intro c₀
  obtain ⟨A, Z, _, hmate⟩ := norm c₀
  unfold CoefVerdierWeil.DualizingMate at hmate
  obtain ⟨theta, htheta, i, hi⟩ := hmate
  let adjCan : structureLeft D l hl Ω T₀ c₀ A Z ⊣
      structureRight D l hl Ω T₀ c₀ A Z :=
    IsoAlgebra.mapOfNatIsoAdjunction A.adjunction Z.common.left Z.common.right
      Z.common.mate.symm
  refine ⟨A, Z, adjCan, (fun _ ↦ HEq.rfl), (fun _ ↦ HEq.rfl), ?_⟩
  let unit : Pairs D l hl Ω (CoefVerdierWeil.pointModel D) := IsoAlgebra.mk _ theta
  let iω : geometricOmega D l hl Ω T₀ B W ≅
      (structureRight D l hl Ω T₀ c₀ A Z).obj unit :=
    IsoAlgebra.isoMk i hi.symm
  -- The fixed-pair comparison determines the transported Frobenius structure.
  let p := homPermitted D l hl Ω T₀ B
  let G := geometricDual D l hl Ω T₀ B W
  let F := IsoAlgebra.forget (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω)
  let eG : F.op ⋙ CoefQbarVerdier.homDual l Ω (D.geometricFiber T₀).left B.omega
      IH.permitted ≅ G ⋙ IsoAlgebra.forget _ :=
    Functor.isoWhiskerLeft F.op IH.comparison.symm ≪≫
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl)
  let e := Functor.isoWhiskerLeft F.op (homTargetIso D l hl Ω T₀ B _ _
    (fun K ↦ p K _) IH.permitted
    ((IsoAlgebra.forget _).mapIso iω.symm)) ≪≫ eG
  let C := transportLift _ _ G e
  let d := transportLiftIso _ _ G e
  let bC := transportBiduality d (geometricBiduality D l hl Ω T₀ B W)
  refine ⟨unit, ⟨theta, rfl, htheta⟩, iω, (fun K ↦ p K _), C,
    ⟨(fun _ ↦ rfl), (fun _ _ _ ↦ HEq.rfl)⟩, ⟨d, ?_⟩, ?_⟩
  · intro K
    apply heq_of_eq
    dsimp [d, transportLiftIso, e, eG, homTargetIso]
    simp only [Category.comp_id]
    rfl
  · intro J adj
    -- This particular normalization is required by ChosenConclusion.
    let n := (adj.rightAdjointUniq adjCan).app unit
    let e' := Functor.isoWhiskerLeft F.op (homTargetIso D l hl Ω T₀ B _ _
      (fun K ↦ p K _) (fun K ↦ p K _) ((IsoAlgebra.forget _).mapIso n)) ≪≫
        (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl) :
          F.op ⋙ CoefQbarVerdier.homDual l Ω (D.geometricFiber T₀).left
            ((structureRight D l hl Ω T₀ c₀ A Z).obj unit).carrier
            (fun K ↦ p K _) ≅ C ⋙ IsoAlgebra.forget _)
    let V := transportLift _ _ C e'
    let c := transportLiftIso _ _ C e'
    let bV := transportBiduality c bC
    have : V.IsEquivalence := antiEquivalence V bV
    refine ⟨n, rfl, (fun K ↦ p K _), V,
      ⟨(fun _ ↦ rfl), (fun _ _ _ ↦ HEq.rfl)⟩, c, ?_,
      inferInstance, ⟨bV⟩, ?_, ?_⟩
    · intro K
      apply heq_of_eq
      dsimp [c, transportLiftIso, e', homTargetIso]
      simp only [Category.comp_id]
      rfl
    · intro K M
      exact ((Functor.FullyFaithful.ofFullyFaithful V).map_bijective (op M) (op K)).comp
        (opEquiv (op M) (op K)).symm.bijective
    · intro K' K M M' a₁ f b₁
      simp only [op_comp, Functor.map_comp, Category.assoc]

end WeilConjectures.SfWeilChosenDuality
