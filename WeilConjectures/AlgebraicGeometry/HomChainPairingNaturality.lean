/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PodCtfPairingMaps
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions

/-! # Target naturality of the counit-evaluation projection pairing

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
fix-lem-tensor-adjunction.proof.md, Step 1
(blueprint: lem-pod-hom-chain-pairing-naturality).

All objects are in the recorded restricted domains of PodCtfAdjunctionData.
The forward projection and internal Hom are the shared canonical constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.HomChain

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorOperationDatum D C E n hn) (s : PodCoefficientStage)
  {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
  (R : PodCtfAdjunctionData (PodCoefficientStage.operations S s)
    (PodCoefficientStage.domain S s) (PodCoefficientStage.homPairs (S := S) s)
    (PodCoefficientStage.internalHom (S := S) s) (PodCoefficientStage.tensor S s) f c)

/-- L_N, formed from the specified internal Hom and exceptional pullback.
Source: the displayed definitions before the identities
(blueprint: lem-pod-hom-chain-pairing-naturality). -/
def inner (M : (PodCoefficientStage.domain S s X).FullSubcategory) (N :
      (PodCoefficientStage.domain S s Y).FullSubcategory) :
      (PodCoefficientStage.domain S s X).FullSubcategory := (PodCtfPairing.homX S s f c R M).obj
      (R.exceptional.obj N)

/-- A_N is the ordinary direct image of L_N.
Source: the displayed definitions (blueprint: lem-pod-hom-chain-pairing-naturality). -/
def outer (M : (PodCoefficientStage.domain S s X).FullSubcategory) (N :
      (PodCoefficientStage.domain S s Y).FullSubcategory) :
      (PodCoefficientStage.domain S s Y).FullSubcategory := R.direct.obj (inner S s f c R M N)

/-- B_N is the specified target internal Hom.
Source: the displayed definitions (blueprint: lem-pod-hom-chain-pairing-naturality). -/
def target (M : (PodCoefficientStage.domain S s X).FullSubcategory) (N :
      (PodCoefficientStage.domain S s Y).FullSubcategory) :
      (PodCoefficientStage.domain S s Y).FullSubcategory := (PodCtfPairing.homY S s f c R
      (R.support.obj M)).obj N

/-- h is the internal-Hom image of the exceptional image of r.
Source: the displayed definitions (blueprint: lem-pod-hom-chain-pairing-naturality). -/
def innerMap (M : (PodCoefficientStage.domain S s X).FullSubcategory) {N N' :
      (PodCoefficientStage.domain S s Y).FullSubcategory}
      (r : N ⟶ N') : inner S s f c R M N ⟶ inner S s f c R M N' :=
  (PodCtfPairing.homX S s f c R M).map (R.exceptional.map r)

/-- a is the ordinary direct image of h.
Source: the displayed definitions (blueprint: lem-pod-hom-chain-pairing-naturality). -/
def outerMap (M : (PodCoefficientStage.domain S s X).FullSubcategory) {N N' :
      (PodCoefficientStage.domain S s Y).FullSubcategory}
      (r : N ⟶ N') : outer S s f c R M N ⟶ outer S s f c R M N' :=
  R.direct.map (innerMap S s f c R M r)

/-- Evaluation is the counit of the supplied left-factor tensor-Hom adjunction.
Source: lem-pod-closed-uncurry-laws, evaluation clause
(blueprint: lem-pod-hom-chain-pairing-naturality). -/
def evaluation (M : (PodCoefficientStage.domain S s X).FullSubcategory) (V :
      (PodCoefficientStage.domain S s X).FullSubcategory) :
    (@MonoidalCategory.tensorLeft _ _ R.closedX.closed.monoidal M).obj
      ((PodCtfPairing.homX S s f c R M).obj V) ⟶ V :=
  (R.tensorAdjunctionX M).counit.app V

/-- q_N applies the ordinary counit in the second tensor factor and then evaluates.
Source: the displayed definition of q_N
(blueprint: lem-pod-hom-chain-pairing-naturality). -/
def q (M : (PodCoefficientStage.domain S s X).FullSubcategory) (N :
      (PodCoefficientStage.domain S s Y).FullSubcategory) :
    (@MonoidalCategory.tensorLeft _ _ R.closedX.closed.monoidal M).obj (R.pull.obj
      (outer S s f c R M N)) ⟶ R.exceptional.obj N :=
  (@MonoidalCategory.tensorLeft _ _ R.closedX.closed.monoidal M).map
      (R.ordinaryAdjunction.counit.app (inner S s f c R M N)) ≫
    evaluation S s f c R M (R.exceptional.obj N)

variable [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]

/-- p_N is exactly projection, compact support of q_N, then exceptional counit.
Source: the displayed definition of p_N
(blueprint: lem-pod-hom-chain-pairing-naturality). -/
def p (M : (PodCoefficientStage.domain S s X).FullSubcategory) (N :
      (PodCoefficientStage.domain S s Y).FullSubcategory) :
    (@MonoidalCategory.tensorLeft _ _ R.closedY.closed.monoidal (R.support.obj M)).obj
      (outer S s f c R M N) ⟶ N :=
  PodCtfPairing.projection S s f c R M (outer S s f c R M N) ≫ R.support.map (q S s f c R M N) ≫
    R.exceptionalAdjunction.counit.app N

/-- All six requested identities, in their original order, as actual morphism
identities in the chosen derived coefficient categories.
Source: Step 1, naturality of the specified Hom-chain maps
(blueprint: lem-pod-hom-chain-pairing-naturality). -/
def Naturality (M : (PodCoefficientStage.domain S s X).FullSubcategory) {N N' :
      (PodCoefficientStage.domain S s Y).FullSubcategory} (r : N ⟶ N') : Prop :=
  (R.pull.map (outerMap S s f c R M r) ≫ R.ordinaryAdjunction.counit.app (inner S s f c R M N') =
    R.ordinaryAdjunction.counit.app (inner S s f c R M N) ≫ innerMap S s f c R M r) ∧
  (R.support.map (R.exceptional.map r) ≫ R.exceptionalAdjunction.counit.app N' =
    R.exceptionalAdjunction.counit.app N ≫ r) ∧
  ((@MonoidalCategory.tensorLeft _ _ R.closedX.closed.monoidal M).map (innerMap S s f c R M r)
      ≫ evaluation S s f c R M (R.exceptional.obj N') =
    evaluation S s f c R M (R.exceptional.obj N) ≫ R.exceptional.map r) ∧
  ((@MonoidalCategory.tensorLeft _ _ R.closedX.closed.monoidal M).map (R.pull.map
      (outerMap S s f c R M r)) ≫ q S s f c R M N' =
    q S s f c R M N ≫ R.exceptional.map r) ∧
  (PodCtfPairing.projection S s f c R M (outer S s f c R M N) ≫
      R.support.map ((@MonoidalCategory.tensorLeft _ _ R.closedX.closed.monoidal M).map
      (R.pull.map (outerMap S s f c R M r))) =
    (@MonoidalCategory.tensorLeft _ _ R.closedY.closed.monoidal (R.support.obj M)).map
      (outerMap S s f c R M r) ≫
      PodCtfPairing.projection S s f c R M (outer S s f c R M N')) ∧
  ((@MonoidalCategory.tensorLeft _ _ R.closedY.closed.monoidal (R.support.obj M)).map
      (outerMap S s f c R M r) ≫ p S s f c R M N' = p S s f c R M N ≫ r)

/-- Fixing the first input in projection-formula naturality gives the raw square.
Source: fix-prop-projection-formula, naturality clause
(blueprint: lem-pod-hom-chain-pairing-naturality). -/
private theorem raw_projection_naturality
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    {T T' : (PodCoefficientStage.domain S s Y).FullSubcategory} (b : T ⟶ T') :
    ((PodCoefficientStage.tensor S s Y).obj (R.support.obj M).obj).map b ≫
        PodCtfPairing.rawProjection S s f c R M T' =
      PodCtfPairing.rawProjection S s f c R M T ≫
        ((PodCoefficientStage.operations S s).support f c).map
          (((PodCoefficientStage.tensor S s X).obj M.obj).map (R.pull.map b)) := by
  cases s with
  | finite =>
    let L : finiteTorConstructibleCategory C.l E n hn Y.obj.left :=
      ⟨T.obj.obj, T.property⟩
    let L' : finiteTorConstructibleCategory C.l E n hn Y.obj.left :=
      ⟨T'.obj.obj, T'.property⟩
    have h := (compactSupportProjectionFormula S).1.naturality f c (𝟙 M.obj)
      (ObjectProperty.homMk (X := L) (Y := L') b.hom.hom)
    simp only [(S.finite.support f c).map_id M.obj,
      (CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Y).map_id,
      (CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X).map_id,
      CategoryTheory.NatTrans.id_app, Category.id_comp] at h
    exact h
  | integral =>
    have h := (compactSupportProjectionFormula S).2.1.naturality f c
      T.property T'.property (𝟙 M.obj) b.hom
    simp only [(S.higher.integral.support f c).map_id M.obj,
      (S.higher.integralTensor Y).map_id,
      (S.higher.integralTensor X).map_id,
      CategoryTheory.NatTrans.id_app, Category.id_comp] at h
    exact h
  | rational =>
    have h := (compactSupportProjectionFormula S).2.2.1.naturality f c
      trivial trivial (𝟙 M.obj) b.hom
    simp only [(S.higher.rational.support f c).map_id M.obj,
      (S.higher.rationalTensor Y).map_id,
      (S.higher.rationalTensor X).map_id,
      CategoryTheory.NatTrans.id_app, Category.id_comp] at h
    exact h
  | common =>
    have h := (compactSupportProjectionFormula S).2.2.2.1.naturality f c
      trivial trivial (𝟙 M.obj) b.hom
    simp only [(S.closure.commonStage.support f c).map_id M.obj,
      (S.closure.commonStageTensor Y).map_id,
      (S.closure.commonStageTensor X).map_id,
      CategoryTheory.NatTrans.id_app, Category.id_comp] at h
    exact h

/-- The projection isomorphism retains the specified forward map at every stage.
Source: def-pod-ctf-pairing-maps
(blueprint: lem-pod-hom-chain-pairing-naturality). -/
private theorem raw_projection_iso_hom
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (T : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    (PodCtfPairing.rawProjectionIso S s f c R M T).hom =
      PodCtfPairing.rawProjection S s f c R M T := by
  cases s <;> rfl

/-- Transport the raw natural transformation through the recorded tensor comparisons.
Source: Step 1, projection square
(blueprint: lem-pod-hom-chain-pairing-naturality). -/
private theorem projection_naturality
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    {T T' : (PodCoefficientStage.domain S s Y).FullSubcategory} (b : T ⟶ T') :
    PodCtfPairing.projection S s f c R M T ≫
        R.support.map
          ((@MonoidalCategory.tensorLeft _ _ R.closedX.closed.monoidal M).map
            (R.pull.map b)) =
      (@MonoidalCategory.tensorLeft _ _ R.closedY.closed.monoidal (R.support.obj M)).map b ≫
        PodCtfPairing.projection S s f c R M T' := by
  let F := (PodCoefficientStage.operations S s).support f c
  let raw : (PodCoefficientStage.tensor S s Y).obj (R.support.obj M).obj ⟶
      R.pull ⋙ (PodCoefficientStage.tensor S s X).obj M.obj ⋙ F :=
    { app := fun T ↦ PodCtfPairing.rawProjection S s f c R M T
      naturality := fun _ _ b ↦ raw_projection_naturality S s f c R M b }
  let a := R.tensorY (R.support.obj M)
  let e := isoWhiskerRight (isoWhiskerLeft R.pull (R.tensorX M)) F
  have h := (a.hom ≫ raw ≫ e.inv).naturality b
  apply (PodCoefficientStage.domain S s Y).ι.map_injective
  simp only [CategoryTheory.Functor.map_comp, PodCtfPairing.projection,
    PodCtfPairing.projectionIso, CategoryTheory.Functor.preimageIso_hom,
    CategoryTheory.Functor.map_preimage]
  change
    (((R.tensorY (R.support.obj M)).app T).hom ≫
        (PodCtfPairing.rawProjectionIso S s f c R M T).hom ≫
        F.map ((R.tensorX M).app (R.pull.obj T)).inv) ≫
      F.map (((@MonoidalCategory.tensorLeft _ _ R.closedX.closed.monoidal M).map
        (R.pull.map b)).hom) =
    ((@MonoidalCategory.tensorLeft _ _ R.closedY.closed.monoidal
      (R.support.obj M)).map b).hom ≫
      ((R.tensorY (R.support.obj M)).app T').hom ≫
        (PodCtfPairing.rawProjectionIso S s f c R M T').hom ≫
        F.map ((R.tensorX M).app (R.pull.obj T')).inv
  rw [raw_projection_iso_hom, raw_projection_iso_hom]
  exact h.symm

/-- Target naturality of the specified counit-evaluation projection pairing, at
all four actual coefficient stages, for separated finite-type morphisms.
Source: blueprint fix-lem-tensor-adjunction.proof.md, Step 1
(blueprint: lem-pod-hom-chain-pairing-naturality).

Proof: (1) The recorded restricted functors and Hom put all objects and arrows
in the indicated full domains by their types.
(2) Apply Mathlib's counit naturality at h for the ordinary adjunction and at r
for the exceptional adjunction. These are the constructed restrictions R from
det-thm-sf-ctf-stability-adjunctions.
(3) Evaluation is (R.tensorAdjunctionX M).counit; its naturality at R.exceptional.map r
is the evaluation square, with left-factor tensor and no additional symmetry.
(4) Expand q, use tensor functoriality and the ordinary/evaluation squares.
(5) The canonical raw projection is natural by fix-prop-projection-formula.
Transport through R.tensorY, R.tensorX and the fully faithful inclusion, whose
naturality squares identify exactly the tensorLeft maps displayed below.
(6) Expand p, move a through projection, combine support images by functoriality,
use the q square, and finally exceptional counit naturality. The composite is p_N;r.
These are actual derived morphisms at each stage, including completed integral
operations and common finite coefficient stages. No reduction faithfulness is used. -/
theorem pairing_naturality
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    {N N' : (PodCoefficientStage.domain S s Y).FullSubcategory} (r : N ⟶ N') :
    Naturality S s f c R M r := by
  let TX := @MonoidalCategory.tensorLeft _ _ R.closedX.closed.monoidal M
  let TY := @MonoidalCategory.tensorLeft _ _ R.closedY.closed.monoidal (R.support.obj M)
  have ho : R.pull.map (outerMap S s f c R M r) ≫
      R.ordinaryAdjunction.counit.app (inner S s f c R M N') =
      R.ordinaryAdjunction.counit.app (inner S s f c R M N) ≫
        innerMap S s f c R M r :=
    R.ordinaryAdjunction.counit_naturality (innerMap S s f c R M r)
  have he : R.support.map (R.exceptional.map r) ≫
      R.exceptionalAdjunction.counit.app N' =
      R.exceptionalAdjunction.counit.app N ≫ r :=
    R.exceptionalAdjunction.counit_naturality r
  have hv : TX.map (innerMap S s f c R M r) ≫
      evaluation S s f c R M (R.exceptional.obj N') =
      evaluation S s f c R M (R.exceptional.obj N) ≫ R.exceptional.map r :=
    (R.tensorAdjunctionX M).counit_naturality (R.exceptional.map r)
  have hq : TX.map (R.pull.map (outerMap S s f c R M r)) ≫
      q S s f c R M N' = q S s f c R M N ≫ R.exceptional.map r := by
    dsimp only [q, TX, outer] at *
    erw [← Category.assoc, ← CategoryTheory.Functor.map_comp, ho,
      CategoryTheory.Functor.map_comp, Category.assoc, hv]
    exact (Category.assoc _ _ _).symm
  have hp : PodCtfPairing.projection S s f c R M (outer S s f c R M N) ≫
      R.support.map (TX.map (R.pull.map (outerMap S s f c R M r))) =
      TY.map (outerMap S s f c R M r) ≫
        PodCtfPairing.projection S s f c R M (outer S s f c R M N') := by
    exact projection_naturality S s f c R M (outerMap S s f c R M r)
  refine ⟨ho, he, hv, hq, hp, ?_⟩
  dsimp only [p]
  rw [← Category.assoc, ← Category.assoc, ← hp]
  simp only [Category.assoc]
  rw [← Category.assoc (R.support.map _) (R.support.map _),
    ← R.support.map_comp, hq, R.support.map_comp, Category.assoc, he]

end WeilConjectures.HomChain
