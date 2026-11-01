/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassTensorPullback
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSectionAdjointNaturality
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement

/-! # Normalized positive twist pullback from tensor and line pullback

Source: blueprint latest, smooth-purity tower classes proof, clause (4).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private def secondIso {T : Scheme.{u}} {N N' : Systems T (Arings l E T)}
    (e : N ≅ N') : tensorRight l E T N ≅ tensorRight l E T N' := by
  let := SemilinearSections.abelianSheafify.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  let := SemilinearSections.locallyBijective.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  let S := PresheafOfModules.sheafification
    (R := SemilinearSections.ring (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (systemRing l E T)) (𝟙 _)
  refine NatIso.ofComponents (fun M ↦ S.mapIso
    { hom := SheafOfModules.siteTensorSecondMap M.val e.hom.val
      inv := SheafOfModules.siteTensorSecondMap M.val e.inv.val
      hom_inv_id := ?_
      inv_hom_id := ?_ }) ?_
  · ext U : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change x ⊗ₜ[(systemRing l E T).obj.obj U] e.inv.val.app U (e.hom.val.app U y) =
      x ⊗ₜ[(systemRing l E T).obj.obj U] y
    rw [show e.inv.val.app U (e.hom.val.app U y) = y from
      congrArg (fun a ↦ a.val.app U y) e.hom_inv_id]
  · ext U : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change x ⊗ₜ[(systemRing l E T).obj.obj U] e.hom.val.app U (e.inv.val.app U y) =
      x ⊗ₜ[(systemRing l E T).obj.obj U] y
    rw [show e.hom.val.app U (e.inv.val.app U y) = y from
      congrArg (fun a ↦ a.val.app U y) e.inv_hom_id]
  · intro M M' f
    exact SheafOfModules.siteSheafTensorSecondMap_naturality f e.hom

private theorem secondIso_pure {T : Scheme.{u}} {N N' : Systems T (Arings l E T)}
    (e : N ≅ N') (M : Systems T (Arings l E T)) (U : (ℕ × T.ProEt)ᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    ((secondIso l E e).hom.app M).val.app U (tensorPure l E T M N U x y) =
      tensorPure l E T M N' U x (e.hom.val.app U y) := by
  let := SemilinearSections.abelianSheafify.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  let := SemilinearSections.locallyBijective.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  exact SheafOfModules.scalarTensor_second_tmul M e.hom U x y

set_option maxHeartbeats 1600000 in
-- Tensor sheafification and the pure-section transports elaborate large comparison terms.
private theorem transport_positive
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f)
    {cY : Chern l E Y} {cX : Chern l E X}
    (k : TensorPullback l E f g) (p : LinePullback l E f g cY cX)
    (FY : Systems Y (Arings l E Y) ⥤ Systems Y (Arings l E Y))
    (FX : Systems X (Arings l E X) ⥤ Systems X (Arings l E X))
    (hY : FY = positive l E cY) (hX : FX = positive l E cX) :
    ∃ e : FY ⋙ g.pull ≅ g.pull ⋙ FX,
      ∀ (M : Systems Y (Arings l E Y)) (n : ℕ) (U : Y.ProEtᵒᵖ)
        (x : M.val.obj (op (n, U.unop)))
        (y : (lineModule l E cY).val.obj (op (n, U.unop)))
        (v : (FY.obj M).val.obj (op (n, U.unop)))
        (x' : (g.pull.obj M).val.obj (op (n, (chart f U).unop)))
        (y' : (lineModule l E cX).val.obj (op (n, (chart f U).unop))),
        HEq v (pure l E cY M (op (n, U.unop)) x y) →
        HEq x' (adjointSection l E g (𝟙 (g.pull.obj M)) n U x) →
        HEq y' (adjointSection l E g p.iso.hom n U y) →
        HEq (adjointSection l E g (e.hom.app M) n U v)
          (pure l E cX (g.pull.obj M) (op (n, (chart f U).unop)) x' y') := by
  subst FY
  subst FX
  let e := k.iso (lineModule l E cY) ≪≫
    Functor.isoWhiskerLeft g.pull (secondIso l E p.iso)
  refine ⟨e, ?_⟩
  intro M n U x y v x' y' hv hx hy
  cases eq_of_heq hv
  cases eq_of_heq hx
  cases eq_of_heq hy
  change HEq (sectionAdjoint l E g
    ((k.iso (lineModule l E cY)).hom.app M ≫
      (secondIso l E p.iso).hom.app (g.pull.obj M)) n U
        (tensorPure l E Y M (lineModule l E cY) (op (n, U.unop)) x y)) _
  rw [sectionAdjoint_postcomp]
  have h := eq_of_heq (k.normalization M (lineModule l E cY) n U x y)
  rw [h]
  apply heq_of_eq
  erw [secondIso_pure l E p.iso (g.pull.obj M) (op (n, (chart f U).unop))]
  congr 1
  have hp := sectionAdjoint_postcomp l E g (𝟙 (g.pull.obj (lineModule l E cY)))
    p.iso.hom n U y
  simpa only [Category.id_comp, sectionAdjoint] using hp.symm

/-- The normalized tensor comparison and the prescribed root-line pullback give
positive twist pullback with its required pure-tensor adjoint formula.

Source: latest blueprint `sk-prop-sp-tower-geometric-classes.proof.md`, clause (4);
step 14 of `lem-sp-prescribed-projective-class-package`.
(blueprint: lem-sp-tower-class-positive-pullback-existence).

Proof: compose the tensor pullback comparison at the source root line with
identity tensor the line pullback isomorphism. Transport the endpoints using
the equalities fixing the positive functors. Naturality of the ordinary
adjunction in its target identifies the adjoint of this composite with the
line map applied to the second tensor factor. The tensor normalization and
functoriality on pure tensors give exactly the two stipulated adjunction
units. This is a construction on whole systems, before evaluation. -/
theorem positivePullback_nonempty
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f)
    {cY : Chern l E Y} {cX : Chern l E X}
    (tY : Twisting l E cY) (tX : Twisting l E cX)
    (k : TensorPullback l E f g) (p : LinePullback l E f g cY cX) :
    Nonempty (PositivePullback l E f g tY tX p) := by
  obtain ⟨e, he⟩ := transport_positive l E g k p tY.equivalence.functor
    tX.equivalence.functor tY.forward tX.forward
  exact ⟨⟨e, he⟩⟩

end AlgebraicGeometry.ProEtale.SpTowerClasses
