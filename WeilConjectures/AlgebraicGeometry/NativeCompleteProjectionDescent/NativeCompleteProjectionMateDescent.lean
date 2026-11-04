/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionReductionSquare

/-! # Native consumer of the normalized reduction square

Source: current blueprint, sec-smooth-purity,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, (2)--(3)
(blueprint: lem-sp-complete-projection-mate-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Bifunctoriality of the native compact-support projection map. -/
private theorem exceptionalProjection_bifunctorial {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) {M M' : Integral l E X} {K K' : Integral l E Y}
    (v : M ⟶ M') (w : K ⟶ K') :
    ((integralImage l E c).map v ⊗ₘ w) ≫
      CondensedRing.exceptionalProjectionMorphismOfCompactification
        (spIntegralCondensed l E) c M' K' =
    CondensedRing.exceptionalProjectionMorphismOfCompactification (spIntegralCondensed l E) c M K ≫
      (integralImage l E c).map (v ⊗ₘ (ringedPull l E f).map w) := by
  have hr : (integralImage l E c).obj M' ◁ w ≫
        CondensedRing.exceptionalProjectionMorphismOfCompactification
          (spIntegralCondensed l E) c M' K' =
      CondensedRing.exceptionalProjectionMorphismOfCompactification
          (spIntegralCondensed l E) c M' K ≫
        (integralImage l E c).map (M' ◁ (ringedPull l E f).map w) :=
    CondensedRing.exceptionalProjectionMorphismOfCompactification_natural_right
      (spIntegralCondensed l E) c M' w
  have hl : (integralImage l E c).map v ▷ K ≫
        CondensedRing.exceptionalProjectionMorphismOfCompactification
          (spIntegralCondensed l E) c M' K =
      CondensedRing.exceptionalProjectionMorphismOfCompactification
          (spIntegralCondensed l E) c M K ≫
        (integralImage l E c).map (v ▷ (ringedPull l E f).obj K) :=
    CondensedRing.exceptionalProjectionMorphismOfCompactification_natural_left
      (spIntegralCondensed l E) c v K
  calc ((integralImage l E c).map v ⊗ₘ w) ≫
        CondensedRing.exceptionalProjectionMorphismOfCompactification
          (spIntegralCondensed l E) c M' K'
      _ = (integralImage l E c).map v ▷ K ≫ (integralImage l E c).obj M' ◁ w ≫
          CondensedRing.exceptionalProjectionMorphismOfCompactification
            (spIntegralCondensed l E) c M' K' := by
        rw [MonoidalCategory.tensorHom_def, Category.assoc]
      _ = ((integralImage l E c).map v ▷ K ≫
          CondensedRing.exceptionalProjectionMorphismOfCompactification
            (spIntegralCondensed l E) c M' K) ≫
            (integralImage l E c).map (M' ◁ (ringedPull l E f).map w) := by
        rw [hr, Category.assoc]
      _ = CondensedRing.exceptionalProjectionMorphismOfCompactification
            (spIntegralCondensed l E) c M K ≫
          (integralImage l E c).map (v ▷ (ringedPull l E f).obj K) ≫
            (integralImage l E c).map (M' ◁ (ringedPull l E f).map w) := by
        rw [hl, Category.assoc]
      _ = _ := by
        rw [← Functor.map_comp, ← MonoidalCategory.tensorHom_def]

/-- Descent of the native compactification projection through its actual reduction units.
Source: blueprint proof (3), tower projection followed by derived inverse limit
(blueprint: lem-sp-complete-projection-mate-descent).

Proof:
1. Apply `projection_reduction_square`, and cancel the invertible target coordinate.
This identifies reduction of the native projection with `transportedProjection`.
2. Naturality of the actual reduction/limit unit gives pi;eta_U = eta_V;L(r(pi)).
Substitute step 1 and cancel the invertible unit at U, giving the displayed formula.
3. The proper and open system projection factors, and both coordinates, are isomorphisms.
Their composite is an isomorphism. Conjugate its inverse by the actual units to obtain
an inverse of pi; the two compositions are identities by functoriality of L.
4. The native proper and open projection maps and pullback compositor are natural in
both inputs. Their composite has exactly the last displayed bifunctoriality square.
No faithfulness of evaluations, nor a monoidal structure on total limit, is used. -/
theorem complete_projection_mate_descent (m : DescentModels l E)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpl : p ≠ l)
    (X Y : Over (Scheme.Spec.obj (op (CommRingCat.of k))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (AX : Limit l E X.left (m.abelian X.left) (m.red X.left))
    (AZ : Limit l E c.Z (m.abelian c.Z) (m.red c.Z))
    (AY : Limit l E Y.left (m.abelian Y.left) (m.red Y.left))
    (M : Integral l E X.left) (K : Integral l E Y.left)
    (hbM : IsIso (reconstruction l E m c AX AZ AY M))
    (hbH : IsIso (reconstruction l E m c AX AZ AY (inputTensor l E m f.left M K)))
    (hOpen : IsIso (systemOpenInverse l E m c.i ((red l E m X.left).obj M)
      ((VaryingRing.G (rings l E) (transitions l E) c.g).obj ((red l E m Y.left).obj K))))
    (_hProper : IsIso (((systemProperProjection l E m c.g).app
      ((VaryingRing.J (rings l E) (transitions l E) c.i).obj ((red l E m X.left).obj M))).app
        ((red l E m Y.left).obj K)))
    (hUnitU : IsIso ((adj l E m Y.left AY).unit.app
      ((integralImage l E c).obj (inputTensor l E m f.left M K))))
    (hUnitV : IsIso ((adj l E m Y.left AY).unit.app ((integralImage l E c).obj M ⊗ K))) :
    let U := (integralImage l E c).obj (inputTensor l E m f.left M K)
    let V := (integralImage l E c).obj M ⊗ K
    let theta := transportedProjection l E m c AX AZ AY M K hbM hbH hOpen
    let pi := CondensedRing.exceptionalProjectionMorphismOfCompactification
      (spIntegralCondensed l E) c M K
    pi = (adj l E m Y.left AY).unit.app V ≫ (lim l E m Y.left AY).map theta ≫
      inv ((adj l E m Y.left AY).unit.app U) ∧
    ∃ (t : (red l E m Y.left).obj V ≅ (red l E m Y.left).obj U) (e : V ≅ U),
      t.hom = theta ∧ e.hom = pi ∧
      e.inv = (adj l E m Y.left AY).unit.app U ≫
        (lim l E m Y.left AY).map t.inv ≫ inv ((adj l E m Y.left AY).unit.app V) ∧
      ∀ (M' : Integral l E X.left) (K' : Integral l E Y.left)
        (v : M ⟶ M') (w : K ⟶ K'),
        ((integralImage l E c).map v ⊗ₘ w) ≫
          CondensedRing.exceptionalProjectionMorphismOfCompactification
            (spIntegralCondensed l E) c M' K' =
        pi ≫ (integralImage l E c).map (v ⊗ₘ (ringedPull l E f.left).map w) := by
  intro U V theta pi
  let := hbM
  let := hbH
  let := hOpen
  let := _hProper
  let := hUnitU
  let := hUnitV
  have ht : IsIso theta := by
    let B := (red l E m X.left).obj M
    let C := (red l E m Y.left).obj K
    let q := (VaryingRing.gComp (rings l E) (transitions l E) c.i c.g).inv.app C ≫
      eqToHom (congrArg (fun g : X.left ⟶ Y.left ↦
        (VaryingRing.G (rings l E) (transitions l E) g).obj C) c.comm.symm)
    have hq' : IsIso ((m.systems X.left).closed.tensor.map (Prod.mkHom (𝟙 B) q)) := by
      change IsIso (((m.systems X.left).closed.tensor.mapIso
        (Iso.prod (Iso.refl B) (asIso q))).hom)
      infer_instance
    dsimp only [theta, transportedProjection, systemProjection]
    infer_instance
  let t := asIso theta
  have hred : (red l E m Y.left).map pi = theta := by
    have h := projection_reduction_square l E m c AX AZ AY M K hOpen
    have hh : (red l E m Y.left).map pi ≫
        (targetComparison l E m c AX AZ AY M K hbH).hom =
      (sourceComparison l E m c AX AZ AY M K hbM).hom ≫
        systemProjection l E m c ((red l E m X.left).obj M)
          ((red l E m Y.left).obj K) hOpen := by
      simpa only [targetComparison, sourceComparison, Iso.trans_hom, Functor.mapIso_hom,
        Iso.prod_hom, asIso_hom, Iso.refl_hom, Iso.app_hom, Category.assoc,
        Functor.map_comp] using h
    dsimp only [theta, transportedProjection]
    rw [← Category.assoc, ← hh]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hpi : pi = (adj l E m Y.left AY).unit.app V ≫ (lim l E m Y.left AY).map theta ≫
      inv ((adj l E m Y.left AY).unit.app U) := by
    have h := (adj l E m Y.left AY).unit.naturality pi
    dsimp only [Functor.id_map, Functor.comp_map] at h
    rw [← hred, ← Category.assoc, IsIso.eq_comp_inv]
    simpa only [Category.assoc] using h
  refine ⟨hpi, t, asIso ((adj l E m Y.left AY).unit.app V) ≪≫
    (lim l E m Y.left AY).mapIso t ≪≫ (asIso ((adj l E m Y.left AY).unit.app U)).symm,
    rfl, hpi.symm, ?_, ?_⟩
  · simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, asIso_hom, asIso_inv,
      Category.assoc]
  · intro M' K' v w
    exact exceptionalProjection_bifunctorial l E c v w

end AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent
