/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleCofinalBlockFactorization

/-! # Evaluation of the normalized cofinal support comparison

Source: Zheng, Construction 4.1 and the paragraph preceding Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] AlgebraicGeometry.Etale.SystemProjection.CofinalRepeatSupport.kappa
  WeilConjectures.SemilinearSections.systemRing WeilConjectures.SemilinearSections.ringPresheaf
  WeilConjectures.SemilinearSections.rings
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- Evaluation of the support square follows from its factorization normalization and
coefficient-projection evaluation. This asserts an equality of evaluated morphisms;
it does not use faithfulness of evaluation on derived categories.
Source: Zheng, Construction 4.1 and paragraph preceding Lemma 4.10, printed pp. 21--23
(blueprint: lem-pur-etale-cofinal-support-evaluation).

Proof: solve the normalization equation for h by composing with the inverse coefficient
projection and the inverse factorization comparisons. Evaluate this word at m. Substitute
data.factorX and data.factorY to identify the evaluated factorization words with the
recorded selected-extension level comparisons. Use naturality of scalar evaluation to
move past R.kappa, and then use data.support for the repeated compact-support square.
The remaining coefficient square is exactly the assumed projection evaluation formula
for D_m→B_m; naturality moves the repeated-evaluation isomorphisms past its scalar map.
Cancel the adjacent evaluation and factorization isomorphisms. The remaining word is
the displayed selected-extension/support equation. This is a diagram calculation from
three explicitly recorded evaluation diagrams, not an inference from faithfulness of
level evaluation. It does not demand literal section identities for arbitrary choices
of open-adjoint data. Repeated least indices and nonflat coefficients are allowed. -/
theorem etaleCofinalSupport_evaluation
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (T : Theory c l) (B : Coefficients.{u} l) (r : ℕ ↪o ℕ)
    (Lx : CofinalExtension X B r) (Ly : CofinalExtension Y B r)
    (R : CofinalRepeatSupport T B r)
    (Fx : CofinalFactor X B r Lx R.x (T.scalarX (cofinalCoefficient B r)))
    (Fy : CofinalFactor Y B r Ly R.y (T.scalarY (cofinalCoefficient B r)))
    (data : CofinalBlockEvaluation T B r Lx Ly R Fx Fy)
    [IsIso (T.q (cofinalCoefficient B r))]
    (hq : ∀ (m : ℕ) (M : Derived X (cofinalRepeated B r).rings),
      (scalarExtension ((cofinalCoefficient B r).app (op m)).hom Y).map
          ((T.supportEvaluation (cofinalRepeated B r) m).iso.inv.app M) ≫
        (T.scalarEvaluationY (cofinalCoefficient B r) m).iso.inv.app
          ((T.support (cofinalRepeated B r)).F.obj M) ≫
        (T.evaluationY B m).E.map ((T.q (cofinalCoefficient B r)).app M) ≫
        (T.supportEvaluation B m).iso.hom.app
          ((T.scalarX (cofinalCoefficient B r)).model.T.obj M) ≫
        (rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (B.rings.obj (op m))) c).map
            ((T.scalarEvaluationX (cofinalCoefficient B r) m).iso.hom.app M) =
        (compactScalarMap ((cofinalCoefficient B r).app (op m)).hom c).app
          ((T.evaluationX (cofinalRepeated B r) m).E.obj M))
    (h : Lx.model.derived ⋙ (T.support B).F ≅
      (T.support (cofinalCoefficients B r)).F ⋙ Ly.model.derived)
    (hn : ∀ N : Derived X (cofinalCoefficients B r).rings,
      (T.q (cofinalCoefficient B r)).app (R.x.R.mapDerivedCategory.obj N) ≫
        (T.support B).F.map (Fx.derived.inv.app N) ≫ h.hom.app N ≫
        Fy.derived.hom.app ((T.support (cofinalCoefficients B r)).F.obj N) =
      (T.scalarY (cofinalCoefficient B r)).model.T.map (R.kappa.hom.app N)) :
  ∀ (m : ℕ) (N : Derived X (cofinalCoefficients B r).rings),
    ((T.evaluationY B m).E).map (h.hom.app N) ≫
      (Ly.level m (T.evaluationY B m)
        (T.evaluationY (cofinalCoefficients B r)
          (SheafOfModules.systemNextSelected r m))).hom.app
            ((T.support (cofinalCoefficients B r)).F.obj N) ≫
      (scalarExtension
        (B.rings.map (homOfLE (SheafOfModules.systemNextSelected_spec r m).1).op).hom Y).map
          ((T.supportEvaluation (cofinalCoefficients B r)
            (SheafOfModules.systemNextSelected r m)).iso.hom.app N) ≫
      (compactScalarMap
        (B.rings.map (homOfLE (SheafOfModules.systemNextSelected_spec r m).1).op).hom c).app
          ((T.evaluationX (cofinalCoefficients B r)
            (SheafOfModules.systemNextSelected r m)).E.obj N) =
    (T.supportEvaluation B m).iso.hom.app
      (Lx.model.derived.obj N) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (B.rings.obj (op m))) c).map
        ((Lx.level m (T.evaluationX B m)
          (T.evaluationX (cofinalCoefficients B r)
            (SheafOfModules.systemNextSelected r m))).hom.app N) := by
  intro m N
  let a := cofinalCoefficient B r
  let M := R.x.R.mapDerivedCategory.obj N
  let P := (T.support (cofinalCoefficients B r)).F.obj N
  let ex := (T.evaluationX B m).E
  let ey := (T.evaluationY B m).E
  let gx := scalarExtension (a.app (op m)).hom X
  let gy := scalarExtension (a.app (op m)).hom Y
  let f1 := rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (B.rings.obj (op m))) c
  let f0 := rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} ((cofinalRepeated B r).rings.obj (op m))) c
  let dX := (T.scalarEvaluationX a m).iso
  let dY := (T.scalarEvaluationY a m).iso
  let sB := (T.supportEvaluation B m).iso
  let sD := (T.supportEvaluation (cofinalRepeated B r) m).iso
  let sC := (T.supportEvaluation (cofinalCoefficients B r)
    (SheafOfModules.systemNextSelected r m)).iso
  let lx := Lx.level m (T.evaluationX B m)
    (T.evaluationX (cofinalCoefficients B r) (SheafOfModules.systemNextSelected r m))
  let cx := data.x m
  let cy := data.y m
  let q0 := compactScalarMap (a.app (op m)).hom c
  have hnE :
      ey.map ((T.q a).app M) ≫ ey.map ((T.support B).F.map (Fx.derived.inv.app N)) ≫
        ey.map (h.hom.app N) ≫ ey.map (Fy.derived.hom.app P) =
      ey.map ((T.scalarY a).model.T.map (R.kappa.hom.app N)) := by
    simpa only [CategoryTheory.Functor.map_comp] using congrArg ey.map (hn N)
  have hx0 : ex.map (Fx.derived.inv.app N) ≫ lx.hom.app N =
      dX.hom.app M ≫ gx.map (cx.hom.app N) := by
    rw [← data.factorX m N]
    rw [← ex.map_comp_assoc, Fx.derived.inv_hom_id_app]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  have hx : f1.map (ex.map (Fx.derived.inv.app N)) ≫ f1.map (lx.hom.app N) =
      f1.map (dX.hom.app M) ≫ f1.map (gx.map (cx.hom.app N)) := by
    simpa only [CategoryTheory.Functor.map_comp] using congrArg f1.map hx0
  have hnatY := dY.hom.naturality (R.kappa.hom.app N)
  have hnatB := sB.hom.naturality (Fx.derived.inv.app N)
  have hnatQ := q0.naturality (cx.hom.app N)
  change ey.map ((T.scalarY a).model.T.map (R.kappa.hom.app N)) ≫
      dY.hom.app (R.y.R.mapDerivedCategory.obj P) =
    dY.hom.app ((T.support (cofinalRepeated B r)).F.obj M) ≫
      gy.map ((T.evaluationY (cofinalRepeated B r) m).E.map (R.kappa.hom.app N)) at hnatY
  change ey.map ((T.support B).F.map (Fx.derived.inv.app N)) ≫
      sB.hom.app (Lx.model.derived.obj N) =
    sB.hom.app ((T.scalarX a).model.T.obj M) ≫
      f1.map (ex.map (Fx.derived.inv.app N)) at hnatB
  change gy.map (f0.map (cx.hom.app N)) ≫
      q0.app ((T.evaluationX (cofinalCoefficients B r)
        (SheafOfModules.systemNextSelected r m)).E.obj N) =
    q0.app ((T.evaluationX (cofinalRepeated B r) m).E.obj M) ≫
      f1.map (gx.map (cx.hom.app N)) at hnatQ
  have hrep :
      gy.map ((T.evaluationY (cofinalRepeated B r) m).E.map (R.kappa.hom.app N)) ≫
        gy.map (cy.hom.app P) ≫ gy.map (sC.hom.app N) =
      gy.map (sD.hom.app M) ≫ gy.map (f0.map (cx.hom.app N)) := by
    simpa only [CategoryTheory.Functor.map_comp] using congrArg gy.map (data.support m N)
  have hproj : ey.map ((T.q a).app M) ≫ sB.hom.app ((T.scalarX a).model.T.obj M) ≫
      f1.map (dX.hom.app M) =
      dY.hom.app ((T.support (cofinalRepeated B r)).F.obj M) ≫
        gy.map (sD.hom.app M) ≫ q0.app ((T.evaluationX (cofinalRepeated B r) m).E.obj M) := by
    have hp := congrArg (fun z ↦
      dY.hom.app ((T.support (cofinalRepeated B r)).F.obj M) ≫
        gy.map (sD.hom.app M) ≫ z) (hq m M)
    change dY.hom.app ((T.support (cofinalRepeated B r)).F.obj M) ≫
        gy.map (sD.hom.app M) ≫ gy.map (sD.inv.app M) ≫
        dY.inv.app ((T.support (cofinalRepeated B r)).F.obj M) ≫
        ey.map ((T.q a).app M) ≫ sB.hom.app ((T.scalarX a).model.T.obj M) ≫
        f1.map (dX.hom.app M) =
      dY.hom.app ((T.support (cofinalRepeated B r)).F.obj M) ≫
        gy.map (sD.hom.app M) ≫ q0.app
          ((T.evaluationX (cofinalRepeated B r) m).E.obj M) at hp
    simp only [← gy.map_comp_assoc, Iso.hom_inv_id_app] at hp
    rw [gy.map_id (((T.support (cofinalRepeated B r)).F ⋙
      (T.evaluationY (cofinalRepeated B r) m).E).obj M)] at hp
    simpa only [Functor.comp_obj, Category.id_comp, Iso.hom_inv_id_app_assoc] using hp
  let p := ey.map ((T.q a).app M) ≫ ey.map ((T.support B).F.map (Fx.derived.inv.app N))
  have : IsIso p := by
    dsimp only [p]
    infer_instance
  change ey.map (h.hom.app N) ≫
      (Ly.level m (T.evaluationY B m)
        (T.evaluationY (cofinalCoefficients B r)
          (SheafOfModules.systemNextSelected r m))).hom.app P ≫
      gy.map (sC.hom.app N) ≫
      q0.app ((T.evaluationX (cofinalCoefficients B r)
        (SheafOfModules.systemNextSelected r m)).E.obj N) =
    sB.hom.app (Lx.model.derived.obj N) ≫ f1.map (lx.hom.app N)
  apply (cancel_epi p).1
  rw [← data.factorY m P]
  simp only [Category.assoc]
  change p ≫ (ey.map (h.hom.app N) ≫ ey.map (Fy.derived.hom.app P) ≫
      dY.hom.app (R.y.R.mapDerivedCategory.obj P) ≫ gy.map (cy.hom.app P) ≫
      gy.map (sC.hom.app N) ≫
      q0.app ((T.evaluationX (cofinalCoefficients B r)
        (SheafOfModules.systemNextSelected r m)).E.obj N)) =
    p ≫ (sB.hom.app (Lx.model.derived.obj N) ≫ f1.map (lx.hom.app N))
  simp only [p, Category.assoc]
  rw [reassoc_of% hnE, reassoc_of% hnatB, hx, reassoc_of% hproj,
    ← hnatQ, ← reassoc_of% hrep, ← reassoc_of% hnatY]

end AlgebraicGeometry.Etale.SystemProjection
