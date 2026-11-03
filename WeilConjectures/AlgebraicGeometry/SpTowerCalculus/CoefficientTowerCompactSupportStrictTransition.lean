/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerIntrinsicTransitions
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerRealizationTransition
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerGenericCompactSupportTransition

/-! # Strict transitions in intrinsic coefficient coordinates

Source: Zheng, Construction 4.1; Stacks 07A6; the first step of the
coefficient-tower transition compatibility argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerCalculus

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

private theorem cancelIsoSquare
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {P P' : D} {Q Q' : C} (i : P ≅ P') (j : Q ≅ Q')
    (a : P ⟶ R.obj Q) (t : P' ⟶ R.obj Q')
    (h : a ≫ R.map j.hom = i.hom ≫ t) :
    i.hom ≫ t ≫ R.map j.inv = a := by
  rw [← reassoc_of% h, ← R.map_comp, j.hom_inv_id, R.map_id, Category.comp_id]

private theorem pasteRestrictionSquare
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    (fn : C ⥤ D) (fm : C' ⥤ D') (rx : C' ⥤ C) (ry : D' ⥤ D)
    (d : rx ⋙ fn ⟶ fm ⋙ ry)
    {A A' : C} {B B' : C'} (g : A ⟶ rx.obj B) (t : A' ⟶ rx.obj B')
    (a : A ⟶ A') (b : B ⟶ B') (h : g ≫ rx.map b = a ≫ t) :
    fn.map g ≫ d.app B ≫ ry.map (fm.map b) =
      fn.map a ≫ fn.map t ≫ d.app B' := by
  have hd := d.naturality b
  dsimp only [Functor.comp_map] at hd
  rw [← hd, ← fn.map_comp_assoc, h, fn.map_comp, Category.assoc]

/-- The strict output transition evaluated at compact support is the pasted proper/open
restriction transition. This statement uses the recorded intrinsic adjoints and contains
no scalar-extension comparison. Their strict-transition identification is supplied by realization.
Source: Zheng 4.1 and 4.10; Stacks 0D6D and 0D6E; blueprint Levels paragraph.
Proof: in the section-preserving realization, the direct-image transition formula is
finite direct image of the input transition followed by its restriction comparison.
Exact open extension sends a structural summand containing x to the same summand
containing its transition. The open adjunction unit and its evaluation normalization
identify this with the published open restriction comparison. Localize this termwise
square and paste it with the proper square. The compact-support restriction comparison
is their specified composite. Expand Evaluation.normalization, use transition naturality
at the realization counit, and cancel the inverse level comparisons. This gives the
displayed identity for every ambient derived tower, including noninvertible transitions.
(blueprint: lem-sp-tower-compact-support-strict-transition). -/
theorem compactSupport_intrinsicTransition
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (e : ∀ n : ℕ, Evaluation l E b o q c n)
    (K : spDerivedCoefficientTowers l E X (q.abelian X))
    {m n : ℕ} (v : m ≤ n) :
    intrinsicTransition l E Y (q.abelian Y) v (q.scalar Y v) ((F l E b o q c).obj K) ≫
        (scalarRestriction (quotient l E v) Y).map ((e m).comparison.hom.app K) =
      (e n).comparison.hom.app K ≫
        (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).map
          (intrinsicTransition l E X (q.abelian X) v (q.scalar X v) K) ≫
        (intrinsicCompactSupportRestriction (quotient l E v) c.i c.g).hom.app
          ((spDerivedCoefficientEvaluation l E X (q.abelian X) m).obj K) := by
  let ex := realization l E b X (q.abelian X)
  let ey := realization l E b Y (q.abelian Y)
  let M := (SpTowerShriek.F l E b o c).obj (ex.functor.obj K)
  let FK := (F l E b o q c).obj K
  let cy := ey.counitIso.hom.app M
  have hx := realization_intrinsicTransition l E b q X K v
  have hy := realization_intrinsicTransition l E b q Y FK v
  have hg := generic_compactSupport_intrinsicTransition l E b o c (ex.functor.obj K) v
  have hn := (genericIntrinsicTransitions l E Y v).naturality cy
  dsimp only [Functor.comp_map] at hn
  rw [(e n).normalization, (e m).normalization]
  apply (cancel_epi ((levelComparison l E b q Y n).hom.app FK)).1
  simp only [Functor.map_comp, Category.assoc]
  rw [Iso.hom_inv_id_app_assoc]
  have hy' : (levelComparison l E b q Y n).hom.app FK ≫
      intrinsicTransition l E Y (q.abelian Y) v (q.scalar Y v) FK ≫
      (scalarRestriction (quotient l E v) Y).map
        ((levelComparison l E b q Y m).inv.app FK) =
      (genericIntrinsicTransitions l E Y v).app (ey.functor.obj FK) := by
    exact cancelIsoSquare (scalarRestriction (quotient l E v) Y)
      ((levelComparison l E b q Y n).app FK) ((levelComparison l E b q Y m).app FK)
      _ _ hy
  rw [reassoc_of% hy']
  dsimp only [FK, F, compactSupport, Functor.comp_obj]
  erw [← reassoc_of% hn, reassoc_of% hg]
  have ht := pasteRestrictionSquare
    (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g)
    (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g)
    (scalarRestriction (quotient l E v) X) (scalarRestriction (quotient l E v) Y)
    (intrinsicCompactSupportRestriction (quotient l E v) c.i c.g).hom
    _ _ _ _ hx
  exact congrArg (fun t ↦ (SpTowerShriek.Ev l E Y n).map cy ≫
    (SpTowerShriek.Fcomparison l E b o c n).hom.app (ex.functor.obj K) ≫ t) ht

end AlgebraicGeometry.ProEtale.SpTowerCalculus
