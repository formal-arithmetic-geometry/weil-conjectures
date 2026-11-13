/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.AdjoinRoot

import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedRootBaseChange
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Auxiliary limit statements for punctured root charts
Source: Stacks Project, Tags 0BSK, 05N9 and 01YW. -/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Pulling a limit of affine schemes back along a fixed affine scheme preserves the
limit and its structural maps. -/
private theorem affine_pullback_limit
    {I : Type u} [Category.{u} I] [IsConnected I]
    {B V : Scheme.{u}} [IsAffine B] [IsAffine V] (k : V ⟶ B)
    (E : I ⥤ Scheme.{u}) (s : E ⟶ (Functor.const I).obj B)
    (cE : Cone E) (hcE : IsLimit cE) (b : cE.pt ⟶ B)
    (hlegs : ∀ j, cE.π.app j ≫ s.app j = b) (hE : ∀ j, IsAffine (E.obj j)) :
    ∃ (D : I ⥤ Scheme.{u}) (c : Cone D) (t : D ⟶ (Functor.const I).obj B),
      Nonempty (IsLimit c) ∧ (∀ j, IsAffine (D.obj j)) ∧
      ∃ e : pullback b k ≅ c.pt,
        (∀ j, e.hom ≫ c.π.app j ≫ t.app j = pullback.fst b k ≫ b) ∧
        ∀ j, ∃ d : pullback (s.app j) k ≅ D.obj j,
          d.hom ≫ t.app j = pullback.fst (s.app j) k ≫ s.app j := by
  let L : I ⥤ Over B := Over.lift E s
  let cL : Cone L := Over.liftCone E s cE b hlegs
  have hcL : IsLimit cL := Over.isLimitLiftCone E s cE b hlegs hcE
  let P := Over.pullback k
  let D : I ⥤ Scheme.{u} := L ⋙ P ⋙ Over.forget V
  let c : Cone D := (P ⋙ Over.forget V).mapCone cL
  have hc : IsLimit c := isLimitOfPreserves (P ⋙ Over.forget V) hcL
  let t : D ⟶ (Functor.const I).obj B :=
    { app := fun j => pullback.fst (s.app j) k ≫ s.app j
      naturality := by
        intro i j h
        change pullback.lift (pullback.fst (s.app i) k ≫ E.map h)
          (pullback.snd (s.app i) k) _ ≫
          (pullback.fst (s.app j) k ≫ s.app j) =
          (pullback.fst (s.app i) k ≫ s.app i) ≫ 𝟙 _
        simp only [Category.assoc, pullback.lift_fst_assoc, Category.comp_id]
        have hs := s.naturality h
        have hs' : E.map h ≫ s.app j = s.app i := by
          change E.map h ≫ s.app j = s.app i ≫ 𝟙 B at hs
          exact hs.trans (Category.comp_id _)
        rw [hs'] }
  refine ⟨D, c, t, ⟨hc⟩, ?_, Iso.refl _, ?_, ?_⟩
  · intro j
    have : IsAffine (E.obj j) := hE j
    exact Pullback.isAffine_of_isAffine_isAffine_isAffine
      (show E.obj j ⟶ B from s.app j) k
  · intro j
    change 𝟙 _ ≫
      pullback.lift (pullback.fst b k ≫ cE.π.app j) (pullback.snd b k) _ ≫
        (pullback.fst (s.app j) k ≫ s.app j) = _
    simp only [Category.id_comp, pullback.lift_fst_assoc, Category.assoc, hlegs]
  · intro j
    exact ⟨Iso.refl _, Category.id_comp _⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option trace.profiler true in
/-- Punctured root charts commute with cofiltered affine ring colimits over R.

Source: Stacks Project, Tags 05N9 and 01YW; universal properties of polynomial
quotients and localization.
(blueprint: lem-sbc-punctured-root-colimit-continuity)

Proof: First identify every punctured root chart with the base change of the
chart V₀ over R, using punctured_root_base_change. Apply Spec to the ring colimit
cocone, and extend the resulting limit cone along Spec(e₀) to put its point at
Spec H. The hypothesis ha identifies every composite of a cone leg and its base
map with Spec b. Lift this cone to schemes over Spec R. Pullback along the fixed
map V₀ to Spec R is a right adjoint, so it preserves this limit. The forgetful
functor from schemes over V₀ preserves connected limits; cofilteredness supplies
connectedness. This gives a limit in schemes of the pullback diagram. Its objects
are affine pullbacks of affine schemes over Spec R, since V₀ is a basic affine open.
The base-change comparison at H identifies its cone point with the required chart;
the comparisons at the stages give the required stage isomorphisms. Their projection
formulas, the pullback leg equations and ha give both structural-map equations.
No positivity or regularity is used: polynomial quotient base change and inverse
images of basic opens also work for n=0, f=0, and zero rings. -/
theorem punctured_root_colimit_continuity
    (R H : CommRingCat.{u}) (f : R) (n : ℕ) (b : R ⟶ H)
    (I : Type u) [Category.{u} I] [IsCofiltered I]
    (F : Iᵒᵖ ⥤ CommRingCat.{u}) (c₀ : Cocone F) (hc₀ : IsColimit c₀)
    (a : (Functor.const Iᵒᵖ).obj R ⟶ F) (e₀ : c₀.pt ≅ H)
    (ha : ∀ j, a.app j ≫ c₀.ι.app j ≫ e₀.hom = b) :
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ∃ (D : I ⥤ Scheme.{u}) (c : Cone D)
      (t : D ⟶ (Functor.const I).obj (Spec R)),
      Nonempty (IsLimit c) ∧ (∀ j, IsAffine (D.obj j)) ∧
      ∃ e : V.toScheme ≅ c.pt,
        (∀ j, e.hom ≫ c.π.app j ≫ t.app j = V.ι ≫ q ≫ Spec.map b) ∧
        ∀ j,
          let S := F.obj (Opposite.op j)
          let g := (a.app (Opposite.op j)).hom f
          let A := AdjoinRoot ((Polynomial.X : Polynomial S) ^ n - Polynomial.C g)
          let N := Spec (CommRingCat.of A)
          let q := Spec.map (CommRingCat.ofHom (algebraMap S A))
          let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap S A g)
          ∃ d : V.toScheme ≅ D.obj j,
            d.hom ≫ t.app j = V.ι ≫ q ≫ Spec.map (a.app (Opposite.op j)) := by
  run_tac Lean.logInfo "PH701: proof started"
  classical
  dsimp only
  have : IsConnected I := IsCofiltered.isConnected I
  let A₀ := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f)
  let N₀ := Spec (CommRingCat.of A₀)
  let q₀ := Spec.map (CommRingCat.ofHom (algebraMap R A₀))
  let V₀ : N₀.Opens := PrimeSpectrum.basicOpen (algebraMap R A₀ f)
  let k := V₀.ι ≫ q₀
  let E := F.rightOp ⋙ Scheme.Spec
  run_tac Lean.logInfo "PH701: diagram defined"
  let s : E ⟶ (Functor.const I).obj (Spec R) :=
    { app := fun j => Spec.map (a.app (Opposite.op j))
      naturality := by
        intro i j h
        dsimp [E]
        rw [← Spec.map_comp]
        congr 1
        simpa using (a.naturality h.op).symm }
  run_tac Lean.logInfo "PH701: natural transformation defined"
  let cE : Cone E := Scheme.Spec.mapCone (coneRightOpOfCocone c₀)
  have hcE : IsLimit cE := isLimitOfPreserves Scheme.Spec
    (isLimitConeRightOpOfCocone F hc₀)
  let cH : Cone E := cE.extend (Spec.map e₀.hom)
  have hcH : IsLimit cH := hcE.extendIso (Spec.map e₀.hom)
  run_tac Lean.logInfo "PH701: limit transported"
  have hlegs : ∀ j, cH.π.app j ≫ s.app j = Spec.map b := by
    intro j
    change Spec.map e₀.hom ≫ Spec.map (c₀.ι.app (Opposite.op j)) ≫
      Spec.map (a.app (Opposite.op j)) = Spec.map b
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    simpa only [Category.assoc] using ha (Opposite.op j)
  have hV₀ : IsAffine V₀.toScheme := IsAffineOpen.Spec_basicOpen _
  have hE : ∀ j, IsAffine (E.obj j) := fun j ↦ inferInstance
  run_tac Lean.logInfo "PH701: start pullback limit"
  obtain ⟨D, c, t, hc, hD, eD, heD, hstage⟩ :=
    affine_pullback_limit k E s cH hcH (Spec.map b) hlegs hE
  run_tac Lean.logInfo "PH701: start root base change"
  obtain ⟨e, he⟩ := punctured_root_base_change R H f n b
  run_tac Lean.logInfo "PH701: start packaging"
  refine ⟨D, ?_⟩
  run_tac Lean.logInfo "PH701: diagram packaged"
  refine ⟨c, t, hc, hD, ?_⟩
  run_tac Lean.logInfo "PH701: cone packaged"
  refine ⟨e ≪≫ eD, ?_, ?_⟩
  · intro j
    rw [Iso.trans_hom, Category.assoc, heD, ← Category.assoc, he]
    simp only [Category.assoc]
  · intro j
    obtain ⟨d, hd⟩ := punctured_root_base_change R (F.obj (Opposite.op j)) f n
      (a.app (Opposite.op j))
    obtain ⟨dD, hdD⟩ := hstage j
    refine ⟨d ≪≫ dD, ?_⟩
    rw [Iso.trans_hom, Category.assoc, hdD, ← Category.assoc, hd]
    simp only [Category.assoc]
    rfl

end AlgebraicGeometry.Scheme
