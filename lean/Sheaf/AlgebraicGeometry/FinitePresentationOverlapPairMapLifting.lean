/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.AlgebraicGeometry.LocalOverlapTransitions
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.Algebra.FinitePresentationColimit

/-! # Descent of a map on one pairwise overlap

Source: Stacks Project, Tags 01ZR and 05N7.
(blueprint: lem-pc-fp-overlap-pair-map-lifting). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace CategoryTheory.Pseudofunctor

open LocallyDiscreteOpToCat

/-- Pull a universal pair map across a commutative base-change diagram.
This generic formula keeps the composition comparisons independent of concrete sheaf pullbacks.
(blueprint: lem-pc-fp-overlap-pair-map-lifting). -/
noncomputable def overlapPairBaseChangeHom
    {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u + 1})
    {S X₁ X₂ S' X₁' X₂' : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    (p : S' ⟶ S) (p₁ : X₁' ⟶ X₁) (p₂ : X₂' ⟶ X₂)
    (f₁' : X₁' ⟶ S') (f₂' : X₂' ⟶ S')
    (w₁ : p₁ ≫ f₁ = f₁' ≫ p) (w₂ : p₂ ≫ f₂ = f₂' ≫ p)
    (N₁ : F.obj (.mk (op X₁))) (N₂ : F.obj (.mk (op X₂)))
    (φ : (F.map (pullback.fst f₁ f₂).op.toLoc).toFunctor.obj N₁ ⟶
      (F.map (pullback.snd f₁ f₂).op.toLoc).toFunctor.obj N₂) :
    (F.map (pullback.fst f₁' f₂').op.toLoc).toFunctor.obj
        ((F.map p₁.op.toLoc).toFunctor.obj N₁) ⟶
      (F.map (pullback.snd f₁' f₂').op.toLoc).toFunctor.obj
        ((F.map p₂.op.toLoc).toFunctor.obj N₂) :=
  let r₁ := pullback.fst f₁' f₂'
  let r₂ := pullback.snd f₁' f₂'
  let s₁ := r₁ ≫ p₁
  let s₂ := r₂ ≫ p₂
  (F.mapComp p₁.op.toLoc r₁.op.toLoc).inv.toNatTrans.app N₁ ≫
    pullHom φ (pullback.lift s₁ s₂ (by
      dsimp only [s₁, s₂]
      rw [Category.assoc, Category.assoc, w₁, w₂, ← Category.assoc,
        ← Category.assoc, pullback.condition])) s₁ s₂
        (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) ≫
    (F.mapComp p₂.op.toLoc r₂.op.toLoc).hom.toNatTrans.app N₂

/-- The base-change square for one pair, expressed for an arbitrary pseudofunctor.
(blueprint: lem-pc-fp-overlap-pair-map-lifting). -/
def overlapPairBaseChangeSquare
    {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C]
    {ι : Type u} {S S' : C} {X X' : ι → C}
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u + 1})
    (f : ∀ a, X a ⟶ S) (f' : ∀ a, X' a ⟶ S')
    (p : S' ⟶ S) (p' : ∀ a, X' a ⟶ X a)
    (w : ∀ a, p' a ≫ f a = f' a ≫ p)
    (N : ∀ a, F.obj (.mk (op (X a)))) (D : F.DescentData f')
    (e : ∀ a, (F.map (p' a).op.toLoc).toFunctor.obj (N a) ≅ D.obj a)
    (a b : ι)
    (φ : (F.map (pullback.fst (f a) (f b)).op.toLoc).toFunctor.obj (N a) ⟶
      (F.map (pullback.snd (f a) (f b)).op.toLoc).toFunctor.obj (N b)) : Prop :=
  let r₁ := pullback.fst (f' a) (f' b)
  let r₂ := pullback.snd (f' a) (f' b)
  (F.map r₁.op.toLoc).toFunctor.map (e a).hom ≫
      D.hom (r₁ ≫ f' a) r₁ r₂ rfl pullback.condition.symm =
    F.overlapPairBaseChangeHom (f a) (f b) p (p' a) (p' b) (f' a) (f' b)
        (w a) (w b) (N a) (N b) φ ≫
      (F.map r₂.op.toLoc).toFunctor.map (e b).hom

end CategoryTheory.Pseudofunctor

namespace AlgebraicGeometry

/-- The limit map factors through every later stage.
(blueprint: lem-pc-fp-overlap-pair-map-lifting). -/
lemma overlapLimitMap_stage_comp {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cone (R.op ⋙ Scheme.Spec))
    {i j k : I} {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (hij : i ≤ j) (hjk : j ≤ k) :
    overlapLimitMap R c f (hij.trans hjk) ≫ overlapStageMap R f hij hjk =
      overlapLimitMap R c f hij := by
  dsimp only [overlapLimitMap, overlapStageMap]
  rw [← baseChangeMap_comp]
  congr 1
  ext
  simpa using c.w (homOfLE hjk).op

/-- The map from an iterated pullback chart to the original limit chart.
It is constructed by the universal property, without choosing a descent witness.
(blueprint: lem-pc-fp-overlap-pair-map-lifting). -/
noncomputable def overlapIteratedChartHom {X Y Z : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t) (a : U.I₀) :
    ((U.pullback₁ q).pullback₁ p).X a ⟶ (U.pullback₁ t).X a :=
  pullback.lift (((U.pullback₁ q).pullback₁ p).f a)
    (Scheme.Cover.pullbackHom (U.pullback₁ q) p a ≫ U.pullbackHom q a) (by
      simp only [← h, Category.assoc, Scheme.Cover.pullbackHom_map,
        Scheme.Cover.pullbackHom_map_assoc])

/-- The canonical component comparison on an iterated limit chart.
Source: Stacks Project, Tag 01ZR, first proof, successive restrictions.
(blueprint: lem-pc-fp-overlap-pair-map-lifting). -/
noncomputable def overlapIteratedComparison {X Y Z : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (a : U.I₀) → (U.X a).Modules) (M : Z.Modules)
    (e : ∀ a, (Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a) ≅
      (Scheme.Modules.pullback ((U.pullback₁ t).f a)).obj M) (a : U.I₀) :
    (Scheme.Modules.pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p a)).obj
        ((Scheme.Modules.pullback (U.pullbackHom q a)).obj (N a)) ≅
      (Scheme.Modules.pullback (((U.pullback₁ q).pullback₁ p).f a)).obj M := by
  let V : Y.OpenCover.{u} := U.pullback₁ q
  let W : Z.OpenCover.{u} := V.pullback₁ p
  let d := overlapIteratedChartHom U q p t h a
  have hdq : d ≫ U.pullbackHom t a = V.pullbackHom p a ≫ U.pullbackHom q a :=
    pullback.lift_snd _ _ _
  have hdf : d ≫ (U.pullback₁ t).f a = W.f a := pullback.lift_fst _ _ _
  exact (Scheme.Modules.pullbackComp (V.pullbackHom p a) (U.pullbackHom q a)).app
      (N a) ≪≫
    (Scheme.Modules.pullbackCongr hdq.symm).app (N a) ≪≫
    ((Scheme.Modules.pullbackComp d (U.pullbackHom t a)).app (N a)).symm ≪≫
    (Scheme.Modules.pullback d).mapIso (e a) ≪≫
    (Scheme.Modules.pullbackComp d ((U.pullback₁ t).f a)).app M ≪≫
    (Scheme.Modules.pullbackCongr hdf).app M

/-- The compatibility square on one universal limit overlap.
Its generic formula avoids expanding concrete module pullbacks during elaboration.
(blueprint: lem-pc-fp-overlap-pair-map-lifting). -/
def overlapPairSquare {X Y : Scheme.{u}} (U : X.OpenCover.{u})
    (N : (a : U.I₀) → (U.X a).Modules) (p : Y ⟶ X)
    (D : modulesPseudofunctor.DescentData (U.pullback₁ p).f)
    (e : ∀ a, (Scheme.Modules.pullback (U.pullbackHom p a)).obj (N a) ≅ D.obj a)
    (a b : U.I₀)
    (φ : (Scheme.Modules.pullback (pullback.fst (U.f a) (U.f b))).obj (N a) ⟶
      (Scheme.Modules.pullback (pullback.snd (U.f a) (U.f b))).obj (N b)) : Prop :=
  modulesPseudofunctor.overlapPairBaseChangeSquare U.f (U.pullback₁ p).f p
    (fun a ↦ U.pullbackHom p a) (fun a ↦ U.pullbackHom_map p a) N D e a b φ

/-- Descend the conjugated transition on one pairwise overlap, with persistence at later stages.
Source: Stacks Project, Tag 01ZR, first proof (Zariski gluing), and Tag 05N7 (2), (3).
(blueprint: lem-pc-fp-overlap-pair-map-lifting).

Proof: The overlap of the two fixed affine charts is quasi-compact because the ambient
scheme is quasi-separated. Cover it by finitely many affine opens, and cover their
pairwise intersections by finitely many affine opens. The restrictions of N a and N b
are finitely presented and quasi-coherent. Conjugate the restriction map of M by e a
and e b. On each affine chart, the limit ring is the directed colimit of the stage
rings and module pullback is extension of scalars. Apply Tag 05N7 (2) to lift the map
on each chart. Apply (3) on the finite refinement intersections to make the local
maps agree at a common later stage. Glue to a map on the entire pairwise overlap.
Its limit pullback is the prescribed map by construction and the sheaf condition.
Pull this map back to every subsequent stage. Pullback composition and the canonical
iterated comparisons give the displayed square there. This argument concerns just
one pair: it asserts neither a common stage for all pairs nor natural overlap
transitions on arbitrary test schemes. If the overlap is empty its unique map works.
For a preorder use the partial-order quotient of the nonempty tail above j. -/
theorem exists_finitePresentation_overlap_pair_map_lifting
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    [Finite U.I₀] [∀ a, IsAffine (U.X a)]
    (N : (a : U.I₀) → (U.X a).Modules)
    (hN : ∀ a, (N a).IsFinitePresentation) (hNq : ∀ a, (N a).IsQuasicoherent)
    (M : (pullback f (c.π.app (op i))).Modules)
    (e : ∀ a, (Scheme.Modules.pullback (U.pullbackHom
      (baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))) a)).obj (N a) ≅
      (Scheme.Modules.pullback ((U.pullback₁ (baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)))).f a)).obj M)
    (a b : U.I₀) :
    ∃ (k : I) (hjk : j ≤ k), ∀ (l : I) (hjl : j ≤ l), k ≤ l →
      let q := overlapStageMap R f hij hjl
      let V := U.pullback₁ q
      let p := overlapLimitMap R c f (hij.trans hjl)
      let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
      let W := V.pullback₁ p
      let D := (modulesPseudofunctor.toDescentData W.f).obj M
      let ε := overlapIteratedComparison U q p (overlapLimitMap R c f hij)
        (overlapLimitMap_stage_comp R c f hij hjl) N M e
      ∃ φ : (Scheme.Modules.pullback (pullback.fst (V.f a) (V.f b))).obj (A a) ⟶
          (Scheme.Modules.pullback (pullback.snd (V.f a) (V.f b))).obj (A b),
        overlapPairSquare V A p D ε a b φ := by sorry

end AlgebraicGeometry
