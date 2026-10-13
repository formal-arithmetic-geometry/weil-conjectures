# CategoryTheory.Pseudofunctor.overlapPairBaseChangeHom and canonical pair comparisons

## Reason

Move the five existing canonical constructions from
`Sheaf.AlgebraicGeometry.FinitePresentationOverlapPairMapLifting` to
`Sheaf.AlgebraicGeometry.OverlapPairCanonicalComparisons`. The former publicly
imports the latter. The composition lemma stays in its original module. Every fully qualified name,
signature, visibility and construction body is unchanged; only blueprint tags now point to the relocated
construction node. The original target theorem is still declared in the original
module with its exact original signature.

The two new proof-step modules need these definitions. Importing the original
item into either step would create a cycle. Expanding the definitions inline
compiled the lower modules but made the combined proof exceed 60 seconds.
Factoring the shared definitions repairs this cost: the shared module and both
steps compile in seconds, and the item compiles in about seven seconds. No
mathematical statement or definition changed and no arbitrary witnesses are
introduced.

## Old

In `Sheaf.AlgebraicGeometry.FinitePresentationOverlapPairMapLifting`:

```lean
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

```

## New

The following five identical constructions are in
`Sheaf.AlgebraicGeometry.OverlapPairCanonicalComparisons`; the old module has
`public import Sheaf.AlgebraicGeometry.OverlapPairCanonicalComparisons`.

```lean
namespace CategoryTheory.Pseudofunctor

open LocallyDiscreteOpToCat

/-- Pull a universal pair map across a commutative base-change diagram.
This generic formula keeps the composition comparisons independent of concrete sheaf pullbacks.
(blueprint: def-pc-overlap-pair-canonical-comparisons). -/
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
(blueprint: def-pc-overlap-pair-canonical-comparisons). -/
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

/-- The map from an iterated pullback chart to the original limit chart.
It is constructed by the universal property, without choosing a descent witness.
(blueprint: def-pc-overlap-pair-canonical-comparisons). -/
noncomputable def overlapIteratedChartHom {X Y Z : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t) (a : U.I₀) :
    ((U.pullback₁ q).pullback₁ p).X a ⟶ (U.pullback₁ t).X a :=
  pullback.lift (((U.pullback₁ q).pullback₁ p).f a)
    (Scheme.Cover.pullbackHom (U.pullback₁ q) p a ≫ U.pullbackHom q a) (by
      simp only [← h, Category.assoc, Scheme.Cover.pullbackHom_map,
        Scheme.Cover.pullbackHom_map_assoc])

/-- The canonical component comparison on an iterated limit chart.
Source: Stacks Project, Tag 01ZR, first proof, successive restrictions.
(blueprint: def-pc-overlap-pair-canonical-comparisons). -/
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
(blueprint: def-pc-overlap-pair-canonical-comparisons). -/
def overlapPairSquare {X Y : Scheme.{u}} (U : X.OpenCover.{u})
    (N : (a : U.I₀) → (U.X a).Modules) (p : Y ⟶ X)
    (D : modulesPseudofunctor.DescentData (U.pullback₁ p).f)
    (e : ∀ a, (Scheme.Modules.pullback (U.pullbackHom p a)).obj (N a) ≅ D.obj a)
    (a b : U.I₀)
    (φ : (Scheme.Modules.pullback (pullback.fst (U.f a) (U.f b))).obj (N a) ⟶
      (Scheme.Modules.pullback (pullback.snd (U.f a) (U.f b))).obj (N b)) : Prop :=
  modulesPseudofunctor.overlapPairBaseChangeSquare U.f (U.pullback₁ p).f p
    (fun a ↦ U.pullbackHom p a) (fun a ↦ U.pullbackHom_map p a) N D e a b φ

```

## Users

`tools/downstream.py` with all five moved names found the original module and
two downstream modules mentioning them. There are 1,281 transitive importers;
those which do not mention a moved name see the same re-exported interface.
No existing downstream module is adapted or included in this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FinitePresentationOverlapPairMapLifting | S2 | Publicly re-exports the same declarations; its theorem signature is unchanged. |
| Sheaf.AlgebraicGeometry.FinitePresentationOverlapMapLifting | unclaimed | Same limit-map composition lemma and iterated comparison under the same names. No edit needed. |
| Sheaf.AlgebraicGeometry.OverlapPairTransitionsAssembly | unclaimed | Same generic pair hom, square and specialized square under the same names. No edit needed. |
| Sheaf.AlgebraicGeometry.FinitePresentationOverlapPairSingleStage | S2 (new) | Publicly imports the shared constructions used in its statement. |
| Sheaf.AlgebraicGeometry.OverlapPairRefinementPersistence | S2 (new) | Publicly imports the shared constructions used in its statement. |

## Status

landed 20261013T163539-L-1621406 2026-10-13 (merge of deliver/S2/Sheaf.AlgebraicGeometry.FinitePresentationOverlapPairMapLifting)
