# AlgebraicGeometry.overlapModelLimitComparison and model transport comparisons

## Reason

The former complete proof exceeded the single-file time limit while matching expanded
inverse-image composites. Extract explicit reusable canonical constructors, keep their
bodies folded, and specialize them in the existing definitions. The tensor comparison
uses the same chosen adjunction as before; its theorem pins the unit and is proved.
No arbitrary witness of an unproved existence theorem or holed data is introduced.
Every existing declaration type and visibility stays identical. The bodies expand to
the old composites, up to proof irrelevance for projection equations. The local
transparency commands do not export changes to Mathlib. No target signature or
mathematical hypothesis changes. A target using a changed definition needs its
statement/definition review reopened under AGENTS.md section 4, confirming these
same canonical composites.

## Old

```lean
def overlapTensorComparison {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Scheme.Modules.tensorPullback p ≅ Scheme.Modules.pullback p :=
  Adjunction.leftAdjointUniq
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p))
    (Scheme.Modules.pullbackPushforwardAdjunction p)

variable {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u})
  (c : Cone (R.op ⋙ Scheme.Spec)) {i : I} {Xi : Scheme.{u}}
  (f : Xi ⟶ Spec (R.obj i)) {j : I} (hij : i ≤ j)
  (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
  (a b : U.I₀)

def overlapModelLimitComparison
    (N : (d : U.I₀) → (U.X d).Modules) (d : U.I₀)
    (r : pullback (U.f a) (U.f b) ⟶ U.X d)
    (hr : r ≫ U.f d = pullback.fst (U.f a) (U.f b) ≫ U.f a) :
    (Scheme.Modules.tensorPullback (overlapLimitMap R c
      (overlapModelHom R f hij U a b) (le_refl j))).obj
      ((Scheme.Modules.pullback (overlapModelChart R f hij U a b d r)).obj (N d)) ≅
    (Scheme.Modules.pullback (overlapModelLimitChart R c f hij U a b d r hr)).obj
      ((Scheme.Modules.pullback (U.pullbackHom (overlapLimitMap R c f hij) d)).obj
        (N d)) :=
  (overlapTensorComparison _).app _ ≪≫
    (pullbackCompOfEq _ _ (pullback.fst _ _ ≫ r)
      (by
        dsimp only [overlapLimitMap, overlapModelChart, baseChangeMap, pullback.map,
          Over.mk_hom, Over.homMk_left]
        simp only [← Category.assoc, pullback.lift_fst, Category.comp_id])
      (N d)) ≪≫
    (pullbackCompOfEq _ _ (pullback.fst _ _ ≫ r)
      (by exact pullback.lift_snd _ _ _) (N d)).symm

def overlapModelConjugate
    (N : (d : U.I₀) → (U.X d).Modules)
    (M : (pullback f (c.π.app (op i))).Modules)
    (e : ∀ d, (Scheme.Modules.pullback
      (U.pullbackHom (overlapLimitMap R c f hij) d)).obj (N d) ≅
      (Scheme.Modules.pullback ((U.pullback₁ (overlapLimitMap R c f hij)).f d)).obj M) :
    (Scheme.Modules.tensorPullback (overlapLimitMap R c
      (overlapModelHom R f hij U a b) (le_refl j))).obj
      ((Scheme.Modules.pullback (overlapModelChart R f hij U a b a
        (pullback.fst (U.f a) (U.f b)))).obj (N a)) ⟶
    (Scheme.Modules.tensorPullback (overlapLimitMap R c
      (overlapModelHom R f hij U a b) (le_refl j))).obj
      ((Scheme.Modules.pullback (overlapModelChart R f hij U a b b
        (pullback.snd (U.f a) (U.f b)))).obj (N b)) := by
  let ra := pullback.fst (U.f a) (U.f b)
  let rb := pullback.snd (U.f a) (U.f b)
  let ha := overlapModelLimitChart R c f hij U a b a ra rfl
  let hb := overlapModelLimitChart R c f hij U a b b rb pullback.condition.symm
  let ta := overlapModelLimitComparison R c f hij U a b N a ra rfl
  let tb := overlapModelLimitComparison R c f hij U a b N b rb pullback.condition.symm
  let W := U.pullback₁ (overlapLimitMap R c f hij)
  let D := (modulesPseudofunctor.toDescentData W.f).obj M
  exact ta.hom ≫ (Scheme.Modules.pullback ha).map (e a).hom ≫
    D.hom (overlapModelLimitToBase R c f hij U a b) ha hb
      (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) ≫
    (Scheme.Modules.pullback hb).map (e b).inv ≫ tb.inv

def overlapModelStageComparison {k : I} (hjk : j ≤ k)
    (N : (d : U.I₀) → (U.X d).Modules) (d : U.I₀)
    (r : pullback (U.f a) (U.f b) ⟶ U.X d)
    (s : pullback ((U.pullback₁ (overlapStageMap R f hij hjk)).f a)
      ((U.pullback₁ (overlapStageMap R f hij hjk)).f b) ⟶
      (U.pullback₁ (overlapStageMap R f hij hjk)).X d)
    (hr : overlapPairToOriginal R f hij U a b hjk ≫ r =
      s ≫ U.pullbackHom (overlapStageMap R f hij hjk) d) :
    (Scheme.Modules.pullback (overlapPairToModel R f hij U a b hjk)).obj
      ((Scheme.Modules.tensorPullback (overlapStageMap R
        (overlapModelHom R f hij U a b) (le_refl j) hjk)).obj
        ((Scheme.Modules.pullback (overlapModelChart R f hij U a b d r)).obj (N d))) ≅
      (Scheme.Modules.pullback s).obj
        ((Scheme.Modules.pullback (U.pullbackHom (overlapStageMap R f hij hjk) d)).obj
          (N d)) :=
  (Scheme.Modules.pullback _).mapIso ((overlapTensorComparison _).app _) ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    pullbackCompOfEq _ _ (s ≫ U.pullbackHom (overlapStageMap R f hij hjk) d) (by
      have hq : overlapStageMap R (overlapModelHom R f hij U a b)
          (le_refl j) hjk ≫ pullback.fst (overlapModelHom R f hij U a b)
            (Spec.map (R.map (homOfLE (le_refl j)))) =
          pullback.fst (overlapModelHom R f hij U a b)
            (Spec.map (R.map (homOfLE hjk))) := by
        dsimp only [overlapStageMap, baseChangeMap, pullback.map]
        simpa only [Category.comp_id, Over.mk_hom] using pullback.lift_fst _ _ _
      dsimp only [overlapModelChart]
      calc
        _ = overlapPairToModel R f hij U a b hjk ≫
            pullback.fst (overlapModelHom R f hij U a b)
              (Spec.map (R.map (homOfLE hjk))) ≫ r := by
          simpa only [Category.assoc] using
            congrArg (fun z ↦ overlapPairToModel R f hij U a b hjk ≫ z ≫ r) hq
        _ = overlapPairToOriginal R f hij U a b hjk ≫ r := by
          rw [← Category.assoc]
          exact congrArg (fun z ↦ z ≫ r) (pullback.lift_fst _ _ _)
        _ = _ := hr) (N d) ≪≫
    ((Scheme.Modules.pullbackComp s
      (U.pullbackHom (overlapStageMap R f hij hjk) d)).app (N d)).symm

def overlapPairMapOfModel {k : I} (hjk : j ≤ k)
    (N : (d : U.I₀) → (U.X d).Modules)
    (α : (Scheme.Modules.tensorPullback (overlapStageMap R
        (overlapModelHom R f hij U a b) (le_refl j) hjk)).obj
        ((Scheme.Modules.pullback (overlapModelChart R f hij U a b a
          (pullback.fst (U.f a) (U.f b)))).obj (N a)) ⟶
      (Scheme.Modules.tensorPullback (overlapStageMap R
        (overlapModelHom R f hij U a b) (le_refl j) hjk)).obj
        ((Scheme.Modules.pullback (overlapModelChart R f hij U a b b
          (pullback.snd (U.f a) (U.f b)))).obj (N b))) :
    let q := overlapStageMap R f hij hjk
    let V := U.pullback₁ q
    let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
    (Scheme.Modules.pullback (pullback.fst (V.f a) (V.f b))).obj (A a) ⟶
      (Scheme.Modules.pullback (pullback.snd (V.f a) (V.f b))).obj (A b) :=
  let V := U.pullback₁ (overlapStageMap R f hij hjk)
  let ta := overlapModelStageComparison R f hij U a b hjk N a
    (pullback.fst (U.f a) (U.f b)) (pullback.fst (V.f a) (V.f b))
    (pullback.lift_fst _ _ _)
  let tb := overlapModelStageComparison R f hij U a b hjk N b
    (pullback.snd (U.f a) (U.f b)) (pullback.snd (V.f a) (V.f b))
    (pullback.lift_snd _ _ _)
  ta.inv ≫ (Scheme.Modules.pullback (overlapPairToModel R f hij U a b hjk)).map α ≫ tb.hom
```

No proof-local reducibility commands followed these definitions.

## New

```lean
abbrev overlapTensorComparison {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Scheme.Modules.tensorPullback p ≅ Scheme.Modules.pullback p :=
  overlapAdjunctionComparison p

variable {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u})
  (c : Cone (R.op ⋙ Scheme.Spec)) {i : I} {Xi : Scheme.{u}}
  (f : Xi ⟶ Spec (R.obj i)) {j : I} (hij : i ≤ j)
  (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
  (a b : U.I₀)

abbrev overlapModelLimitComparison
    (N : (d : U.I₀) → (U.X d).Modules) (d : U.I₀)
    (r : pullback (U.f a) (U.f b) ⟶ U.X d)
    (hr : r ≫ U.f d = pullback.fst (U.f a) (U.f b) ≫ U.f a) :
    (Scheme.Modules.tensorPullback (overlapLimitMap R c
      (overlapModelHom R f hij U a b) (le_refl j))).obj
      ((Scheme.Modules.pullback (overlapModelChart R f hij U a b d r)).obj (N d)) ≅
    (Scheme.Modules.pullback (overlapModelLimitChart R c f hij U a b d r hr)).obj
      ((Scheme.Modules.pullback (U.pullbackHom (overlapLimitMap R c f hij) d)).obj
        (N d)) :=
  overlapDirectModelComparison
    (overlapLimitMap R c (overlapModelHom R f hij U a b) (le_refl j))
    (overlapModelChart R f hij U a b d r) (pullback.fst _ _ ≫ r)
    (overlapModelLimitChart R c f hij U a b d r hr)
    (U.pullbackHom (overlapLimitMap R c f hij) d) (by
        dsimp only [overlapLimitMap, overlapModelChart, baseChangeMap, pullback.map,
          Over.mk_hom, Over.homMk_left]
        simp only [← Category.assoc, pullback.lift_fst, Category.comp_id])
      (by exact pullback.lift_snd _ _ _) (N d)

abbrev overlapModelConjugate
    (N : (d : U.I₀) → (U.X d).Modules)
    (M : (pullback f (c.π.app (op i))).Modules)
    (e : ∀ d, (Scheme.Modules.pullback
      (U.pullbackHom (overlapLimitMap R c f hij) d)).obj (N d) ≅
      (Scheme.Modules.pullback ((U.pullback₁ (overlapLimitMap R c f hij)).f d)).obj M) :
    (Scheme.Modules.tensorPullback (overlapLimitMap R c
      (overlapModelHom R f hij U a b) (le_refl j))).obj
      ((Scheme.Modules.pullback (overlapModelChart R f hij U a b a
        (pullback.fst (U.f a) (U.f b)))).obj (N a)) ⟶
    (Scheme.Modules.tensorPullback (overlapLimitMap R c
      (overlapModelHom R f hij U a b) (le_refl j))).obj
      ((Scheme.Modules.pullback (overlapModelChart R f hij U a b b
        (pullback.snd (U.f a) (U.f b)))).obj (N b)) := by
  let ra := pullback.fst (U.f a) (U.f b)
  let rb := pullback.snd (U.f a) (U.f b)
  let ha := overlapModelLimitChart R c f hij U a b a ra rfl
  let hb := overlapModelLimitChart R c f hij U a b b rb pullback.condition.symm
  let ta := overlapModelLimitComparison R c f hij U a b N a ra rfl
  let tb := overlapModelLimitComparison R c f hij U a b N b rb pullback.condition.symm
  exact overlapConjugatedTransition U (overlapLimitMap R c f hij) N M e a b
    (overlapModelLimitToBase R c f hij U a b) ha hb
    (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) _ _ ta tb

abbrev overlapModelStageComparison {k : I} (hjk : j ≤ k)
    (N : (d : U.I₀) → (U.X d).Modules) (d : U.I₀)
    (r : pullback (U.f a) (U.f b) ⟶ U.X d)
    (s : pullback ((U.pullback₁ (overlapStageMap R f hij hjk)).f a)
      ((U.pullback₁ (overlapStageMap R f hij hjk)).f b) ⟶
      (U.pullback₁ (overlapStageMap R f hij hjk)).X d)
    (hr : overlapPairToOriginal R f hij U a b hjk ≫ r =
      s ≫ U.pullbackHom (overlapStageMap R f hij hjk) d) :
    (Scheme.Modules.pullback (overlapPairToModel R f hij U a b hjk)).obj
      ((Scheme.Modules.tensorPullback (overlapStageMap R
        (overlapModelHom R f hij U a b) (le_refl j) hjk)).obj
        ((Scheme.Modules.pullback (overlapModelChart R f hij U a b d r)).obj (N d))) ≅
      (Scheme.Modules.pullback s).obj
        ((Scheme.Modules.pullback (U.pullbackHom (overlapStageMap R f hij hjk) d)).obj
          (N d)) :=
  overlapStageModelComparison (overlapPairToModel R f hij U a b hjk)
    (overlapStageMap R (overlapModelHom R f hij U a b) (le_refl j) hjk)
    (overlapModelChart R f hij U a b d r) s
    (U.pullbackHom (overlapStageMap R f hij hjk) d) (by
      have hq : overlapStageMap R (overlapModelHom R f hij U a b)
          (le_refl j) hjk ≫ pullback.fst (overlapModelHom R f hij U a b)
            (Spec.map (R.map (homOfLE (le_refl j)))) =
          pullback.fst (overlapModelHom R f hij U a b)
            (Spec.map (R.map (homOfLE hjk))) := by
        dsimp only [overlapStageMap, baseChangeMap, pullback.map]
        simpa only [Category.comp_id, Over.mk_hom] using pullback.lift_fst _ _ _
      dsimp only [overlapModelChart]
      calc
        _ = overlapPairToModel R f hij U a b hjk ≫
            pullback.fst (overlapModelHom R f hij U a b)
              (Spec.map (R.map (homOfLE hjk))) ≫ r := by
          simpa only [Category.assoc] using
            congrArg (fun z ↦ overlapPairToModel R f hij U a b hjk ≫ z ≫ r) hq
        _ = overlapPairToOriginal R f hij U a b hjk ≫ r := by
          rw [← Category.assoc]
          exact congrArg (fun z ↦ z ≫ r) (pullback.lift_fst _ _ _)
        _ = _ := hr) (N d)

@[irreducible]
def overlapPairMapOfModel {k : I} (hjk : j ≤ k)
    (N : (d : U.I₀) → (U.X d).Modules)
    (α : (Scheme.Modules.tensorPullback (overlapStageMap R
        (overlapModelHom R f hij U a b) (le_refl j) hjk)).obj
        ((Scheme.Modules.pullback (overlapModelChart R f hij U a b a
          (pullback.fst (U.f a) (U.f b)))).obj (N a)) ⟶
      (Scheme.Modules.tensorPullback (overlapStageMap R
        (overlapModelHom R f hij U a b) (le_refl j) hjk)).obj
        ((Scheme.Modules.pullback (overlapModelChart R f hij U a b b
          (pullback.snd (U.f a) (U.f b)))).obj (N b))) :
    let q := overlapStageMap R f hij hjk
    let V := U.pullback₁ q
    let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
    (Scheme.Modules.pullback (pullback.fst (V.f a) (V.f b))).obj (A a) ⟶
      (Scheme.Modules.pullback (pullback.snd (V.f a) (V.f b))).obj (A b) :=
  let V := U.pullback₁ (overlapStageMap R f hij hjk)
  let ta := overlapModelStageComparison R f hij U a b hjk N a
    (pullback.fst (U.f a) (U.f b)) (pullback.fst (V.f a) (V.f b))
    (pullback.lift_fst _ _ _)
  let tb := overlapModelStageComparison R f hij U a b hjk N b
    (pullback.snd (U.f a) (U.f b)) (pullback.snd (V.f a) (V.f b))
    (pullback.lift_snd _ _ _)
  ta.inv ≫ (Scheme.Modules.pullback (overlapPairToModel R f hij U a b hjk)).map α ≫ tb.hom
```

The tensor comparison and the specialized limit/stage/conjugate wrappers become
abbrevs of the explicit generic constructors. This gives the kernel a preferred
unfolding direction: expand the wrapper first, then match the shared constructor
without expanding its large inverse-image composite on both sides.
The new explicit constructors are overlapAdjunctionComparison,
overlapDirectModelComparison, overlapStageModelComparison and
overlapConjugatedTransition, in OverlapConjugateRestriction.lean. Their bodies contain
actual composites, not sorry. Immediately before the proof:

```lean
attribute [local implicit_reducible] Precoverage.ZeroHypercover.pullback₁
  PreZeroHypercover.pullback₁ Scheme.Modules.pseudofunctor
  CategoryTheory.Pseudofunctor.comp CategoryTheory.PrelaxFunctor.comp
  CategoryTheory.Bicategory.Adj.forget₁ CategoryTheory.LocallyDiscrete.mkPseudofunctor
  CategoryTheory.PrelaxFunctorStruct.comp Prefunctor.comp
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete CategoryTheory.Cat.of
  CategoryTheory.Bundled.of CategoryTheory.Adjunction.toCat
  overlapLimitMap overlapStageMap CategoryTheory.Pseudofunctor.toDescentData
  CategoryTheory.Pseudofunctor.DescentData.ofObj Quiver.Hom.toLoc

attribute [local irreducible] Scheme.Modules.pullback Scheme.Modules.tensorPullback
  Scheme.Modules.tensorPullbackCompositionIso Adjunction.leftAdjointUniq
  Scheme.Modules.pullbackComp pullbackCompOfEq Scheme.Modules.pullbackCongr
  overlapDirectRestrictionIso overlapIteratedComparison
  CategoryTheory.Pseudofunctor.overlapPairBaseChangeHom limit.cone
  overlapPairSquare CategoryTheory.Pseudofunctor.overlapPairBaseChangeSquare

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OverlapPairModelTransport | J3 | Named constructors; unchanged theorem signature. |
| Sheaf.AlgebraicGeometry.FinitePresentationOverlapPairSingleStage | unclaimed | Uses overlapModelConjugate and overlapPairMapOfModel; unchanged signatures. |

The usage search lists no other actual users of the changed definitions. Transitive
importers retain every previous public declaration through the replacement public
import. Check the original single-stage module against the delivery's compiled overlay;
no forced adaptation is proposed unless that check fails.

## Status

landed 20261013T215606-L-898885 2026-10-13 (merge of deliver/J3/Sheaf.AlgebraicGeometry.OverlapPairModelTransport)
