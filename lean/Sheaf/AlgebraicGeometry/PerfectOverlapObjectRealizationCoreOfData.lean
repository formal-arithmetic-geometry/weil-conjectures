/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectOverlapHomContinuityData
public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase
public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons
public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport
public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreCanonicalFamily
public import Sheaf.AlgebraicGeometry.PerfectHomTransport
public import Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionLocalization
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
import Sheaf.AlgebraicGeometry.PerfectOverlapCompositeObjectPin
import all Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreCanonicalFamily

/-! # Core object comparison data (without the final Hom pin).

Source: Stacks Project, Tags 09RE, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w v h v' h'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
private theorem existsPinned {α : Sort*} (a : α) : ∃ b : α, b = a := ⟨a, rfl⟩

/-- Cache a constructed comparison, specified uniquely by equality. -/
@[irreducible] private noncomputable def pinned {α : Sort*} (a : α) : α :=
  Classical.choose (existsPinned a)

private theorem pinned_eq {α : Sort*} (a : α) : pinned a = a := by
  unfold pinned
  exact Classical.choose_spec (existsPinned a)

/-- Use the equation API of the transport map before instantiating the geometry. -/
private theorem homMap_formula
    {Y S : Scheme.{u}} (s : Y ⟶ S) {T T' : Over S} (a : T' ⟶ T)
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (P Q : schemeDerivedCategory Y)
    (e : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q) :
    perfectHomMap s a e = (perfectHomComparison s a).hom.app P ≫
      (derivedPullback (baseChangeMap s a)).map e ≫ (perfectHomComparison s a).inv.app Q :=
  rfl

private theorem limitMap_formula
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (j : I) (Y : Scheme.{u}) (s : Y ⟶ Spec (R.obj j))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (k : Set.Ici j) (P Q : schemeDerivedCategory Y)
    (e : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property))))).obj P ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property))))).obj Q) :
    perfectLimitMap R c s k.property e = perfectHomMap s (overlapLimitArrow R c k) e := by
  rfl

/-- A core construction with abstract scheme maps. Keeping the maps as parameters
avoids reducing concrete chosen pullback cones in the component calculation. -/
@[irreducible] private def genericCoreStatement
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (j : I)
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (T : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over T))]
    (X Y : Scheme.{u}) (Yk : Set.Ici j → Scheme.{u})
    (pX : X ⟶ Spec c.pt) (pY : Y ⟶ Spec (R.obj j))
    (pK : ∀ k : Set.Ici j, Yk k ⟶ Spec (R.obj k.val))
    (f : ∀ k : Set.Ici j, Yk k ⟶ Y) (g : X ⟶ Y)
    (gk : ∀ k : Set.Ici j, X ⟶ Yk k) (hgf : ∀ k, gk k ≫ f k = g)
    (hg : IsPullback g pX pY (Spec.map (c.ι.app j)))
    (hf : ∀ k : Set.Ici j, IsPullback (f k) (pK k) pY
      (Spec.map (R.map (homOfLE k.property))))
    (U V : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (g ∣_ U)).obj A ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (g ∣_ V)).obj B ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ V)).mapDerivedCategory.obj E) : Prop :=
  let W := U ⊓ V
  let s := W.ι ≫ pY
  let P := g ⁻¹ᵁ U
  let Q := g ⁻¹ᵁ V
  let C : Set.Ici j → Type (u + 1) := fun k ↦
    schemeDerivedCategory (f k ⁻¹ᵁ U ⊓ f k ⁻¹ᵁ V).toScheme
  let F : (k : Set.Ici j) → Bool → C k := fun k b ↦
    if b then
      (schemeOpenOverlapRestriction (Yk k)
        (homOfLE (inf_le_right : f k ⁻¹ᵁ U ⊓ f k ⁻¹ᵁ V ≤ f k ⁻¹ᵁ V))).mapDerivedCategory.obj
        ((derivedPullback (f k ∣_ V)).obj B)
    else
      (schemeOpenOverlapRestriction (Yk k)
        (homOfLE (inf_le_left : f k ⁻¹ᵁ U ⊓ f k ⁻¹ᵁ V ≤ f k ⁻¹ᵁ U))).mapDerivedCategory.obj
        ((derivedPullback (f k ∣_ U)).obj A)
  let data := fun k ↦ transportDataOfComposite (f k) (gk k) g (hgf k) U V A B E φU φV
  let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
    (homOfLE (inf_le_left : P ⊓ Q ≤ P))).mapDerivedCategory
  let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
    (homOfLE (inf_le_right : P ⊓ Q ≤ Q))).mapDerivedCategory
  let τU := (Functor.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) P)
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
      (homOfLE (inf_le_left : P ⊓ Q ≤ P)))).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (inf_le_left : P ⊓ Q ≤ P)))
  let τV := (Functor.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) Q)
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
      (homOfLE (inf_le_right : P ⊓ Q ≤ Q)))).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (inf_le_right : P ⊓ Q ≤ Q)))
  let RW := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
    (P ⊓ Q)).mapDerivedCategory
  let G : ∀ k, C k ⥤ DerivedCategory (SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over (P ⊓ Q))) := fun k ↦ (data k).d.toDiagram.HW
  let ψ : ∀ k b, (G k).obj (F k b) ≅ RW.obj E := fun k b ↦
    match b with
    | true => (data k).d.toDiagram.γV.symm.app ((derivedPullback (f k ∣_ V)).obj B) ≪≫
        SQ.mapIso (data k).θV ≪≫ τV.app E
    | false => (data k).d.toDiagram.γU.symm.app ((derivedPullback (f k ∣_ U)).obj A) ≪≫
        SP.mapIso (data k).θU ≪≫ τU.app E
  let stageEquiv := fun k ↦ perfectOverlapStageEquivalence (f k) (pK k) pY
    (Spec.map (R.map (homOfLE k.property))) (hf k) U V
  let apexEquiv := perfectOverlapApexEquivalence g pX pY (Spec.map (c.ι.app j)) hg U V
  let objects := fun b : Bool ↦
    if b then (derivedPullback (Y.homOfLE (inf_le_right : W ≤ V))).obj B
    else (derivedPullback (Y.homOfLE (inf_le_left : W ≤ U))).obj A
  Nonempty (PerfectHomObjectRealizationCore R c j C F _ (fun _ ↦ RW.obj E) G ψ
    W.toScheme s objects stageEquiv apexEquiv)

private theorem assembleOverlapCore
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (j : I)
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (T : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over T))]
    (X Y : Scheme.{u}) (Yk : Set.Ici j → Scheme.{u})
    (pX : X ⟶ Spec c.pt) (pY : Y ⟶ Spec (R.obj j))
    (pK : ∀ k : Set.Ici j, Yk k ⟶ Spec (R.obj k.val))
    (f : ∀ k : Set.Ici j, Yk k ⟶ Y) (g : X ⟶ Y)
    (gk : ∀ k : Set.Ici j, X ⟶ Yk k) (hgf : ∀ k, gk k ≫ f k = g)
    (hg : IsPullback g pX pY (Spec.map (c.ι.app j)))
    (hf : ∀ k : Set.Ici j, IsPullback (f k) (pK k) pY
      (Spec.map (R.map (homOfLE k.property))))
    (U V : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (g ∣_ U)).obj A ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (g ∣_ V)).obj B ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ V)).mapDerivedCategory.obj E)
    (hgk : ∀ k : Set.Ici j, gk k ≫ pK k = pX ≫ Spec.map (c.ι.app k.val)) :
    genericCoreStatement R c j X Y Yk pX pY pK f g gk hgf hg hf U V A B E φU φV := by
  unfold genericCoreStatement
  intro W s P Q C F data SP SQ τU τV RW G ψ stageEquiv apexEquiv objects
  let r (k : Set.Ici j) := (gk k).resLE (f k ⁻¹ᵁ W) (g ⁻¹ᵁ W)
    (by rw [← Scheme.Hom.comp_preimage, hgf k])
  let eY := ((isPullback_morphismRestrict g W).paste_vert hg).isoPullback
  let eK (k : Set.Ici j) :=
    ((isPullback_morphismRestrict (f k) W).paste_vert (hf k)).isoPullback
  have hmap (k : Set.Ici j) : eY.inv ≫ r k =
      baseChangeMap s (overlapLimitArrow R c k) ≫ (eK k).inv := by
    exact perfectOverlapCartesianComponentOver g (gk k) (f k) pX (pK k) pY
      (Spec.map (c.ι.app j)) (Spec.map (R.map (homOfLE k.property)))
      (overlapLimitArrow R c k) (hgf k) (hgk k) (hf k) W (r k)
      ((gk k).resLE_comp_ι _) eY (eK k)
      ((isPullback_morphismRestrict g W).paste_vert hg).isoPullback_inv_fst
      ((isPullback_morphismRestrict g W).paste_vert hg).isoPullback_inv_snd
      ((isPullback_morphismRestrict (f k) W).paste_vert (hf k)).isoPullback_inv_fst
      ((isPullback_morphismRestrict (f k) W).paste_vert (hf k)).isoPullback_inv_snd
  let transition (k : Set.Ici j) :=
    derivedPullback (baseChangeMap s (overlapLimitArrow R c k))
  let comparison : ∀ k, G k ⋙ apexEquiv.functor ≅
      (stageEquiv k).functor ⋙ transition k := by
    intro k
    dsimp only [G, data, transportDataOfComposite,
      schemeComparisonFromRestrictions, comparisonFromRestrictions]
    exact perfectOverlapNaturalComparisonOfSquare g (f k) pX (pK k) pY
      (Spec.map (c.ι.app j)) (Spec.map (R.map (homOfLE k.property))) hg (hf k) U V
      (r k) (baseChangeMap s (overlapLimitArrow R c k)) (hmap k)
  let σ : ∀ k b, (stageEquiv k).functor.obj (F k b) ≅
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property))))).obj
        (objects b) := pinned (fun k b ↦ Bool.casesOn b
      ((perfectOverlapStageObjectIso (f k) (pK k) pY _ (hf k)
          U V U inf_le_left).app A)
      ((perfectOverlapStageObjectIso (f k) (pK k) pY _ (hf k)
          U V V inf_le_right).app B))
  let ρ : ∀ b, apexEquiv.functor.obj (RW.obj E) ≅
      (derivedPullback (pullback.fst s (Spec.map (c.ι.app j)))).obj (objects b) :=
    pinned (fun b ↦ Bool.casesOn b
      (perfectOverlapApexObjectIso g pX pY _ hg U V U inf_le_left A E φU)
      (perfectOverlapApexObjectIso g pX pY _ hg U V V inf_le_right B E φV))
  let χ := pinned (fun k ↦ perfectHomComparison s (overlapLimitArrow R c k))
  let η := pinned comparison
  refine ⟨{
    stageObj := σ
    apexObj := ρ
    transition := transition
    baseComparison := χ
    transition_pin := ?_
    comparison := η
    object_pin := ?_ }⟩
  · intro k M N e
    dsimp only [χ]
    rw [pinned_eq]
    exact (limitMap_formula R c j _ s k M N e).trans
      (homMap_formula s (overlapLimitArrow R c k) M N e)
  · intro k b
    have hp := perfect_overlap_composite_object_pin (f k) (gk k) g (hgf k)
      pX (pK k) pY (Spec.map (c.ι.app j)) (Spec.map (R.map (homOfLE k.property)))
      hg (hf k) (overlapLimitArrow R c k) U V A B E φU φV (hmap k)
      (σ k) ρ (η k) (χ k)
      (congrFun (pinned_eq _) k) (pinned_eq _)
      (congrFun (pinned_eq _) k) (congrFun (pinned_eq _) k)
    cases b <;> exact hp _

set_option maxHeartbeats 8000000 in
-- The dependent core record has seven large functorial fields.
/-- Given the canonical stagewise comparison data, the transition and object pins
are assembled into the core realization structure.  The transition is obtained by
conjugating the overlap pullback functor by the fixed stage and apex equivalences.
The counit-pinned derived-pullback composition comparison gives `baseComparison`
and `transition_pin`; its naturality gives `comparison`.  Expanding the prescribed
`ψ` and the theta equations cancels the site unit and counit and proves `object_pin`.
This is the cartesian composition calculation from Tags 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-of-data).
-/
-- The canonicality hypothesis rules out independently twisted transports, which
-- make the unrestricted statement false (K1 delivery report).
@[irreducible] def perfectOverlapCoreOfDataStatement
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} ((SheafOfModules.{u})
        ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k) : Prop :=
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
      let P := gj ⁻¹ᵁ U
      let Q := gj ⁻¹ᵁ V
      let RU := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) P).mapDerivedCategory
      let RV := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) Q).mapDerivedCategory
      let RW := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
      let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
      let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
      let τU : RU ⋙ SP ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
      let τV : RV ⋙ SQ ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
    ∀ (data : (k : I) → (hjk : j ≤ k) →
      perfectOverlapComparisonDataType R c hc i Z t j hij hstage
        U V hcover hU hV A B hA hB E φU φV k hjk),
    data = perfectOverlapCanonicalComparisonFamily R c hc i Z t j hij hstage
      U V hcover hU hV A B hA hB E φU φV →
    Nonempty (
      let K := {k : I // j ≤ k}
      let C : K → Type (u + 1) := fun k ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        schemeDerivedCategory (U' ⊓ V').toScheme
      let F : (k : K) → Bool → C k := fun k b ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
        let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
        let SU : schemeDerivedCategory U'.toScheme ⥤
            schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
          (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
        let SV : schemeDerivedCategory V'.toScheme ⥤
            schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
          (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
        if b then SV.obj B' else SU.obj A'
      let G : (k : K) → C k ⥤
          DerivedCategory (SheafOfModules.{u}
            ((moduleRings X.toRingedSpace).over (P ⊓ Q))) := fun k ↦
        (data k.val k.property).d.toDiagram.HW
      let ψ : ∀ k b, (G k).obj (F k b) ≅ RW.obj E := fun k b ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
        let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
        let d := (data k.val k.property).d
        let θU := (data k.val k.property).θU
        let θV := (data k.val k.property).θV
        match b with
        | true => d.toDiagram.γV.symm.app B' ≪≫ SQ.mapIso θV ≪≫ τV.app E
        | false => d.toDiagram.γU.symm.app A' ≪≫ SP.mapIso θU ≪≫ τU.app E
      let stageEquiv : ∀ k : K, C k ≌
          schemeDerivedCategory (pullback
            ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
            (Spec.map (R.map (homOfLE k.property)))) := fun k ↦
        let arrow : Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))) ⟶
            Over.mk (Spec.map (R.map (homOfLE hij))) :=
          Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)
        perfectOverlapStageEquivalence (baseChangeMap t arrow)
          (pullback.snd t (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (pullback.snd t (Spec.map (R.map (homOfLE hij))))
          (Spec.map (R.map (homOfLE k.property))) (isPullback_baseChangeMap t arrow) U V
      let apexEquiv : DerivedCategory (SheafOfModules.{u}
          ((moduleRings X.toRingedSpace).over (P ⊓ Q))) ≌
          schemeDerivedCategory (pullback
            ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
            (Spec.map (c.ι.app j))) :=
        let arrow : Over.mk (Spec.map (c.ι.app i)) ⟶
            Over.mk (Spec.map (R.map (homOfLE hij))) :=
          Over.homMk (Spec.map (c.ι.app j))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])
        perfectOverlapApexEquivalence gj
          (pullback.snd t (Spec.map (c.ι.app i)))
          (pullback.snd t (Spec.map (R.map (homOfLE hij))))
          (Spec.map (c.ι.app j)) (isPullback_baseChangeMap t arrow) U V
      PerfectHomObjectRealizationCore R c j C F _ (fun _ ↦ RW.obj E) G ψ
        (U ⊓ V).toScheme
        ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
        (fun b ↦ if b then
          (derivedPullback (Yj.homOfLE (inf_le_right : U ⊓ V ≤ V))).obj B
          else (derivedPullback (Yj.homOfLE (inf_le_left : U ⊓ V ≤ U))).obj A)
        stageEquiv apexEquiv)

set_option maxHeartbeats 200000 in
-- The fieldwise core construction checks dependent functor and comparison types.
/-- The canonical comparison data realizes the named core proposition.
The name prevents Lean from expanding the full dependent record while
checking the statement and the fieldwise construction. -/
theorem perfect_overlap_object_realization_core_of_data
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u}
        ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k) :
    perfectOverlapCoreOfDataStatement R c hc i Z t j hij hstage := by
  unfold perfectOverlapCoreOfDataStatement
  classical
  intro Yj X gj U V hcover hU hV A B hA hB E instP instQ instX PU PV φU φV
    P Q RU RV RW SP SQ τU τV data hdata
  subst data
  let data := perfectOverlapCanonicalComparisonFamily R c hc i Z t j hij hstage
    U V hcover hU hV A B hA hB E φU φV
  let K := {k : I // j ≤ k}
  let C : K → Type (u + 1) := fun k ↦
    let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
    let f := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
      (Over.homMk (Spec.map (R.map (homOfLE k.property)))
        (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
    let U' := f ⁻¹ᵁ U
    let V' := f ⁻¹ᵁ V
    schemeDerivedCategory (U' ⊓ V').toScheme
  let F : (k : K) → Bool → C k := fun k b ↦
    let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
    let f := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
      (Over.homMk (Spec.map (R.map (homOfLE k.property)))
        (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
    let U' := f ⁻¹ᵁ U
    let V' := f ⁻¹ᵁ V
    let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
    let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
    let SU : schemeDerivedCategory U'.toScheme ⥤
        schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
      (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
    let SV : schemeDerivedCategory V'.toScheme ⥤
        schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
      (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
    if b then SV.obj B' else SU.obj A'
  let G : (k : K) → C k ⥤
      DerivedCategory (SheafOfModules.{u}
        ((moduleRings X.toRingedSpace).over (P ⊓ Q))) := fun k ↦
    (data k.val k.property).d.toDiagram.HW
  let ψ : ∀ k b, (G k).obj (F k b) ≅ RW.obj E := fun k b ↦
    let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
    let f := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
      (Over.homMk (Spec.map (R.map (homOfLE k.property)))
        (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
    let U' := f ⁻¹ᵁ U
    let V' := f ⁻¹ᵁ V
    let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
    let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
    let d := (data k.val k.property).d
    let θU := (data k.val k.property).θU
    let θV := (data k.val k.property).θV
    match b with
    | true => d.toDiagram.γV.symm.app B' ≪≫ SQ.mapIso θV ≪≫ τV.app E
    | false => d.toDiagram.γU.symm.app A' ≪≫ SP.mapIso θU ≪≫ τU.app E
  let stageEquiv : ∀ k : K, C k ≌
      schemeDerivedCategory (pullback
        ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
        (Spec.map (R.map (homOfLE k.property)))) := fun k ↦
    let arrow : Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))) ⟶
        Over.mk (Spec.map (R.map (homOfLE hij))) :=
      Over.homMk (Spec.map (R.map (homOfLE k.property)))
        (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)
    perfectOverlapStageEquivalence (baseChangeMap t arrow)
      (pullback.snd t (Spec.map (R.map (homOfLE (hij.trans k.property)))))
      (pullback.snd t (Spec.map (R.map (homOfLE hij))))
      (Spec.map (R.map (homOfLE k.property))) (isPullback_baseChangeMap t arrow) U V
  let apexEquiv : DerivedCategory (SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over (P ⊓ Q))) ≌
      schemeDerivedCategory (pullback
        ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
        (Spec.map (c.ι.app j))) :=
    let arrow : Over.mk (Spec.map (c.ι.app i)) ⟶
        Over.mk (Spec.map (R.map (homOfLE hij))) :=
      Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])
    perfectOverlapApexEquivalence gj
      (pullback.snd t (Spec.map (c.ι.app i)))
      (pullback.snd t (Spec.map (R.map (homOfLE hij))))
      (Spec.map (c.ι.app j)) (isPullback_baseChangeMap t arrow) U V
  change Nonempty (PerfectHomObjectRealizationCore R c j C F _ (fun _ ↦ RW.obj E) G ψ
    (U ⊓ V).toScheme
    ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
    (fun b ↦ if b then
      (derivedPullback (Yj.homOfLE (inf_le_right : U ⊓ V ≤ V))).obj B
      else (derivedPullback (Yj.homOfLE (inf_le_left : U ⊓ V ≤ U))).obj A)
    stageEquiv apexEquiv)
  let jk (k : Set.Ici j) :
      Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))) ⟶
        Over.mk (Spec.map (R.map (homOfLE hij))) :=
    Over.homMk (Spec.map (R.map (homOfLE k.property)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)
  let aj : Over.mk (Spec.map (c.ι.app i)) ⟶
      Over.mk (Spec.map (R.map (homOfLE hij))) :=
    Over.homMk (Spec.map (c.ι.app j))
      (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])
  let ak (k : Set.Ici j) : Over.mk (Spec.map (c.ι.app i)) ⟶
      Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))) :=
    Over.homMk (Spec.map (c.ι.app k.val))
      (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans k.property))])
  let f (k : Set.Ici j) := baseChangeMap t (jk k)
  let g (k : Set.Ici j) := baseChangeMap t (ak k)
  have hgf (k : Set.Ici j) : g k ≫ f k = gj := by
    change baseChangeMap t (ak k) ≫ baseChangeMap t (jk k) = baseChangeMap t aj
    rw [← baseChangeMap_comp]
    congr 1
    ext
    change Spec.map (c.ι.app k.val) ≫ Spec.map (R.map (homOfLE k.property)) =
      Spec.map (c.ι.app j)
    rw [← Spec.map_comp, c.w (homOfLE k.property)]
  have hcore := assembleOverlapCore R c j X Yj
    (fun k ↦ pullback t (Spec.map (R.map (homOfLE (hij.trans k.property)))))
    (pullback.snd t (Spec.map (c.ι.app i)))
    (pullback.snd t (Spec.map (R.map (homOfLE hij))))
    (fun k ↦ pullback.snd t (Spec.map (R.map (homOfLE (hij.trans k.property)))))
    f gj g hgf (isPullback_baseChangeMap t aj)
    (fun k ↦ isPullback_baseChangeMap t (jk k)) U V A B E φU φV
    (fun k ↦ baseChangeMap_snd t (ak k))
  unfold genericCoreStatement at hcore
  dsimp only [G, ψ, data, perfectOverlapCanonicalComparisonFamily]
  exact hcore

end AlgebraicGeometry
