/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SequenceSiteOpenData

/-! # Scalar preservation by open extension

Source: Stacks Project, Tags 03DI, 03DJ and 05RU
(blueprint: lem-pur-sequence-open-scalars).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe c v r u s
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
namespace WeilConjectures.SemilinearSections

private def sectionMul {A : Type c} [Category.{v} A]
    {K : GrothendieckTopology A}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (R : CategoryTheory.Sheaf K CommRingCat.{r})
    (b : ∀ X : Aᵒᵖ, R.obj.obj X)
    (hb : ∀ {X Y : Aᵒᵖ} (f : X ⟶ Y), R.obj.map f (b X) = b Y)
    (M : SheafOfModules.{r} ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    M ⟶ M where
  val :=
    { app := fun X ↦ ModuleCat.ofHom
        { toFun := fun x ↦ b X • x
          map_add' := smul_add (b X)
          map_smul' := fun a x ↦ by
            change b X • (a • x) = a • (b X • x)
            rw [smul_smul, smul_smul]
            congr 1
            exact mul_comm (b X) a }
      naturality := by
        intro X Y f
        ext x
        change b Y • M.val.map f x = M.val.map f (b X • x)
        rw [M.val.map_smul]
        change b Y • M.val.map f x = R.obj.map f (b X) • M.val.map f x
        rw [hb f] }

private theorem extension_sectionMul {C : Type c} [Category.{v} C]
    [EssentiallySmall.{max c v r} C] (J : GrothendieckTopology C) (U : C)
    (R : Sheaf J CommRingCat.{max c v r})
    (b : ∀ X : Cᵒᵖ, R.obj.obj X)
    (hb : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), R.obj.map f (b X) = b Y)
    (M : Mod.{max c v, v, max c v r} (J.over U) (R.over U)) :
    (SheafOfModules.localizedSystemExtension.{c, v, r} R U).map
      (sectionMul (R.over U) (fun X ↦ b (op X.unop.left))
        (fun f ↦ hb ((Over.forget U).op.map f)) M) =
    sectionMul R b hb ((SheafOfModules.localizedSystemExtension.{c, v, r} R U).obj M) := by
  let adj := SheafOfModules.localizedSystemAdjunction.{c, v, r} R U
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  erw [← adj.unit.naturality]
  ext X x
  exact (adj.unit.app M).val.app X |>.hom.map_smul (b (op X.unop.left)) x

private theorem compatibleScalar {C : Type c} [Category.{v} C]
    [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
    (B : ℕ → Sheaf J CommRingCat.{r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
    (b : ∀ (n : ℕ) (X : Cᵒᵖ), (B n).obj.obj X)
    (hb : ∀ (n : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y), (B n).obj.map f (b n X) = b n Y)
    (hτ : ∀ {m n : ℕ} (h : n ≤ m) (X : Cᵒᵖ),
      (coefficientMap.{c, v, r} J B τ h).hom.app X (b m X) = b n X)
    {X Y : (ℕ × C)ᵒᵖ} (f : X ⟶ Y) :
    (systemRing.{c, v, r} J B τ).obj.map f (b X.unop.1 (op X.unop.2)) =
      b Y.unop.1 (op Y.unop.2) := by
  change (B _).obj.map f.unop.2.op
    ((coefficientMap.{c, v, r} J B τ (leOfHom f.unop.1)).hom.app _
      (b X.unop.1 (op X.unop.2))) = _
  rw [hτ, hb]

private theorem evaluation_smul {C : Type c} [Category.{v} C]
    [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
    (B : ℕ → Sheaf J CommRingCat.{r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
    (n : ℕ) (M : Systems.{c, v, r} J B τ) (X : Cᵒᵖ)
    (a : (B n).obj.obj X) (x : M.val.obj (op (n, X.unop))) :
    @SMul.smul ((B n).obj.obj X)
      (((evaluation.{c, v, r} J B τ n).obj M).val.obj X) inferInstance a x =
      a • x := by
  have he : ((eqToHom (evaluation_ring.{c, v, r} J B τ n).symm).hom.app X) = 𝟙 _ := by
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl
  change (((eqToHom (evaluation_ring.{c, v, r} J B τ n).symm).hom.app X) a) • x = _
  rw [he]
  rfl

set_option maxHeartbeats 800000 in
-- Evaluation transports scalar structures through the ring-identification isomorphism.
/-- Compatible sectionwise scalar endomorphisms are preserved by ordinary open extension.
Source: Stacks 03DI and 03CY (blueprint: lem-pur-sequence-open-scalars).
Proof: compatible sections act on the actual sequence-site module by multiplication.
The scalar formula for the level extension follows by transposing against its unit and
using linearity of that unit. Naturality of the level comparison transports this formula
back to the sequence module, where evaluation at all pairs detects equality. -/
theorem SequenceOpenOrdinary.scalars {C : Type c} [Category.{v} C]
    [EssentiallySmall.{max c v r} C] (J : GrothendieckTopology C) (U : C)
    (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
    (O : SequenceOpenOrdinary.{c, v, r} J U B τ) : O.Scalars.{c, v, r, s} := by
  intro R _ a ha hτ t M
  let b := fun (n : ℕ) (X : Cᵒᵖ) ↦ a n X t
  have hb := fun (n : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) ↦ ha n f t
  have ht := fun {m n : ℕ} (h : n ≤ m) (X : Cᵒᵖ) ↦ hτ h X t
  let bU := fun (n : ℕ) (X : (Over U)ᵒᵖ) ↦ b n (op X.unop.left)
  have hbU := fun (n : ℕ) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) ↦
    hb n ((Over.forget U).op.map f)
  have htU {m n : ℕ} (h : n ≤ m) (X : (Over U)ᵒᵖ) :
      (coefficientMap.{max c v, v, max c v r} (J.over U)
        (openTower.{c, v, r} J U B)
        (openTowerMap.{c, v, r} J U B τ) h).hom.app X (bU m X) = bU n X := by
    let F := rings.{c, v, max c v r} J B τ ⋙
      J.overPullback CommRingCat.{max c v r} U
    let G := rings.{max c v, v, max c v r} (J.over U)
      (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ)
    let e : F ⟶ G := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro k
      change (J.overPullback CommRingCat.{max c v r} U).map
        ((rings.{c, v, max c v r} J B τ).map (homOfLE (Nat.le_succ k)).op) ≫ 𝟙 _ =
        𝟙 _ ≫ (rings.{max c v, v, max c v r} (J.over U)
          (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ)).map
            (homOfLE (Nat.le_succ k)).op
      simp only [rings, Functor.ofOpSequence_map_homOfLE_succ,
        Category.id_comp, Category.comp_id])
    have he := e.naturality (homOfLE h).op
    change (J.overPullback CommRingCat.{max c v r} U).map
      (coefficientMap.{c, v, max c v r} J B τ h) ≫ 𝟙 _ =
        𝟙 _ ≫ coefficientMap.{max c v, v, max c v r} (J.over U)
          (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ) h at he
    rw [Category.comp_id, Category.id_comp] at he
    rw [← he]
    exact ht h (op X.unop.left)
  let f := sectionMul (systemRing (J.over U) (openTower.{c, v, r} J U B)
      (openTowerMap.{c, v, r} J U B τ))
    (fun X ↦ bU X.unop.1 (op X.unop.2))
    (fun k ↦ compatibleScalar.{max c v, v, max c v r} (J.over U)
      (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ) bU hbU htU k) M
  let g := sectionMul (systemRing J B τ) (fun X ↦ b X.unop.1 (op X.unop.2))
    (fun k ↦ compatibleScalar J B τ b hb ht k) (O.Jfun.obj M)
  refine ⟨f, g, fun X x ↦ rfl, fun X x ↦ rfl, ?_⟩
  ext X x
  let n := X.unop.1
  let V := op X.unop.2
  let E := evaluation.{max c v, v, max c v r} (J.over U)
    (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ) n
  have hf : E.map f = sectionMul ((B n).over U)
      (bU n) (hbU n) (E.obj M) := by
    ext Y y
    exact (evaluation_smul (J.over U) _ _ n M Y (bU n Y) y).symm
  have hmap := congrArg (fun q ↦ q.val.app V x) ((O.level n).hom.naturality f)
  have hscalar := extension_sectionMul.{c, v, r} J U (B n) (b n) (hb n) (E.obj M)
  rw [← hf] at hscalar
  change ((O.level n).hom.app M).val.app V ((O.Jfun.map f).val.app X x) =
    ((SheafOfModules.localizedSystemExtension.{c, v, r} (B n) U).map (E.map f)).val.app V
      (((O.level n).hom.app M).val.app V x) at hmap
  rw [hscalar] at hmap
  have hlin := (((O.level n).hom.app M).val.app V).hom.map_smul (b n V) x
  have hv := evaluation_smul.{c, v, max c v r} J B τ n (O.Jfun.obj M) V (b n V) x
  have hlin' : ((O.level n).hom.app M).val.app V (g.val.app X x) =
      b n V • (((O.level n).hom.app M).val.app V x) := by
    exact (congrArg (fun z ↦ ((O.level n).hom.app M).val.app V z) hv.symm).trans hlin
  have hc (z) : ((O.level n).inv.app M).val.app V
      (((O.level n).hom.app M).val.app V z) = z := by
    exact congrArg (fun q ↦ q.val.app V z) ((O.level n).hom_inv_id_app M)
  apply Function.LeftInverse.injective hc
  exact hmap.trans hlin'.symm

end WeilConjectures.SemilinearSections
