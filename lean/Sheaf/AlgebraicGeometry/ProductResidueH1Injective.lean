/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups H3 and G1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.PicardH1ProductInjective
import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullbackFunctorial
import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf

/-!
# Joint H¹ injectivity of the two product slices after residue-field base change

Source: Stacks Project, Tag 0BF3, Kunneth input in the proof.
(blueprint: lem-sc-product-residue-h1-injective).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem app_isIso_of_tensor_unit {A B : Scheme.{u}} (g : A ⟶ B)
    (h : IsIso ((Classical.choose (Modules.exists_tensorPullbackAdjunction g)).unit.app
      (SheafOfModules.unit B.ringCatSheaf))) (U : B.Opens) : IsIso (g.app U) := by
  have := h
  have := (Modules.tensorPullbackObjUnitToUnit_isIso g).1
  have hs : IsIso (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) := by
    rw [← (Modules.tensorPullbackObjUnitToUnit_isIso g).2]
    infer_instance
  have happ := Functor.map_isIso (SheafOfModules.evaluation B.ringCatSheaf
    (Opposite.op U)) (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)
  rw [ConcreteCategory.isIso_iff_bijective] at happ ⊢
  exact happ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def productBaseChangeIso
    {C : Type*} [Category C] [HasPullbacks C]
    {S X Y T : C} (f : X ⟶ S) (g : Y ⟶ S) (t : T ⟶ S) :
    pullback (pullback.fst f g ≫ f) t ≅
      pullback (pullback.snd f t) (pullback.snd g t) := by
  let p := pullback.fst f g ≫ f
  let a : pullback p t ⟶ pullback f t :=
    pullback.lift (pullback.fst p t ≫ pullback.fst f g) (pullback.snd p t)
      (by simpa only [p, Category.assoc] using (pullback.condition (f := p) (g := t)))
  let b : pullback p t ⟶ pullback g t :=
    pullback.lift (pullback.fst p t ≫ pullback.snd f g) (pullback.snd p t)
      (by rw [Category.assoc, ← pullback.condition, ← Category.assoc];
          simpa only [p, Category.assoc] using (pullback.condition (f := p) (g := t)))
  let h : pullback p t ⟶ pullback (pullback.snd f t) (pullback.snd g t) :=
    pullback.lift a b (by simp [a, b])
  let c : pullback (pullback.snd f t) (pullback.snd g t) ⟶ pullback f g :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst f t)
      (pullback.snd _ _ ≫ pullback.fst g t) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc,
          pullback.condition, Category.assoc, ← pullback.condition, Category.assoc])
  let v : pullback (pullback.snd f t) (pullback.snd g t) ⟶ pullback p t :=
    pullback.lift c (pullback.fst _ _ ≫ pullback.snd f t) (by
      dsimp only [p]
      rw [← Category.assoc, show c ≫ pullback.fst f g = _ from pullback.lift_fst ..,
        Category.assoc, pullback.condition, Category.assoc])
  refine ⟨h, v, ?_, ?_⟩
  · apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [p, h, v, c, a, b, Category.assoc]
    · simp [p, h, v, a, Category.assoc]
  · apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [p, h, v, c, a, Category.assoc]
    · apply pullback.hom_ext
      · simp [p, h, v, c, b, Category.assoc]
      · simp only [p, h, v, b, Category.assoc, pullback.lift_snd,
          Category.id_comp]
        exact pullback.condition

private theorem productBaseChangeIso_hom_fst
    {C : Type*} [Category C] [HasPullbacks C]
    {S X Y T : C} (f : X ⟶ S) (g : Y ⟶ S) (t : T ⟶ S) :
    (productBaseChangeIso f g t).hom ≫ pullback.fst _ _ =
      pullback.lift (f := f) (g := t)
        (pullback.fst (pullback.fst f g ≫ f) t ≫ pullback.fst f g)
        (pullback.snd (pullback.fst f g ≫ f) t)
        (by simpa only [Category.assoc] using
          (pullback.condition (f := pullback.fst f g ≫ f) (g := t))) := by
  exact pullback.lift_fst ..

private theorem productBaseChangeIso_hom_snd
    {C : Type*} [Category C] [HasPullbacks C]
    {S X Y T : C} (f : X ⟶ S) (g : Y ⟶ S) (t : T ⟶ S) :
    (productBaseChangeIso f g t).hom ≫ pullback.snd _ _ =
      pullback.lift (f := g) (g := t)
        (pullback.fst (pullback.fst f g ≫ f) t ≫ pullback.snd f g)
        (pullback.snd (pullback.fst f g ≫ f) t)
        (by rw [Category.assoc, ← pullback.condition, ← Category.assoc];
            simpa only [Category.assoc] using
              (pullback.condition (f := pullback.fst f g ≫ f) (g := t))) := by
  exact pullback.lift_snd ..


private theorem injective_slices_of_iso
    {A B P Q : Scheme.{u}} (e : P ≅ Q)
    (jX : A ⟶ P) (jY : B ⟶ P) (aX : A ⟶ Q) (aY : B ⟶ Q)
    (hX : jX ≫ e.hom = aX) (hY : jY ≫ e.hom = aY)
    (hinj : Function.Injective
      ((structureSheafCohomologyPullback aX 1).prod
        (structureSheafCohomologyPullback aY 1))) :
    Function.Injective (fun z ↦
      (structureSheafCohomologyPullback jX 1 z,
        structureSheafCohomologyPullback jY 1 z)) := by
  have hmX : aX ≫ e.inv = jX := by
    rw [← hX, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hmY : aY ≫ e.inv = jY := by
    rw [← hY, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hcX : (structureSheafCohomologyPullback aX 1).comp
      (structureSheafCohomologyPullback e.inv 1) =
      structureSheafCohomologyPullback jX 1 := by
    rw [← structureSheafCohomologyPullback_functorial.2 aX e.inv 1, hmX]
  have hcY : (structureSheafCohomologyPullback aY 1).comp
      (structureSheafCohomologyPullback e.inv 1) =
      structureSheafCohomologyPullback jY 1 := by
    rw [← structureSheafCohomologyPullback_functorial.2 aY e.inv 1, hmY]
  have hc : (structureSheafCohomologyPullback e.hom 1).comp
      (structureSheafCohomologyPullback e.inv 1) = AddMonoidHom.id _ := by
    rw [← structureSheafCohomologyPullback_functorial.2 e.hom e.inv 1, e.hom_inv_id]
    exact structureSheafCohomologyPullback_functorial.1 P 1
  intro z w h
  have ht : structureSheafCohomologyPullback e.inv 1 z =
      structureSheafCohomologyPullback e.inv 1 w := by
    apply hinj
    exact Prod.ext
      ((DFunLike.congr_fun hcX z).trans
        ((congrArg Prod.fst h).trans (DFunLike.congr_fun hcX w).symm))
      ((DFunLike.congr_fun hcY z).trans
        ((congrArg Prod.snd h).trans (DFunLike.congr_fun hcY w).symm))
  exact (DFunLike.congr_fun hc z).symm.trans
    ((congrArg (structureSheafCohomologyPullback e.hom 1) ht).trans
      (DFunLike.congr_fun hc w))

/-- The residue-field base changes of the two section slices jointly detect H¹.
Source: Stacks Project, Tag 0BF3, first sentence of its proof, using Tag 0BED.
(blueprint: lem-sc-product-residue-h1-injective).

Proof: set k = κ(s). Universal structure pushforward evaluated at Spec k identifies
H⁰(X_s, O) and H⁰(Y_s, O) with k, through the canonical scalar maps. Base change of
σ and τ gives k-rational points of these proper k-schemes. Apply
picard_h1_product_injective to X_s and Y_s. Pullback pasting identifies
(X ×_S Y)_s with X_s ×_k Y_s, and identifies the two base-changed slice morphisms
with the rational-point slices in that theorem. Functoriality of structure-sheaf
cohomology transports the injectivity along this scheme isomorphism. Thus equality
of both slice images forces equality of the source classes. Neither a line bundle
nor its trivializations enter this assertion. -/
theorem product_residue_h1_injective
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsProper f] [IsProper g]
    (σ : S ⟶ X) (τ : S ⟶ Y)
    (hσ : σ ≫ f = 𝟙 S) (hτ : τ ≫ g = 𝟙 S)
    (hX : ∀ {T : Scheme.{u}} (t : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f t))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hY : ∀ {T : Scheme.{u}} (t : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd g t))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (s : S) :
    let p := pullback.fst f g ≫ f
    let iX := pullback.lift (𝟙 X) (f ≫ τ) (by simp [hτ])
    let iY := pullback.lift (g ≫ σ) (𝟙 Y) (by simp [hσ])
    let hiX : iX ≫ p = f := by
      dsimp only [p]
      rw [← Category.assoc, pullback.lift_fst, Category.id_comp]
    let hiY : iY ≫ p = g := by
      dsimp only [p]
      rw [← Category.assoc, pullback.lift_fst, Category.assoc, hσ, Category.comp_id]
    Function.Injective (fun x :
        Sheaf.H (structureSheafAb (pullback p (S.fromSpecResidueField s))) 1 ↦
      (structureSheafCohomologyPullback
        (((Over.pullback (S.fromSpecResidueField s)).map
          (Over.homMk (U := Over.mk f) (V := Over.mk p) iX hiX)).left) 1 x,
       structureSheafCohomologyPullback
        (((Over.pullback (S.fromSpecResidueField s)).map
          (Over.homMk (U := Over.mk g) (V := Over.mk p) iY hiY)).left) 1 x)) := by
  let k : Type u := S.residueField s
  let t := S.fromSpecResidueField s
  let A := pullback f t
  let B := pullback g t
  let fa : A ⟶ Spec (CommRingCat.of k) := pullback.snd f t
  let gb : B ⟶ Spec (CommRingCat.of k) := pullback.snd g t
  let : A.Over (Spec (CommRingCat.of k)) := ⟨fa⟩
  let : B.Over (Spec (CommRingCat.of k)) := ⟨gb⟩
  have hA : Function.Bijective (globalSectionsRingHom k (X := A)) := by
    have := app_isIso_of_tensor_unit fa (hX t) ⊤
    change Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fa.appTop).hom
    rw [← ConcreteCategory.isIso_iff_bijective]
    infer_instance
  have hB : Function.Bijective (globalSectionsRingHom k (X := B)) := by
    have := app_isIso_of_tensor_unit gb (hY t) ⊤
    change Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ gb.appTop).hom
    rw [← ConcreteCategory.isIso_iff_bijective]
    infer_instance
  have hfa : IsProper fa := inferInstanceAs (IsProper (pullback.snd f t))
  have hgb : IsProper gb := inferInstanceAs (IsProper (pullback.snd g t))
  let x : fa.fieldPoints k :=
    ⟨pullback.lift (t ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ]),
      by simp [fa]⟩
  let y : gb.fieldPoints k :=
    ⟨pullback.lift (t ≫ τ) (𝟙 _) (by simp [Category.assoc, hτ]),
      by simp [gb]⟩
  have hinj := @picard_h1_product_injective k inferInstance A B
    ⟨fa⟩ ⟨gb⟩ hfa hgb hA hB x y
  let p := pullback.fst f g ≫ f
  let iX : X ⟶ pullback f g := pullback.lift (𝟙 X) (f ≫ τ) (by simp [hτ])
  let iY : Y ⟶ pullback f g := pullback.lift (g ≫ σ) (𝟙 Y) (by simp [hσ])
  let hiX : iX ≫ p = f := by
    dsimp only [p]
    rw [← Category.assoc, pullback.lift_fst, Category.id_comp]
  let hiY : iY ≫ p = g := by
    dsimp only [p]
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, hσ, Category.comp_id]
  let jX : A ⟶ pullback p t := (((Over.pullback t).map
    (Over.homMk (U := Over.mk f) (V := Over.mk p) iX hiX)).left)
  let jY : B ⟶ pullback p t := (((Over.pullback t).map
    (Over.homMk (U := Over.mk g) (V := Over.mk p) iY hiY)).left)
  let e := productBaseChangeIso f g t
  let aX : A ⟶ pullback fa gb :=
    pullback.lift (f := fa) (g := gb) (𝟙 A) (fa ≫ y.1) (by
      rw [Category.id_comp, Category.assoc, y.2]
      simp)
  let aY : B ⟶ pullback fa gb :=
    pullback.lift (f := fa) (g := gb) (gb ≫ x.1) (𝟙 B) (by
      rw [Category.id_comp, Category.assoc, x.2]
      simp)
  have hjXfst : jX ≫ pullback.fst p t = pullback.fst f t ≫ iX :=
    pullback.lift_fst ..
  have hjXsnd : jX ≫ pullback.snd p t = pullback.snd f t := pullback.lift_snd ..
  have hjYfst : jY ≫ pullback.fst p t = pullback.fst g t ≫ iY :=
    pullback.lift_fst ..
  have hjYsnd : jY ≫ pullback.snd p t = pullback.snd g t := pullback.lift_snd ..
  have haXfst : aX ≫ pullback.fst fa gb = 𝟙 A := pullback.lift_fst ..
  have haXsnd : aX ≫ pullback.snd fa gb = fa ≫ y.1 := pullback.lift_snd ..
  have haYfst : aY ≫ pullback.fst fa gb = gb ≫ x.1 := pullback.lift_fst ..
  have haYsnd : aY ≫ pullback.snd fa gb = 𝟙 B := pullback.lift_snd ..
  have hiXfst : iX ≫ pullback.fst f g = 𝟙 X := pullback.lift_fst ..
  have hiXsnd : iX ≫ pullback.snd f g = f ≫ τ := pullback.lift_snd ..
  have hiYfst : iY ≫ pullback.fst f g = g ≫ σ := pullback.lift_fst ..
  have hiYsnd : iY ≫ pullback.snd f g = 𝟙 Y := pullback.lift_snd ..
  have hxfst : x.1 ≫ pullback.fst f t = t ≫ σ := pullback.lift_fst ..
  have hxsnd : x.1 ≫ pullback.snd f t = 𝟙 _ := pullback.lift_snd ..
  have hyfst : y.1 ≫ pullback.fst g t = t ≫ τ := pullback.lift_fst ..
  have hysnd : y.1 ≫ pullback.snd g t = 𝟙 _ := pullback.lift_snd ..
  have heX : jX ≫ e.hom = aX := by
    apply pullback.hom_ext
    · rw [Category.assoc, productBaseChangeIso_hom_fst, haXfst]
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hjXfst,
          Category.assoc, hiXfst, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, pullback.lift_snd, hjXsnd, Category.id_comp]
    · rw [Category.assoc, productBaseChangeIso_hom_snd, haXsnd]
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hjXfst,
          Category.assoc, hiXsnd, Category.assoc, hyfst]
        exact congrArg (fun q ↦ q ≫ τ) (pullback.condition (f := f) (g := t))
      · rw [Category.assoc, pullback.lift_snd, hjXsnd, Category.assoc, hysnd,
          Category.comp_id]
  have heY : jY ≫ e.hom = aY := by
    apply pullback.hom_ext
    · rw [Category.assoc, productBaseChangeIso_hom_fst, haYfst]
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hjYfst,
          Category.assoc, hiYfst, Category.assoc, hxfst]
        exact congrArg (fun q ↦ q ≫ σ) (pullback.condition (f := g) (g := t))
      · rw [Category.assoc, pullback.lift_snd, hjYsnd, Category.assoc, hxsnd,
          Category.comp_id]
    · rw [Category.assoc, productBaseChangeIso_hom_snd, haYsnd]
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hjYfst,
          Category.assoc, hiYsnd, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, pullback.lift_snd, hjYsnd, Category.id_comp]
  change Function.Injective
    ((structureSheafCohomologyPullback aX 1).prod
      (structureSheafCohomologyPullback aY 1)) at hinj
  change Function.Injective (fun z ↦
    (structureSheafCohomologyPullback jX 1 z, structureSheafCohomologyPullback jY 1 z))
  exact @injective_slices_of_iso A B (pullback p t) (pullback fa gb)
    e jX jY aX aY heX heY hinj

end AlgebraicGeometry.Scheme
