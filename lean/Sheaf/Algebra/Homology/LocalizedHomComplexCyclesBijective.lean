module

public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace CategoryTheory

open Limits in
private lemma fan_bijective {ι : Type*} {X : Type u} {Y : ι → Type u}
    (π : ∀ i, X → Y i) (h : IsLimit (Fan.mk X (fun i ↦ ↾(π i)))) :
    Function.Bijective (fun x i ↦ π i x) := by
  constructor
  · intro x y hxy
    have he : (↾fun _ : PUnit.{u + 1} ↦ x) = (↾fun _ : PUnit.{u + 1} ↦ y) := by
      apply h.hom_ext
      intro i
      ext z
      exact congrFun hxy i.as
    exact ConcreteCategory.congr_hom he PUnit.unit
  · intro y
    let c := Fan.mk PUnit.{u + 1} (fun i ↦ ↾fun _ ↦ y i)
    refine ⟨h.lift c PUnit.unit, funext fun i ↦ ?_⟩
    exact ConcreteCategory.congr_hom (h.fac c ⟨i⟩) PUnit.unit

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 2000000 in
-- Evaluated products and slice-restriction components require extra elaboration work.
set_option backward.defeqAttrib.useBackward false in
private theorem cycles_bijective_of_product
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    (L I : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (hzero : Functor.PreservesZeroMorphisms
      (SheafOfModules.overFunctor.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) U))
    (H : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (π : ∀ (n p q : ℤ), p + n = q →
      (H.X n ⟶ SheafOfModules.homObj (R := R) (L.X p) (I.X q)))
    (hlimit : ∀ n : ℤ, Nonempty (Limits.IsLimit (Limits.Fan.mk (H.X n)
      (fun p : ℤ ↦ π n p (p + n) rfl))))
    (hdiff : ∀ p : ℤ, H.d 0 1 ≫ π 1 p (p + 1) rfl =
      π 0 p p (add_zero p) ≫ SheafOfModules.homObjMap (R := R) (𝟙 (L.X p))
        (I.d p (p + 1)) -
      π 0 (p + 1) (p + 1) (add_zero _) ≫
        SheafOfModules.homObjMap (R := R) (L.d p (p + 1)) (𝟙 (I.X (p + 1)))) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
    let S := ((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj H
    letI := hzero
    let res : CochainComplex (SheafOfModules.{max u v} R₀) ℤ ⥤
        CochainComplex (SheafOfModules.{max u v} (R₀.over U)) ℤ :=
      (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex (ComplexShape.up ℤ)
    ∀ f : S.cycles 0 → (res.obj L ⟶ res.obj I),
      (∀ (z : S.cycles 0) (p : ℤ) (W : (Over U)ᵒᵖ),
        ((f z).f p).val.app W =
          (((π 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)).app W) →
      Function.Bijective f := by
  classical
  intro R₀ S res f hf
  let E := SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
    forget (ModuleCat.{max u v} (R₀.obj.obj (op U)))
  have hprod (n : ℤ) : Function.Bijective
      (fun (x : (H.X n).val.obj (op U)) p ↦
        ((π n p (p + n) rfl).val.app (op U)) x) := by
    have hc := (hlimit n).some
    have he := (Limits.isLimitMapConeFanMkEquiv E _ _).1 (Limits.isLimitOfPreserves E hc)
    exact fan_bijective _ he
  have hp0 : Function.Bijective
      (fun (x : (H.X 0).val.obj (op U)) p ↦
        ((π 0 p p (add_zero p)).val.app (op U)) x) := by
    let e := Equiv.piCongrRight (fun p : ℤ ↦ Equiv.cast
      (congrArg (fun q : ℤ ↦ ↥((SheafOfModules.homObj (R := R) (L.X p) (I.X q)).val.obj (op U)))
        (add_zero p)))
    have hcast (p q : ℤ) (h : p + 0 = q) (x : (H.X 0).val.obj (op U)) :
        cast (congrArg
          (fun q : ℤ ↦ ↥((SheafOfModules.homObj (R := R) (L.X p) (I.X q)).val.obj (op U))) h)
          (((π 0 p (p + 0) rfl).val.app (op U)) x) =
          (((π 0 p q h).val.app (op U)) x) := by
      subst q
      rfl
    have heq : (fun x ↦ e (fun p ↦ ((π 0 p (p + 0) rfl).val.app (op U)) x)) =
        (fun (x : (H.X 0).val.obj (op U)) p ↦
          ((π 0 p p (add_zero p)).val.app (op U)) x) := by
      funext x p
      exact hcast p p (add_zero p) x
    rw [← heq]
    exact e.bijective.comp (hprod 0)
  constructor
  · intro z z' hzz'
    apply (AddCommGrpCat.mono_iff_injective (S.iCycles 0)).1 inferInstance
    apply hp0.1
    funext p
    apply PresheafOfModules.hom_ext
    intro W
    exact (hf z p W).symm.trans
      ((congrArg (fun g ↦ (g.f p).val.app W) hzz').trans (hf z' p W))
  · intro g
    obtain ⟨x, hx⟩ := hp0.2 (fun p ↦ (g.f p).val)
    have hx' (p : ℤ) : ((π 0 p p (add_zero p)).val.app (op U)) x =
        (g.f p).val := congrFun hx p
    have hdx : S.d 0 1 x = 0 := by
      apply (hprod 1).1
      funext p
      have hd := hdiff p
      have he := congrArg
        (fun k : H.X 0 ⟶ SheafOfModules.homObj (R := R) (L.X p) (I.X (p + 1)) ↦
          (k.val.app (op U)) x) hd
      change ((π 1 p (p + 1) rfl).val.app (op U)) (S.d 0 1 x) =
        (SheafOfModules.homObjMap (R := R) (𝟙 (L.X p)) (I.d p (p + 1))).val.app (op U)
          (((π 0 p p (add_zero p)).val.app (op U)) x) -
        (SheafOfModules.homObjMap (R := R) (L.d p (p + 1)) (𝟙 (I.X (p + 1)))).val.app
          (op U) (((π 0 (p + 1) (p + 1) (add_zero _)).val.app (op U)) x) at he
      rw [hx' p, hx' (p + 1)] at he
      have hc := congrArg (fun k ↦ k.val) (g.comm p (p + 1))
      change (PresheafOfModules.restrictOver R.obj U).map (𝟙 (L.X p).val) ≫
          (g.f p).val ≫ (PresheafOfModules.restrictOver R.obj U).map (I.d p (p + 1)).val =
        (PresheafOfModules.restrictOver R.obj U).map (L.d p (p + 1)).val ≫
          (g.f (p + 1)).val ≫
            (PresheafOfModules.restrictOver R.obj U).map (𝟙 (I.X (p + 1)).val) at hc
      change ((π 1 p (p + 1) rfl).val.app (op U)) (S.d 0 1 x) =
        ((π 1 p (p + 1) rfl).val.app (op U)) 0
      rw [map_zero]
      exact he.trans (sub_eq_zero.mpr hc)
    have hxker : (S.sc 0).g x = 0 := by
      change S.d 0 ((ComplexShape.up ℤ).next 0) x = 0
      rw [CochainComplex.next]
      exact hdx
    let z : S.cycles 0 := (S.sc 0).abCyclesIso.inv ⟨x, hxker⟩
    refine ⟨z, ?_⟩
    apply HomologicalComplex.hom_ext
    intro p
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    rw [hf z p W]
    have hz : S.iCycles 0 z = x := (S.sc 0).abCyclesIso_inv_apply_iCycles ⟨x, hxker⟩
    exact (congrArg (fun y ↦ (((π 0 p p (add_zero p)).val.app (op U)) y).app W)
      hz).trans (congrArg (fun k ↦ k.app W) (hx' p))

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 2000000 in
-- Evaluated products and slice-restriction components require extra elaboration work.
set_option backward.defeqAttrib.useBackward false in
/-- A function with the localized cycle projection formula is bijective.
Source: Stacks Project, Tag 0A8X, construction preceding Equation 0A8Y.
(blueprint: lem-pur-localized-hom-complex-cycles-bijective)

Proof: section evaluation preserves the product cone supplied by
homComplex_exists: forgetful functors for sheaves and modules preserve limits,
and evaluation of presheaves preserves limits. Its degree-zero projections
therefore identify sections with arbitrary families of internal-Hom sections.
For injectivity, equality of the chain maps f z and f z' implies equality of
all components on all objects of the slice. The formula gives equality of the
projected internal-Hom sections. The evaluated product projections are jointly
injective, so the included cycles agree. The cycle inclusion is monic, hence
injective in abelian groups, giving z = z'. For surjectivity, take a chain map g.
View its components as internal-Hom sections at U and assemble them into a
section x using the evaluated degree-zero product universal property. The
chain-map equations and the degree-zero differential formula make every
degree-one projection of d x zero. Joint injectivity of these projections gives
d x = 0. The kernel universal property of iCycles supplies a cycle z with
included value x. The prescribed formula shows f z and g have equal components
on every slice object, so extensionality of natural transformations, sheaf
morphisms, and complex morphisms gives f z = g. No boundedness or finite-support
assumption is used; products are indexed by all integers. -/
theorem localizedHomComplex_cycles_bijective
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    (L I : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (hzero : Functor.PreservesZeroMorphisms
      (SheafOfModules.overFunctor.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) U)) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
    let H := homComplex (R := R) L I
    let π := Classical.choose (Classical.choose_spec
      (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
    let S := ((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj H
    letI := hzero
    let res : CochainComplex (SheafOfModules.{max u v} R₀) ℤ ⥤
        CochainComplex (SheafOfModules.{max u v} (R₀.over U)) ℤ :=
      (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex (ComplexShape.up ℤ)
    ∀ f : S.cycles 0 → (res.obj L ⟶ res.obj I),
      (∀ (z : S.cycles 0) (p : ℤ) (W : (Over U)ᵒᵖ),
        ((f z).f p).val.app W =
          (((π L I 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)).app W) →
      Function.Bijective f := by
  classical
  have hspec := Classical.choose_spec (Classical.choose_spec
    (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
  refine cycles_bijective_of_product J R U L I hzero _ _ (hspec.1 L I) ?_
  intro p
  have hd := hspec.2.1 L I 0 1 p (p + 1) p (p + 1)
    (by decide) rfl (add_zero p) (add_zero (p + 1))
  simp only [Int.negOnePow_zero, one_smul] at hd
  exact hd

end CategoryTheory
