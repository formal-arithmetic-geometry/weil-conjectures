/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Submission.WeilConjectures.CategoryTheory.TraceFormula.AbelianInverseImagePresentation
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Types.Basic
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all Mathlib.Algebra.Category.Ring.Limits
import all Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Submission.WeilConjectures.CategoryTheory.RingedToposRingData
import all Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import all Submission.WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Exactness of geometric inverse image on abelian sheaves and modules

Source: Stacks Project, Modules on Sites, Tags 04JC, 03D2, 03DA and 03DB;
Sites, Proposition 00YV (2)
(blueprint: lem-trf-geometric-inverse-image-exact).
-/

@[expose] public section

universe w uC vC uD vD

open CategoryTheory.Limits

namespace CategoryTheory.GeometricMorphism

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

private noncomputable abbrev abSheafify
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : HasSheafify J AddCommGrpCat.{w} :=
  hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}

private noncomputable abbrev smallArrowLimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] (U : Cᵒᵖ) :
    HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
      AddCommGrpCat.{w} :=
  HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _

attribute [local instance] abSheafify smallArrowLimits

private noncomputable abbrev abLocallyBijective
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
    (A := AddCommGrpCat.{w})

attribute [local instance] abLocallyBijective

private theorem abForgetLimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) :
    PreservesFiniteLimits (sheafCompose J (forget AddCommGrpCat.{w})) := by
  have : PreservesFiniteLimits
      (sheafCompose J (forget AddCommGrpCat.{w}) ⋙ sheafToPresheaf J (Type w)) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{w} ⋙
      (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{w})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type w))

attribute [local instance] abForgetLimits

/-- Recognize algebra-valued sheaves on an essentially small site without imposing
an inequality between the site universes and the value universe. -/
private theorem sheaf_of_underlying
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {A : Type*} [Category.{w} A]
    [HasLimitsOfSize.{w, w} A] (U : A ⥤ Type w)
    [PreservesLimitsOfSize.{w, w} U] [U.ReflectsIsomorphisms]
    (P : Cᵒᵖ ⥤ A) (h : Presheaf.IsSheaf J (P ⋙ U)) : Presheaf.IsSheaf J P := by
  let e := equivSmallModel.{w} C
  let K := e.inverse.inducedTopology J
  have : ReflectsLimitsOfSize.{w, w} U := reflectsLimits_of_reflectsIsomorphisms
  have hs : Presheaf.IsSheaf K (e.inverse.op ⋙ P) :=
    Presheaf.isSheaf_of_isSheaf_comp K _ U
      (e.inverse.op_comp_isSheaf K J ⟨P ⋙ U, h⟩)
  have hs' := e.functor.op_comp_isSheaf J K ⟨_, hs⟩
  exact (Presheaf.isSheaf_of_iso_iff (Functor.isoWhiskerRight e.op.unitIso.symm P)).mp hs'

open CategoryTheory.MonoidalCategory
open SheafOfModules.GeometricConstruction

@[instance_reducible] private def ringStructure
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] (J : GrothendieckTopology C)
    (A : Sheaf J CommRingCat.{w}) :
    CommRingObj ((sheafCompose J (forget CommRingCat.{w})).obj A) where
  zero := ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (0 : A.obj.obj U))
             naturality := by
               intro X Y f
               ext x
               change (0 : A.obj.obj Y) = (A.obj.map f).hom _
               exact (map_zero _).symm }⟩
  add := ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : A.obj.obj U × A.obj.obj U ↦ x.1 + x.2)
            naturality := by
              intro X Y f
              ext x
              change A.obj.obj X × A.obj.obj X at x
              change (A.obj.map f).hom x.1 + (A.obj.map f).hom x.2 =
                (A.obj.map f).hom (x.1 + x.2)
              exact (map_add _ _ _).symm }⟩
  neg := ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : A.obj.obj U ↦ -x)
            naturality := by
              intro X Y f
              ext x
              change A.obj.obj X at x
              change -(A.obj.map f).hom x = (A.obj.map f).hom (-x)
              exact (map_neg _ _).symm }⟩
  one := ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (1 : A.obj.obj U))
            naturality := by
               intro X Y f
               ext x
               change (1 : A.obj.obj Y) = (A.obj.map f).hom _
               exact (map_one _).symm }⟩
  mul := ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : A.obj.obj U × A.obj.obj U ↦ x.1 * x.2)
            naturality := by
              intro X Y f
              ext x
              change A.obj.obj X × A.obj.obj X at x
              change (A.obj.map f).hom x.1 * (A.obj.map f).hom x.2 =
                (A.obj.map f).hom (x.1 * x.2)
              exact (map_mul _ _ _).symm }⟩
  zero_add := by
    ext U x
    change PUnit × A.obj.obj U at x
    change (0 : A.obj.obj U) + x.2 = x.2
    exact zero_add x.2
  add_zero := by
    ext U x
    change A.obj.obj U × PUnit at x
    change (x.1 : A.obj.obj U) + 0 = x.1
    exact add_zero x.1
  add_assoc := by
    ext U x
    change (A.obj.obj U × A.obj.obj U) × A.obj.obj U at x
    change (x.1.1 : A.obj.obj U) + x.1.2 + x.2 = x.1.1 + (x.1.2 + x.2)
    exact add_assoc x.1.1 x.1.2 x.2
  left_neg := by
    ext U x
    change A.obj.obj U at x
    change -(x : A.obj.obj U) + x = 0
    exact neg_add_cancel x
  right_neg := by
    ext U x
    change A.obj.obj U at x
    change (x : A.obj.obj U) + -x = 0
    exact add_neg_cancel x
  add_comm := by
    ext U x
    change A.obj.obj U × A.obj.obj U at x
    change (x.2 : A.obj.obj U) + x.1 = x.1 + x.2
    exact add_comm x.2 x.1
  one_mul := by
    ext U x
    change PUnit × A.obj.obj U at x
    change (1 : A.obj.obj U) * x.2 = x.2
    exact one_mul x.2
  mul_one := by
    ext U x
    change A.obj.obj U × PUnit at x
    change (x.1 : A.obj.obj U) * 1 = x.1
    exact mul_one x.1
  mul_assoc := by
    ext U x
    change (A.obj.obj U × A.obj.obj U) × A.obj.obj U at x
    change (x.1.1 : A.obj.obj U) * x.1.2 * x.2 = x.1.1 * (x.1.2 * x.2)
    exact mul_assoc x.1.1 x.1.2 x.2
  mul_comm := by
    ext U x
    change A.obj.obj U × A.obj.obj U at x
    change (x.2 : A.obj.obj U) * x.1 = x.1 * x.2
    exact mul_comm x.2 x.1
  mul_add := by
    ext U x
    change A.obj.obj U × (A.obj.obj U × A.obj.obj U) at x
    change (x.1 : A.obj.obj U) * (x.2.1 + x.2.2) = x.1 * x.2.1 + x.1 * x.2.2
    exact mul_add x.1 x.2.1 x.2.2
  add_mul := by
    ext U x
    change (A.obj.obj U × A.obj.obj U) × A.obj.obj U at x
    change ((x.1.1 : A.obj.obj U) + x.1.2) * x.2 = x.1.1 * x.2 + x.1.2 * x.2
    exact add_mul x.1.1 x.1.2 x.2

-- Sectionwise reconstruction follows `SheafRingObjectReconstruction`, with the
-- sheaf condition checked on a small model to retain independent site universes.
noncomputable section RingReconstruction

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
private abbrev sadd
    (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) (a b : R.X.obj.obj U) : R.X.obj.obj U :=
  (AddMonObj.add (X := R.X)).hom.app U (a, b)
private abbrev szero
    (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) : R.X.obj.obj U :=
  (AddMonObj.zero (X := R.X)).hom.app U PUnit.unit
private abbrev sneg
    (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) (a : R.X.obj.obj U) : R.X.obj.obj U :=
  (AddGrpObj.neg (X := R.X)).hom.app U a
private abbrev smul
    (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) (a b : R.X.obj.obj U) : R.X.obj.obj U :=
  (MonObj.mul (X := R.X)).hom.app U (a, b)
private abbrev sone
    (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) : R.X.obj.obj U :=
  (MonObj.one (X := R.X)).hom.app U PUnit.unit

private abbrev sectionAddGroup
    (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) : AddCommGroup (R.X.obj.obj U) where
  add := sadd R U
  zero := szero R U
  neg := sneg R U
  add_assoc a b c := congrArg (fun f => f.hom.app U ((a, b), c))
    (AddMonObj.add_assoc R.X)
  zero_add a := congrArg (fun f => f.hom.app U (PUnit.unit, a))
    (AddMonObj.zero_add R.X)
  add_zero a := congrArg (fun f => f.hom.app U (a, PUnit.unit))
    (AddMonObj.add_zero R.X)
  add_comm a b := (congrArg (fun f => f.hom.app U (a, b))
    (IsCommAddMonObj.add_comm R.X)).symm
  neg_add_cancel a := congrArg (fun f => f.hom.app U a) (AddGrpObj.left_neg R.X)
  nsmul := @nsmulRec _ ⟨szero R U⟩ ⟨sadd R U⟩
  zsmul := @zsmulRec _ ⟨szero R U⟩ ⟨sadd R U⟩ ⟨sneg R U⟩
    (@nsmulRec _ ⟨szero R U⟩ ⟨sadd R U⟩)

private abbrev sectionMonoid
    (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) : CommMonoid (R.X.obj.obj U) where
  mul := smul R U
  one := sone R U
  mul_assoc a b c := congrArg (fun f => f.hom.app U ((a, b), c))
    (MonObj.mul_assoc R.X)
  one_mul a := congrArg (fun f => f.hom.app U (PUnit.unit, a))
    (MonObj.one_mul R.X)
  mul_one a := congrArg (fun f => f.hom.app U (a, PUnit.unit))
    (MonObj.mul_one R.X)
  mul_comm a b := (congrArg (fun f => f.hom.app U (a, b))
    (IsCommMonObj.mul_comm R.X)).symm

private abbrev sectionCommRing
    (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) : CommRing (R.X.obj.obj U) := by
  letI := sectionAddGroup R U
  letI := sectionMonoid R U
  exact {
    left_distrib := fun a b c => congrArg (fun f => f.hom.app U (a, (b, c)))
      (RingObj.mul_add R.X)
    right_distrib := fun a b c => congrArg (fun f => f.hom.app U ((a, b), c))
      (RingObj.add_mul R.X)
    mul_zero := by
      intro a
      have h : a * (0 + 0) = a * 0 + a * 0 :=
        congrArg (fun f => f.hom.app U (a, (0, 0))) (RingObj.mul_add R.X)
      simpa using h
    zero_mul := by
      intro a
      have h : (0 + 0) * a = 0 * a + 0 * a :=
        congrArg (fun f => f.hom.app U ((0, 0), a)) (RingObj.add_mul R.X)
      simpa using h }

private def reconstructedPresheaf
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
    (R : CommRingObjCat (Sheaf J (Type (w)))) :
    Cᵒᵖ ⥤ CommRingCat.{w} where
  obj U := @CommRingCat.of (R.X.obj.obj U) (sectionCommRing R U)
  map {U V} f := by
    letI := sectionCommRing R U
    letI := sectionCommRing R V
    exact CommRingCat.ofHom {
      toFun := R.X.obj.map f
      map_zero' := (congrArg (fun g => g PUnit.unit)
        ((AddMonObj.zero (X := R.X)).hom.naturality f)).symm
      map_one' := (congrArg (fun g => g PUnit.unit)
        ((MonObj.one (X := R.X)).hom.naturality f)).symm
      map_add' := fun a b => (congrArg (fun g => g (a, b))
        ((AddMonObj.add (X := R.X)).hom.naturality f)).symm
      map_mul' := fun a b => (congrArg (fun g => g (a, b))
        ((MonObj.mul (X := R.X)).hom.naturality f)).symm }
  map_id U := by
    ext x
    exact congrArg (fun g => g x) (R.X.obj.map_id U)
  map_comp f g := by
    ext x
    exact congrArg (fun k => k x) (R.X.obj.map_comp f g)

end RingReconstruction

private def ringSheaf
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : CommRingObjCat (Sheaf J (Type w))) :
    Sheaf J CommRingCat.{w} :=
  ⟨reconstructedPresheaf R,
    sheaf_of_underlying (forget CommRingCat.{w}) _ R.X.property⟩

private def imageRing
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [L.Braided]
    (R : Sheaf J CommRingCat.{w}) : Sheaf K CommRingCat.{w} := by
  let X := (sheafCompose J (forget CommRingCat.{w})).obj R
  letI := ringStructure J R
  letI := Adjunction.transportedRing L X
  exact ringSheaf ⟨L.obj X⟩

private theorem algebraic_presentation_exists
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{w}) :
    ∃ S : Sheaf K CommRingCat.{w}, Nonempty (SheafOfModules.AlgebraicInverseImage L R S) := by
  let : L.Braided := Functor.Braided.ofChosenFiniteProducts L
  let S := imageRing L R
  let d : rset S ⟶ L.obj (rset R) := 𝟙 _
  have ha : ringAdd S ≫ d = (d ⊗ₘ d) ≫ Functor.LaxMonoidal.μ L _ _ ≫
      L.map (ringAdd R) := by
    simp only [d, Category.comp_id, tensorHom_id]
    rfl
  have hm : letI := ringMonoid R
            letI := ringMonoid S
            letI := L.monObjObj (rset R)
            IsMonHom d := by
    let := ringMonoid R
    let := ringMonoid S
    let := L.monObjObj (rset R)
    constructor
    · simp only [d, Category.comp_id]
    · simp only [d, Category.comp_id, tensorHom_id]
      rfl
  let F := imageFunctor L R S d ha hm
  have hAdd (T : Sheaf J (Type w))
      (a b t : T ⟶ rset R)
      (ht : ∀ U x, t.hom.app U x =
        @Add.add (R.obj.obj U) inferInstance (a.hom.app U x) (b.hom.app U x))
      (V : Dᵒᵖ) (x : (L.obj T).obj.obj V) :
      (L.map t).hom.app V x =
        @Add.add (S.obj.obj V) inferInstance
          ((L.map a).hom.app V x) ((L.map b).hom.app V x) := by
    have he : t = CartesianMonoidalCategory.lift a b ≫ ringAdd R := by
      ext U y
      exact ht U y
    rw [he, L.map_comp, ← Functor.Monoidal.lift_μ]
    rfl
  have hMAdd (M : SheafOfModules.{w} (base R)) (T : Sheaf J (Type w))
      (a b t : T ⟶ (mset R).obj M)
      (ht : ∀ U x, t.hom.app U x =
        @Add.add (M.val.obj U) inferInstance (a.hom.app U x) (b.hom.app U x))
      (V : Dᵒᵖ) (x : (L.obj T).obj.obj V) :
      (L.map t).hom.app V x =
        @Add.add ((F.obj M).val.obj V) inferInstance
          ((L.map a).hom.app V x) ((L.map b).hom.app V x) := by
    have he : t = CartesianMonoidalCategory.lift a b ≫ addition R M := by
      ext U y
      exact ht U y
    rw [he, L.map_comp, ← Functor.Monoidal.lift_μ]
    rfl
  refine ⟨S, ⟨{
    ringUnderlying := Iso.refl _
    ringAdd := hAdd
    ringMul := ?_
    ringZero := ?_
    ringOne := ?_
    modules := F
    moduleUnderlying := imageFunctorUnderlying L R S d ha hm
    moduleAdd := hMAdd
    moduleZero := ?_
    moduleSMul := ?_ }⟩⟩
  · intro T a b t ht V x
    have he : t = CartesianMonoidalCategory.lift a b ≫ ringMul R := by
      ext U y
      exact ht U y
    rw [he, L.map_comp, ← Functor.Monoidal.lift_μ]
    rfl
  · intro T a ha V x
    let := ringStructure J R
    have he : a = CartesianMonoidalCategory.toUnit T ≫
        AddMonObj.zero (X := rset R) := by
      ext U y
      exact ha U y
    rw [he, L.map_comp, ← Functor.Monoidal.toUnit_ε]
    rfl
  · intro T a ha V x
    have he : a = CartesianMonoidalCategory.toUnit T ≫ ringOne R := by
      ext U y
      exact ha U y
    rw [he, L.map_comp, ← Functor.Monoidal.toUnit_ε]
    rfl
  · intro M T a ha V x
    have he : a = CartesianMonoidalCategory.toUnit T ≫
        MonObj.one (X := (additiveObject R M).X) := by
      ext U y
      exact ha U y
    rw [he, L.map_comp, ← Functor.Monoidal.toUnit_ε]
    rfl
  · intro M T a b t ht V x
    have he : t = CartesianMonoidalCategory.lift a b ≫ action R M := by
      ext U y
      exact ht U y
    rw [he, L.map_comp, ← Functor.Monoidal.lift_μ]
    change _ = (imageAction L R S d M).hom.app V
      ((L.map a).hom.app V x, (L.map b).hom.app V x)
    simp only [imageAction, d, tensorHom_id]
    rfl

-- The same conjugation by `ULift.down` is used in `LocalizationInverseImageCoherence`.
end CategoryTheory.GeometricMorphism
