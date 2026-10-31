/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.NormalizedCoefficientDiagramSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

import all WeilConjectures.SecSmoothPurity.NormalizedKappaTransitionsSupplement
import all WeilConjectures.SecSmoothPurity.NormalizedScalarTensorTransitionsSupplement

/-! # Units and successive composition of strict coefficient comparisons

Source: Stacks, sites-modules.tex, Section 03EK and Tag 03EL; the seven agent
calculations in the DAG (blueprint: lem-pur-coefficient-comparisons-unit-composition).

Only the definition interface of StrictCoefficientComparisonCalculus is used.
Its downstream existence theorem is neither a hypothesis nor a proof input.
-/

set_option Elab.async false
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
universe w uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace CategoryTheory.CochainPullback.StrictCoefficient

attribute [local irreducible] scalarComp scalarUnit extensionAdjunction extensionFunctor
open SheafOfModules

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The multiplication and insertion formulas for the already constructed unit.
Source: Stacks 03EK, agent proof step 2
(blueprint: lem-pur-coefficient-comparisons-unit-composition). -/
def UnitMultiplication (B : Index ⥤ Sheaf J CommRingCat.{w}) : Prop :=
  ∀ (i : Index) (P : Complex (B.obj i)) (p : ℤ) (U : Cᵒᵖ)
    (c : (B.obj i).obj.obj U) (x : (P.X p).val.obj U),
    ((((diagramUnit B i).app P).hom.f p).val.app U
        (extensionTmul (B.map (𝟙 i)) (P.X p) U c x) = c • x) ∧
    ((((diagramUnit B i).app P).inv.f p).val.app U x =
      extensionTmul (B.map (𝟙 i)) (P.X p) U 1 x)

/-- Multiplication of the two scalar factors, and insertion of one for the inverse.
Source: Stacks 03EK, agent proof step 2
(blueprint: lem-pur-coefficient-comparisons-unit-composition). -/
def CompositionMultiplication (B : Index ⥤ Sheaf J CommRingCat.{w}) : Prop :=
  ∀ {i j k : Index} (a : i ⟶ j) (b : j ⟶ k) (P : Complex (B.obj i))
    (p : ℤ) (U : Cᵒᵖ) (c : (B.obj k).obj.obj U) (d : (B.obj j).obj.obj U)
    (x : (P.X p).val.obj U),
    ((((diagramComp B a b).app P).hom.f p).val.app U
        (extensionTmul (B.map b) ((extensionFunctor (B.map a)).obj (P.X p)) U c
          (extensionTmul (B.map a) (P.X p) U d x)) =
      extensionTmul (B.map (a ≫ b)) (P.X p) U (c * (B.map b).hom.app U d) x) ∧
    ((((diagramComp B a b).app P).inv.f p).val.app U
        (extensionTmul (B.map (a ≫ b)) (P.X p) U c x) =
      extensionTmul (B.map b) ((extensionFunctor (B.map a)).obj (P.X p)) U c
        (extensionTmul (B.map a) (P.X p) U 1 x))

/-- The scalar action unit and its inverse commute with every semilinear transition.
The map f is arbitrary, in particular it can be zero.
Source: Stacks 03EK, agent proof step 3
(blueprint: lem-pur-coefficient-comparisons-unit-composition). -/
def UnitStrictness (B : Index ⥤ Sheaf J CommRingCat.{w}) : Prop :=
  ∀ {i j : Index} (r : i ⟶ j) (P : Complex (B.obj i)) (Q : Complex (B.obj j))
    (f : (extend (B.map r)).obj P ⟶ Q),
    ((extend (B.map r)).map ((diagramUnit B i).app P).hom ≫ f =
      squareArrow B (𝟙 i) (𝟙 j) r r (CategoryTheory.Prod.hom_ext
        (Subsingleton.elim _ _) (Subsingleton.elim _ _)) P Q f ≫
        ((diagramUnit B j).app Q).hom) ∧
    ((extend (B.map r)).map ((diagramUnit B i).app P).inv ≫
        squareArrow B (𝟙 i) (𝟙 j) r r (CategoryTheory.Prod.hom_ext
        (Subsingleton.elim _ _) (Subsingleton.elim _ _)) P Q f =
      f ≫ ((diagramUnit B j).app Q).inv)

/-- Successive transport of an arbitrary semilinear map through two coefficient squares.
This is a composite of the recorded square transports, with no chosen transition.
Source: Stacks 03EK, agent proof step 3
(blueprint: lem-pur-coefficient-comparisons-unit-composition). -/
def twiceSquareArrow (B : Index ⥤ Sheaf J CommRingCat.{w})
    {i j k i' j' k' : Index} (a : i ⟶ j) (b : j ⟶ k)
    (a' : i' ⟶ j') (b' : j' ⟶ k') (r : i ⟶ i') (s : j ⟶ j') (t : k ⟶ k')
    (P : Complex (B.obj i)) (Q : Complex (B.obj i'))
    (f : (extend (B.map r)).obj P ⟶ Q) :
    (extend (B.map t)).obj ((extend (B.map b)).obj ((extend (B.map a)).obj P)) ⟶
      (extend (B.map b')).obj ((extend (B.map a')).obj Q) :=
  squareArrow B b b' s t (CategoryTheory.Prod.hom_ext
        (Subsingleton.elim _ _) (Subsingleton.elim _ _))
    ((extend (B.map a)).obj P) ((extend (B.map a')).obj Q)
    (squareArrow B a a' r s (CategoryTheory.Prod.hom_ext
        (Subsingleton.elim _ _) (Subsingleton.elim _ _)) P Q f)

/-- The multiplication associator and its inverse commute with all semilinear transitions.
All squares commute because the coefficient/sequence index is a thin category.
Source: Stacks 03EK, agent proof step 3
(blueprint: lem-pur-coefficient-comparisons-unit-composition). -/
def CompositionStrictness (B : Index ⥤ Sheaf J CommRingCat.{w}) : Prop :=
  ∀ {i j k i' j' k' : Index} (a : i ⟶ j) (b : j ⟶ k)
    (a' : i' ⟶ j') (b' : j' ⟶ k') (r : i ⟶ i') (s : j ⟶ j') (t : k ⟶ k')
    (P : Complex (B.obj i)) (Q : Complex (B.obj i'))
    (f : (extend (B.map r)).obj P ⟶ Q),
    ((extend (B.map t)).map ((diagramComp B a b).app P).hom ≫
        squareArrow B (a ≫ b) (a' ≫ b') r t (CategoryTheory.Prod.hom_ext
        (Subsingleton.elim _ _) (Subsingleton.elim _ _)) P Q f =
      twiceSquareArrow B a b a' b' r s t P Q f ≫ ((diagramComp B a' b').app Q).hom) ∧
    ((extend (B.map t)).map ((diagramComp B a b).app P).inv ≫
        twiceSquareArrow B a b a' b' r s t P Q f =
      squareArrow B (a ≫ b) (a' ≫ b') r t (CategoryTheory.Prod.hom_ext
        (Subsingleton.elim _ _) (Subsingleton.elim _ _)) P Q f ≫
        ((diagramComp B a' b').app Q).inv)

private abbrev sectionModule (A : Sheaf J CommRingCat.{w})
    (M : Modules A) (U : Cᵒᵖ) : Module (A.obj.obj U) (M.val.obj U) :=
  (M.val.obj U).isModule

attribute [local instance] sectionModule

open KappaCalculation

private def scalarUnitAlong (A : Sheaf J CommRingCat.{w})
    (a : A ⟶ A) (ha : a = 𝟙 A) : extend a ≅ 𝟭 (Complex A) :=
  NatIso.mapHomologicalComplex
    (Adjunction.leftAdjointUniq (F := extensionFunctor a)
      (F' := 𝟭 (Modules A)) (G := 𝟭 (Modules A))
      ((extensionAdjunction a).ofNatIsoRight
        (SheafOfModules.systemScalarRestrictionUnit a ha)) Adjunction.id) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (Modules A) (.up ℤ)

private theorem scalarUnitAlong_eq_transport (A : Sheaf J CommRingCat.{w})
    (a : A ⟶ A) (ha : a = 𝟙 A) :
    eqToIso (congrArg (fun t ↦ extend t) ha) ≪≫ scalarUnit A =
      scalarUnitAlong A a ha := by
  subst a
  rw [eqToIso_refl, Iso.refl_trans]
  unfold scalarUnitAlong scalarUnit
  rfl

attribute [local irreducible] scalarUnitAlong

private theorem scalarUnitAlong_value (A : Sheaf J CommRingCat.{w})
    (a : A ⟶ A) (ha : a = 𝟙 A)
    (P : Complex A) (p : ℤ) (U : Cᵒᵖ) (c : A.obj.obj U) (x : (P.X p).val.obj U) :
    ((((scalarUnitAlong A a ha).app P).hom.f p).val.app U
      (extensionTmul a (P.X p) U c x)) = c • x := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((extensionAdjunction a).ofNatIsoRight
      (SheafOfModules.systemScalarRestrictionUnit a ha)) Adjunction.id (P.X p)
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  have hx := congrArg (fun g : P.X p ⟶ P.X p ↦ g.val.app U x) h
  change (((extensionAdjunction a).homEquiv _ _
    ((Adjunction.leftAdjointUniq
      ((extensionAdjunction a).ofNatIsoRight
        (SheafOfModules.systemScalarRestrictionUnit a ha))
      Adjunction.id).hom.app (P.X p))).val.app U x) = x at hx
  rw [Adjunction.homEquiv_unit] at hx
  change ((Adjunction.leftAdjointUniq
    ((extensionAdjunction a).ofNatIsoRight
      (SheafOfModules.systemScalarRestrictionUnit a ha))
    Adjunction.id).hom.app (P.X p)).val.app U
      (((extensionAdjunction a).unit.app (P.X p)).val.app U x) = x at hx
  rw [extension_unit] at hx
  unfold scalarUnitAlong
  dsimp only [Iso.trans_hom, NatIso.mapHomologicalComplex,
    NatTrans.mapHomologicalComplex, Functor.mapHomologicalComplexIdIso]
  erw [extension_smul, map_smul]
  exact congrArg (fun z ↦ c • z) hx

private theorem diagramUnit_eq_along (B : Index ⥤ Sheaf J CommRingCat.{w})
    (i : Index) :
    diagramUnit B i = scalarUnitAlong (B.obj i) (B.map (𝟙 i)) (B.map_id i) := by
  unfold diagramUnit
  exact scalarUnitAlong_eq_transport (B.obj i) (B.map (𝟙 i)) (B.map_id i)

private theorem unitIso_value_congr (A : Sheaf J CommRingCat.{w})
    (a : A ⟶ A) (e f : extend a ≅ 𝟭 (Complex A)) (h : e = f)
    (P : Complex A) (p : ℤ) (U : Cᵒᵖ) (c : A.obj.obj U) (x : (P.X p).val.obj U) :
    (((e.app P).hom.f p).val.app U (extensionTmul a (P.X p) U c x)) =
    (((f.app P).hom.f p).val.app U (extensionTmul a (P.X p) U c x)) := by
  subst f
  rfl

private theorem diagramUnit_value (B : Index ⥤ Sheaf J CommRingCat.{w})
    (i : Index) (P : Complex (B.obj i)) (p : ℤ) (U : Cᵒᵖ)
    (c : (B.obj i).obj.obj U) (x : (P.X p).val.obj U) :
    ((((diagramUnit B i).app P).hom.f p).val.app U
      (extensionTmul (B.map (𝟙 i)) (P.X p) U c x)) = c • x := by
  exact (unitIso_value_congr (B.obj i) (B.map (𝟙 i)) (diagramUnit B i)
    (scalarUnitAlong (B.obj i) (B.map (𝟙 i)) (B.map_id i)) (diagramUnit_eq_along B i)
      P p U c x).trans
    (scalarUnitAlong_value (B.obj i) (B.map (𝟙 i)) (B.map_id i) P p U c x)

private theorem unitIso_inv_value (A : Sheaf J CommRingCat.{w})
    (a : A ⟶ A) (e : extend a ≅ 𝟭 (Complex A)) (P : Complex A)
    (p : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U)
    (h : (((e.app P).hom.f p).val.app U (extensionTmul a (P.X p) U 1 x)) = x) :
    ((e.app P).inv.f p).val.app U x = extensionTmul a (P.X p) U 1 x := by
  calc
    _ = ((e.app P).inv.f p).val.app U
        (((e.app P).hom.f p).val.app U (extensionTmul a (P.X p) U 1 x)) :=
      congrArg (fun z ↦ ((e.app P).inv.f p).val.app U z) h.symm
    _ = _ := by
      exact congrArg (fun f ↦ f.val.app U (extensionTmul a (P.X p) U 1 x))
        (show (e.app P).hom.f p ≫ (e.app P).inv.f p = 𝟙 _ from
          congrArg (fun f ↦ f.f p) (e.app P).hom_inv_id)

private def UnitFormulas (A : Sheaf J CommRingCat.{w})
    (a : A ⟶ A) (e : extend a ≅ 𝟭 (Complex A)) : Prop :=
  ∀ (P : Complex A) (p : ℤ) (U : Cᵒᵖ) (c : A.obj.obj U) (x : (P.X p).val.obj U),
    ((((e.app P).hom.f p).val.app U (extensionTmul a (P.X p) U c x)) = c • x) ∧
    (((e.app P).inv.f p).val.app U x = extensionTmul a (P.X p) U 1 x)

private theorem unitAlongFormulas (A : Sheaf J CommRingCat.{w})
    (a : A ⟶ A) (ha : a = 𝟙 A) : UnitFormulas A a (scalarUnitAlong A a ha) := by
  intro P p U c x
  refine ⟨scalarUnitAlong_value A a ha P p U c x, ?_⟩
  apply unitIso_inv_value A a (scalarUnitAlong A a ha) P p U x
  simpa only [one_smul] using scalarUnitAlong_value A a ha P p U 1 x

private theorem unitDiagramFormulas (B : Index ⥤ Sheaf J CommRingCat.{w}) (i : Index) :
    UnitFormulas (B.obj i) (B.map (𝟙 i)) (diagramUnit B i) := by
  rw [diagramUnit_eq_along]
  exact unitAlongFormulas (B.obj i) (B.map (𝟙 i)) (B.map_id i)

private theorem unitMultiplication (B : Index ⥤ Sheaf J CommRingCat.{w}) :
    UnitMultiplication B := by
  intro i
  exact unitDiagramFormulas B i


private theorem compositionMultiplication (B : Index ⥤ Sheaf J CommRingCat.{w}) :
    CompositionMultiplication B := by
  intro i j k a b P p U c d x
  exact ⟨KappaCalculation.scalarComp_value _ _ _ _ P p U c d x,
    KappaCalculation.scalarComp_inv_value _ _ _ _ P p U c x⟩

attribute [local irreducible] extensionTmul squareArrow

private theorem extension₂_hom_ext {A B H : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) (b : B ⟶ H) (M : Modules A) (N : Modules H)
    {f g : (extensionFunctor b).obj ((extensionFunctor a).obj M) ⟶ N}
    (h : ∀ U x, f.val.app U (extensionTmul b ((extensionFunctor a).obj M) U 1
      (extensionTmul a M U 1 x)) =
      g.val.app U (extensionTmul b ((extensionFunctor a).obj M) U 1
        (extensionTmul a M U 1 x))) : f = g := by
  apply ((extensionAdjunction b).homEquiv _ _).injective
  apply ((extensionAdjunction a).homEquiv _ _).injective
  apply SheafOfModules.hom_ext
  ext U x
  change f.val.app U
    (((extensionAdjunction b).unit.app ((extensionFunctor a).obj M)).val.app U
      (((extensionAdjunction a).unit.app M).val.app U x)) =
    g.val.app U
      (((extensionAdjunction b).unit.app ((extensionFunctor a).obj M)).val.app U
        (((extensionAdjunction a).unit.app M).val.app U x))
  simpa only [extension_unit] using h U x

private theorem isoSquare_inverse {E F : Type*} [Category E] [Category F]
    (L : E ⥤ F) {P P' : E} {Q Q' : F} (u : P' ≅ P) (v : Q' ≅ Q)
    (f : L.obj P ⟶ Q) (g : L.obj P' ⟶ Q')
    (h : L.map u.hom ≫ f = g ≫ v.hom) : L.map u.inv ≫ g = f ≫ v.inv := by
  apply (cancel_mono v.hom).1
  simp only [Category.assoc]
  rw [← h]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id,
    Category.id_comp, Category.comp_id]

private def UnitStrictnessFor (B : Index ⥤ Sheaf J CommRingCat.{w})
    (u : ∀ i : Index, extend (B.map (𝟙 i)) ≅ 𝟭 (Complex (B.obj i))) : Prop :=
  ∀ {i j : Index} (r : i ⟶ j) (P : Complex (B.obj i)) (Q : Complex (B.obj j))
    (f : (extend (B.map r)).obj P ⟶ Q),
    ((extend (B.map r)).map ((u i).app P).hom ≫ f =
      squareArrow B (𝟙 i) (𝟙 j) r r (CategoryTheory.Prod.hom_ext
        (Subsingleton.elim _ _) (Subsingleton.elim _ _)) P Q f ≫
        ((u j).app Q).hom) ∧
    ((extend (B.map r)).map ((u i).app P).inv ≫
        squareArrow B (𝟙 i) (𝟙 j) r r (CategoryTheory.Prod.hom_ext
        (Subsingleton.elim _ _) (Subsingleton.elim _ _)) P Q f =
      f ≫ ((u j).app Q).inv)

private theorem unitFamily_value (B : Index ⥤ Sheaf J CommRingCat.{w})
    (u : ∀ i : Index, extend (B.map (𝟙 i)) ≅ 𝟭 (Complex (B.obj i)))
    (hu : ∀ i, UnitFormulas (B.obj i) (B.map (𝟙 i)) (u i))
    (i : Index) (P : Complex (B.obj i)) (p : ℤ) (U : Cᵒᵖ)
    (c : (B.obj i).obj.obj U) (x : (P.X p).val.obj U) :
    ((((u i).app P).hom.f p).val.app U
      (extensionTmul (B.map (𝟙 i)) (P.X p) U c x)) = c • x :=
  (hu i P p U c x).1

private theorem unitStrictnessFor (B : Index ⥤ Sheaf J CommRingCat.{w})
    (u : ∀ i : Index, extend (B.map (𝟙 i)) ≅ 𝟭 (Complex (B.obj i)))
    (hu : ∀ i, UnitFormulas (B.obj i) (B.map (𝟙 i)) (u i)) :
    UnitStrictnessFor B u := by
  intro i j r P Q f
  let hsq : (𝟙 i) ≫ r = r ≫ (𝟙 j) :=
    CategoryTheory.Prod.hom_ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  have hh : (extend (B.map r)).map ((u i).app P).hom ≫ f =
      squareArrow B (𝟙 i) (𝟙 j) r r hsq P Q f ≫ ((u j).app Q).hom := by
    apply HomologicalComplex.hom_ext
    intro p
    apply extension₂_hom_ext (B.map (𝟙 i)) (B.map r) (P.X p)
    intro U x
    change (f.f p).val.app U
        (((extensionFunctor (B.map r)).map (((u i).app P).hom.f p)).val.app U
          (extensionTmul (B.map r) ((extensionFunctor (B.map (𝟙 i))).obj (P.X p)) U 1
            (extensionTmul (B.map (𝟙 i)) (P.X p) U 1 x))) =
      (((u j).app Q).hom.f p).val.app U
        ((squareArrow B (𝟙 i) (𝟙 j) r r hsq P Q f).f p |>.val.app U <|
          extensionTmul (B.map r) ((extensionFunctor (B.map (𝟙 i))).obj (P.X p)) U 1
            (extensionTmul (B.map (𝟙 i)) (P.X p) U 1 x))
    erw [extension_map, unitFamily_value B u hu, one_smul, squareArrow_value,
      map_one, one_mul, unitFamily_value B u hu, one_smul]
    change (f.f p).val.app U (extensionTmul (B.map r) (P.X p) U 1 x) =
      (f.f p).val.app U (((extensionAdjunction (B.map r)).unit.app (P.X p)).val.app U x)
    rw [extension_unit]
  exact ⟨hh, isoSquare_inverse (extend (B.map r)) ((u i).app P)
    ((u j).app Q) f (squareArrow B (𝟙 i) (𝟙 j) r r hsq P Q f) hh⟩


private theorem unitStrictness (B : Index ⥤ Sheaf J CommRingCat.{w}) :
    UnitStrictness B :=
  unitStrictnessFor B (diagramUnit B) (unitDiagramFormulas B)

private theorem extension₃_hom_ext {A B H T : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) (b : B ⟶ H) (c : H ⟶ T) (M : Modules A) (N : Modules T)
    {f g : (extensionFunctor c).obj
      ((extensionFunctor b).obj ((extensionFunctor a).obj M)) ⟶ N}
    (h : ∀ U x, f.val.app U
      (extensionTmul c ((extensionFunctor b).obj ((extensionFunctor a).obj M)) U 1
        (extensionTmul b ((extensionFunctor a).obj M) U 1 (extensionTmul a M U 1 x))) =
      g.val.app U
      (extensionTmul c ((extensionFunctor b).obj ((extensionFunctor a).obj M)) U 1
        (extensionTmul b ((extensionFunctor a).obj M) U 1 (extensionTmul a M U 1 x)))) :
    f = g := by
  apply ((extensionAdjunction c).homEquiv _ _).injective
  apply extension₂_hom_ext a b M
  intro U x
  change f.val.app U (((extensionAdjunction c).unit.app _).val.app U _) =
    g.val.app U (((extensionAdjunction c).unit.app _).val.app U _)
  simpa only [extension_unit] using h U x

private theorem compositionStrictness (B : Index ⥤ Sheaf J CommRingCat.{w}) :
    CompositionStrictness B := by
  intro i j k i' j' k' a b a' b' r s t P Q f
  have hh : (extend (B.map t)).map ((diagramComp B a b).app P).hom ≫
      squareArrow B (a ≫ b) (a' ≫ b') r t
        (CategoryTheory.Prod.hom_ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))
        P Q f =
      twiceSquareArrow B a b a' b' r s t P Q f ≫ ((diagramComp B a' b').app Q).hom := by
    ext p : 1
    apply extension₃_hom_ext (B.map a) (B.map b) (B.map t) (P.X p)
    intro U x
    dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    change ((squareArrow B (a ≫ b) (a' ≫ b') r t _ P Q f).f p).val.app U
        (((extensionFunctor (B.map t)).map (((diagramComp B a b).app P).hom.f p)).val.app U _) =
      (((diagramComp B a' b').app Q).hom.f p).val.app U
        ((twiceSquareArrow B a b a' b' r s t P Q f).f p |>.val.app U <|
          extensionTmul (B.map t)
            ((extensionFunctor (B.map b)).obj ((extensionFunctor (B.map a)).obj (P.X p)))
            U 1 (extensionTmul (B.map b) ((extensionFunctor (B.map a)).obj (P.X p))
              U 1 (extensionTmul (B.map a) (P.X p) U 1 x)))
    erw [extension_map, scalarComp_value, map_one, one_mul, squareArrow_value,
      map_one, one_mul]
    change _ = (((diagramComp B a' b').app Q).hom.f p).val.app U
      ((squareArrow B b b' s t _ ((extend (B.map a)).obj P)
        ((extend (B.map a')).obj Q) (squareArrow B a a' r s _ P Q f)).f p |>.val.app U <|
        extensionTmul (B.map t)
          ((extensionFunctor (B.map b)).obj ((extensionFunctor (B.map a)).obj (P.X p)))
          U 1 (extensionTmul (B.map b) ((extensionFunctor (B.map a)).obj (P.X p))
            U 1 (extensionTmul (B.map a) (P.X p) U 1 x)))
    erw [squareArrow_value, map_one, one_mul]
    dsimp only [KappaCalculation.semilinearSectionMap]
    change _ = (((diagramComp B a' b').app Q).hom.f p).val.app U
      (extensionTmul (B.map b') ((extensionFunctor (B.map a')).obj (Q.X p)) U 1
        (((squareArrow B a a' r s _ P Q f).f p).val.app U
          (((extensionAdjunction (B.map s)).unit.app _).val.app U _)))
    erw [extension_unit, squareArrow_value, map_one, one_mul]
    simpa only [map_one, one_mul, diagramComp, Iso.app_hom, semilinearSectionMap] using
      (scalarComp_value (B.map a') (B.map b') (B.map (a' ≫ b')) (B.map_comp a' b')
        Q p U 1 1 ((semilinearSectionMap (B.map r) f p).hom.app U x)).symm
  exact ⟨hh, isoSquare_inverse (extend (B.map t)) ((diagramComp B a b).app P)
    ((diagramComp B a' b').app Q)
    (squareArrow B (a ≫ b) (a' ≫ b') r t
      (CategoryTheory.Prod.hom_ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)) P Q f)
    (twiceSquareArrow B a b a' b' r s t P Q f) hh⟩

open ScalarCalculation


private theorem totalExtension_hom_ext {A B : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) (P Q : Complex A) (n : ℤ) (M : Modules B)
    {f g : (extensionFunctor a).obj ((total P Q).X n) ⟶ M}
    (h : ∀ p q (hpq : p + q = n) U x y,
      f.val.app U (extensionTmul a ((total P Q).X n) U 1
        (totalPure P Q p q n hpq U x y)) =
      g.val.app U (extensionTmul a ((total P Q).X n) U 1
        (totalPure P Q p q n hpq U x y))) : f = g := by
  apply ((extensionAdjunction a).homEquiv _ _).injective
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply tensor_hom_ext
  intro U x y
  change f.val.app U
    (((extensionAdjunction a).unit.app ((total P Q).X n)).val.app U
      (totalPure P Q p q n hpq U x y)) =
    g.val.app U
      (((extensionAdjunction a).unit.app ((total P Q).X n)).val.app U
        (totalPure P Q p q n hpq U x y))
  simpa only [extension_unit] using h p q hpq U x y

private theorem tensorLaws (B : Index ⥤ Sheaf J CommRingCat.{w})
    (z : ∀ {i j : Index} (a : i ⟶ j), Comparison (extensionPullback (B.map a))) :
    TensorLaws B z := by
  constructor
  · intro i P Q
    apply Iso.ext
    ext n : 1
    apply totalExtension_hom_ext (B.map (𝟙 i)) P Q n
    intro p q hpq U x y
    change ((tensorTotalMap ((diagramUnit B i).app P).hom
      ((diagramUnit B i).app Q).hom).f n).val.app U
        (((tensorComparison (extensionPullback (B.map (𝟙 i))) (z (𝟙 i)) P Q).hom.f n).val.app U _)
       = _
    erw [scalarTotal_hom, totalMap_pure, diagramUnit_value, diagramUnit_value,
      one_smul, one_smul, diagramUnit_value, one_smul]
    rfl
  · intro i j k a b P Q
    apply Iso.ext
    ext n : 1
    apply nestedTotal_hom_ext (B.map a) (B.map b) P Q n
    intro p q hpq U x y
    change ((tensorTotalMap ((diagramComp B a b).app P).hom
      ((diagramComp B a b).app Q).hom).f n).val.app U
        (((tensorComparison (extensionPullback (B.map b)) (z b)
          ((extend (B.map a)).obj P) ((extend (B.map a)).obj Q)).hom.f n).val.app U
          (((extensionFunctor (B.map b)).map
            ((tensorComparison (extensionPullback (B.map a)) (z a) P Q).hom.f n)).val.app U _)) =
      ((tensorComparison (extensionPullback (B.map (a ≫ b))) (z (a ≫ b)) P Q).hom.f n).val.app U
        ((((diagramComp B a b).app (total P Q)).hom.f n).val.app U _)
    erw [extension_map, scalarTotal_hom, scalarTotal_hom, totalMap_pure,
      scalarComp_value, scalarComp_value, map_one, one_mul,
      scalarComp_value, map_one, one_mul, scalarTotal_hom]

private def compDegreeMap (B : Index ⥤ Sheaf J CommRingCat.{w})
    {i j l : Index} (a : i ⟶ j) (b : j ⟶ l) (P : Complex (B.obj i)) (p : ℤ) :
    (extensionFunctor (B.map b)).obj ((extensionFunctor (B.map a)).obj (P.X p)) ⟶
      (extensionFunctor (B.map (a ≫ b))).obj (P.X p) :=
  ((diagramComp B a b).app P).hom.f p

private theorem insertion_unit_general (A : Sheaf J CommRingCat.{w})
    (a : A ⟶ A) (e : extend a ≅ 𝟭 (Complex A)) (he : UnitFormulas A a e)
    (P : Complex A) (p : ℤ) :
    insertion a (P.X p) ≫ (underlying A).map ((e.app P).hom.f p) = 𝟙 _ := by
  apply Sheaf.hom_ext
  ext U x
  change ((e.app P).hom.f p).val.app U
    (((extensionAdjunction a).unit.app (P.X p)).val.app U x) = x
  erw [extension_unit]
  exact (he P p U 1 x).1.trans (one_smul _ _)

private theorem insertion_comp (B : Index ⥤ Sheaf J CommRingCat.{w})
    {i j k : Index} (a : i ⟶ j) (b : j ⟶ k) (P : Complex (B.obj i)) (p : ℤ) :
    insertion (B.map a) (P.X p) ≫
      insertion (B.map b) ((extensionFunctor (B.map a)).obj (P.X p)) ≫
      (underlying (B.obj k)).map (compDegreeMap B a b P p) =
      insertion (B.map (a ≫ b)) (P.X p) := by
  apply Sheaf.hom_ext
  ext U x
  change (((diagramComp B a b).app P).hom.f p).val.app U
    (((extensionAdjunction (B.map b)).unit.app _).val.app U
      (((extensionAdjunction (B.map a)).unit.app _).val.app U x)) =
    (((extensionAdjunction (B.map (a ≫ b))).unit.app _).val.app U x)
  erw [extension_unit, extension_unit, extension_unit]
  change (((scalarComp (B.map a) (B.map b) (B.map (a ≫ b))
    (B.map_comp a b)).hom.app P).f p).val.app U
      (extensionTmul (B.map b) ((extensionFunctor (B.map a)).obj (P.X p)) U 1
        (extensionTmul (B.map a) (P.X p) U 1 x)) =
    extensionTmul (B.map (a ≫ b)) (P.X p) U 1 x
  erw [scalarComp_value, map_one, one_mul]

private def pulledUnitMapFor (d : Diagram (J := J) (K := K)) (i : Index)
    (u : extend (d.S.map (𝟙 i)) ≅ 𝟭 (Complex (d.S.obj i)))
    (P : Complex (d.R.obj i)) (p : ℤ) :
    (extensionFunctor (d.S.map (𝟙 i))).obj ((d.L i).obj (P.X p)) ⟶
      (d.L i).obj (P.X p) :=
  (u.app ((pull (d.ringed i)).obj P)).hom.f p

private def PulledUnitInsertionFor (d : Diagram (J := J) (K := K)) (i : Index)
    (u : extend (d.S.map (𝟙 i)) ≅ 𝟭 (Complex (d.S.obj i))) : Prop :=
  ∀ (P : Complex (d.R.obj i)) (p : ℤ),
    insertion (d.S.map (𝟙 i)) ((d.L i).obj (P.X p)) ≫
      (underlying (d.S.obj i)).map (pulledUnitMapFor d i u P p) = 𝟙 _

private theorem pulledUnitInsertionFor (d : Diagram (J := J) (K := K)) (i : Index)
    (u : extend (d.S.map (𝟙 i)) ≅ 𝟭 (Complex (d.S.obj i)))
    (hu : UnitFormulas (d.S.obj i) (d.S.map (𝟙 i)) u) :
    PulledUnitInsertionFor d i u := by
  intro P p
  exact insertion_unit_general (d.S.obj i) (d.S.map (𝟙 i)) u hu
    ((pull (d.ringed i)).obj P) p

private def pulledCompDegreeMap (d : Diagram (J := J) (K := K))
    {i j l : Index} (a : i ⟶ j) (b : j ⟶ l) (P : Complex (d.R.obj i)) (p : ℤ) :
    (extensionFunctor (d.S.map b)).obj
      ((extensionFunctor (d.S.map a)).obj ((d.L i).obj (P.X p))) ⟶
    (extensionFunctor (d.S.map (a ≫ b))).obj ((d.L i).obj (P.X p)) :=
  compDegreeMap d.S a b ((pull (d.ringed i)).obj P) p

@[reassoc]
private theorem pulledInsertionComp (d : Diagram (J := J) (K := K))
    {i j l : Index} (a : i ⟶ j) (b : j ⟶ l) (P : Complex (d.R.obj i)) (p : ℤ) :
    insertion (d.S.map a) ((d.L i).obj (P.X p)) ≫
      insertion (d.S.map b) ((extensionFunctor (d.S.map a)).obj ((d.L i).obj (P.X p))) ≫
      (underlying (d.S.obj l)).map (pulledCompDegreeMap d a b P p) =
    insertion (d.S.map (a ≫ b)) ((d.L i).obj (P.X p)) := by
  erw [pulledCompDegreeMap]
  exact insertion_comp d.S a b ((pull (d.ringed i)).obj P) p

private def diagramGenerator (d : Diagram (J := J) (K := K))
    (k : ∀ i : Index, Comparison (d.ringed i)) (i : Index)
    {M : Modules (d.R.obj i)} {Z : Sheaf J (Type w)}
    (x : Z ⟶ (underlying (d.R.obj i)).obj M) :
    d.inverse.obj Z ⟶ (underlying (d.S.obj i)).obj ((d.L i).obj M) :=
  generator (d.ringed i) (k i) x

@[reassoc]
private theorem diagramGenerator_kappa (d : Diagram (J := J) (K := K))
    (k : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized k) {i j : Index} (a : i ⟶ j)
    (M : Modules (d.R.obj i)) (Z : Sheaf J (Type w))
    (x : Z ⟶ (underlying (d.R.obj i)).obj M) :
    diagramGenerator d k i x ≫ insertion (d.S.map a) ((d.L i).obj M) ≫
      (underlying (d.S.obj j)).map ((e.kappa a).hom.app M) =
    diagramGenerator d k j (x ≫ insertion (d.R.map a) M) := by
  exact kappa_generator d k e hn a M Z x

private theorem diagramGenerator_naturality (d : Diagram (J := J) (K := K))
    (k : ∀ i : Index, Comparison (d.ringed i)) (i : Index)
    {M N : Modules (d.R.obj i)} (b : M ⟶ N) {Z : Sheaf J (Type w)}
    (x : Z ⟶ (underlying (d.R.obj i)).obj M) :
    diagramGenerator d k i (x ≫ (underlying (d.R.obj i)).map b) =
      diagramGenerator d k i x ≫ (underlying (d.S.obj i)).map ((d.L i).map b) := by
  exact CategoryTheory.CochainPullback.generator_naturality (d.ringed i) (k i) b x


attribute [local irreducible] generator

private def KappaUnitFor (d : Diagram (J := J) (K := K)) (e : Comparisons d)
    (i : Index) (uR : extend (d.R.map (𝟙 i)) ≅ 𝟭 (Complex (d.R.obj i)))
    (uS : extend (d.S.map (𝟙 i)) ≅ 𝟭 (Complex (d.S.obj i))) : Prop :=
  ∀ (P : Complex (d.R.obj i)),
    e.kappaC (𝟙 i) P ≪≫ (pull (d.ringed i)).mapIso (uR.app P) =
      uS.app ((pull (d.ringed i)).obj P)

set_option maxHeartbeats 800000 in
-- The adjunction and generator calculation unfolds several module functors.
private theorem kappaUnitFor (d : Diagram (J := J) (K := K))
    (k : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized k) (i : Index)
    (uR : extend (d.R.map (𝟙 i)) ≅ 𝟭 (Complex (d.R.obj i)))
    (uS : extend (d.S.map (𝟙 i)) ≅ 𝟭 (Complex (d.S.obj i)))
    (hR : UnitFormulas (d.R.obj i) (d.R.map (𝟙 i)) uR)
    (hS : UnitFormulas (d.S.obj i) (d.S.map (𝟙 i)) uS) :
    KappaUnitFor d e i uR uS := by
  intro P
  apply Iso.ext
  ext p : 1
  apply ((extensionAdjunction (d.S.map (𝟙 i))).homEquiv _ _).injective
  apply pull_generator_hom_ext (d.ringed i) (k i) (P.X p)
  intro Z x
  change diagramGenerator d k i x ≫
      insertion (d.S.map (𝟙 i)) ((d.L i).obj (P.X p)) ≫
      (underlying (d.S.obj i)).map ((e.kappa (𝟙 i)).hom.app (P.X p)) ≫
      (underlying (d.S.obj i)).map ((d.L i).map ((uR.app P).hom.f p)) =
    diagramGenerator d k i x ≫
      insertion (d.S.map (𝟙 i)) ((d.L i).obj (P.X p)) ≫
      (underlying (d.S.obj i)).map (pulledUnitMapFor d i uS P p)
  try simp only [Category.assoc]
  erw [diagramGenerator_kappa_assoc d k e hn]
  erw [← diagramGenerator_naturality]
  simp only [Category.assoc]
  have hR' : x ≫ insertion (d.R.map (𝟙 i)) (P.X p) ≫
      (underlying (d.R.obj i)).map ((uR.app P).hom.f p) = x := by
    calc
      _ = x ≫ 𝟙 _ := congrArg (fun z ↦ x ≫ z)
        (insertion_unit_general (d.R.obj i) (d.R.map (𝟙 i)) uR hR P p)
      _ = x := Category.comp_id x
  calc
    _ = diagramGenerator d k i x :=
      congrArg (fun y ↦ diagramGenerator d k i y) hR'
    _ = _ := by
      symm
      calc
        _ = diagramGenerator d k i x ≫ 𝟙 _ :=
          congrArg (fun z ↦ diagramGenerator d k i x ≫ z)
            (pulledUnitInsertionFor d i uS hS P p)
        _ = _ := Category.comp_id _

private theorem kappa_unit (d : Diagram (J := J) (K := K))
    (k : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized k) (i : Index) :
    ∀ (P : Complex (d.R.obj i)),
      e.kappaC (𝟙 i) P ≪≫
        (pull (d.ringed i)).mapIso ((diagramUnit d.R i).app P) =
          (diagramUnit d.S i).app ((pull (d.ringed i)).obj P) :=
  kappaUnitFor d k e hn i (diagramUnit d.R i) (diagramUnit d.S i)
    (unitDiagramFormulas d.R i) (unitDiagramFormulas d.S i)

set_option maxHeartbeats 800000 in
-- Two adjunctions and their naturality maps require several module-functor unfoldings.
private theorem kappa_comp (d : Diagram (J := J) (K := K))
    (k : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized k) {i j l : Index} (a : i ⟶ j) (b : j ⟶ l)
    (P : Complex (d.R.obj i)) :
    (extend (d.S.map b)).mapIso (e.kappaC a P) ≪≫
      e.kappaC b ((extend (d.R.map a)).obj P) ≪≫
      (pull (d.ringed l)).mapIso ((diagramComp d.R a b).app P) =
    (diagramComp d.S a b).app ((pull (d.ringed i)).obj P) ≪≫ e.kappaC (a ≫ b) P := by
  apply Iso.ext
  ext p : 1
  apply ((extensionAdjunction (d.S.map b)).homEquiv _ _).injective
  apply ((extensionAdjunction (d.S.map a)).homEquiv _ _).injective
  apply pull_generator_hom_ext (d.ringed i) (k i) (P.X p)
  intro Z x
  change diagramGenerator d k i x ≫
      insertion (d.S.map a) ((d.L i).obj (P.X p)) ≫
      insertion (d.S.map b) ((extensionFunctor (d.S.map a)).obj ((d.L i).obj (P.X p))) ≫
      (underlying (d.S.obj l)).map
        ((extensionFunctor (d.S.map b)).map ((e.kappa a).hom.app (P.X p))) ≫
      (underlying (d.S.obj l)).map
        ((e.kappa b).hom.app ((extensionFunctor (d.R.map a)).obj (P.X p))) ≫
      (underlying (d.S.obj l)).map
        ((d.L l).map (compDegreeMap d.R a b P p)) =
    diagramGenerator d k i x ≫
      insertion (d.S.map a) ((d.L i).obj (P.X p)) ≫
      insertion (d.S.map b) ((extensionFunctor (d.S.map a)).obj ((d.L i).obj (P.X p))) ≫
      (underlying (d.S.obj l)).map
        (pulledCompDegreeMap d a b P p) ≫
      (underlying (d.S.obj l)).map ((e.kappa (a ≫ b)).hom.app (P.X p))
  have hnat := CategoryTheory.CochainPullback.insertion_naturality
    (d.S.map b) ((e.kappa a).hom.app (P.X p))
  erw [← reassoc_of% hnat]
  erw [diagramGenerator_kappa_assoc d k e hn a (P.X p) Z x]
  erw [diagramGenerator_kappa_assoc d k e hn b
    ((extensionFunctor (d.R.map a)).obj (P.X p)) Z
    (x ≫ insertion (d.R.map a) (P.X p))]
  erw [← diagramGenerator_naturality d k l (compDegreeMap d.R a b P p)
    ((x ≫ insertion (d.R.map a) (P.X p)) ≫
      insertion (d.R.map b) ((extensionFunctor (d.R.map a)).obj (P.X p)))]
  have hR : ((x ≫ insertion (d.R.map a) (P.X p)) ≫
      insertion (d.R.map b) ((extensionFunctor (d.R.map a)).obj (P.X p))) ≫
      (underlying (d.R.obj l)).map (compDegreeMap d.R a b P p) =
    x ≫ insertion (d.R.map (a ≫ b)) (P.X p) := by
    simpa only [Category.assoc] using
      congrArg (fun z ↦ x ≫ z) (insertion_comp d.R a b P p)
  erw [hR, pulledInsertionComp_assoc d a b P p]
  exact (diagramGenerator_kappa d k e hn (a ≫ b) (P.X p) Z x).symm


-- Assemble the degreewise scalar and total tensor equations.
/-- Unit and successive-composition laws, in the category of strict chain systems.
Source: Stacks 03EK and 03EL, and the seven agent calculations in the DAG
(blueprint: lem-pur-coefficient-comparisons-unit-composition).

Proof:
1. The normalized scalar, tensor and kappa formulas provide equality tests on
   generalized generators. Iterated scalar adjunctions test nested extensions;
   the total coproduct test and pure tensors test unbounded tensor total maps.
2. Identify the canonical unit with the adjoint-uniqueness unit along the same
   identity coefficient map. Its transpose is identity, which gives multiplication
   and the inverse insertion formula. The scalar composition formulas give the
   two multiplication formulas for successive extensions.
3. Test unit and composition strictness after two and three scalar adjunctions.
   Both routes apply the given semilinear map to the same inserted unit tensors.
   Cancel the comparison isomorphisms to obtain the inverse equations.
4. Test the tensor equations in each homogeneous summand on pure tensors.
   Both unit routes remove the inserted ones, and both composition routes give
   the same pair of tensors without a permutation or an extra sign.
5. Test kappa coherence after scalar adjunction and on generalized pullback
   generators. Normalization moves a generator through kappa; naturality moves
   it through the geometric pullback map. Multiplication removes the unit
   insertion or combines two successive insertions. For the unit calculation,
   first use arbitrary normalized units and then specialize to the canonical ones.
   Assemble the resulting isomorphism equalities, which also identify inverses.
   No exactness, flatness, boundedness or invertibility of transitions is used.
-/
theorem coefficientComparisonsUnitComposition (d : Diagram (J := J) (K := K))
    (k : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (_normalized : e.Normalized k)
    (_strict : e.KappaTransitionLaws ∧
      TensorTransitionLaws d.R e.sigmaR ∧ TensorTransitionLaws d.S e.sigmaS) :
    UnitMultiplication d.R ∧ UnitMultiplication d.S ∧
    CompositionMultiplication d.R ∧ CompositionMultiplication d.S ∧
    UnitStrictness d.R ∧ UnitStrictness d.S ∧
    CompositionStrictness d.R ∧ CompositionStrictness d.S ∧
    TensorLaws d.R e.sigmaR ∧ TensorLaws d.S e.sigmaS ∧
    (∀ (i : Index) (P : Complex (d.R.obj i)),
      e.kappaC (𝟙 i) P ≪≫
          (pull (d.ringed i)).mapIso ((diagramUnit d.R i).app P) =
        (diagramUnit d.S i).app ((pull (d.ringed i)).obj P)) ∧
    (∀ {i j l : Index} (a : i ⟶ j) (b : j ⟶ l) (P : Complex (d.R.obj i)),
      (extend (d.S.map b)).mapIso (e.kappaC a P) ≪≫
          e.kappaC b ((extend (d.R.map a)).obj P) ≪≫
          (pull (d.ringed l)).mapIso ((diagramComp d.R a b).app P) =
        (diagramComp d.S a b).app ((pull (d.ringed i)).obj P) ≪≫ e.kappaC (a ≫ b) P)  := by
  refine ⟨unitMultiplication d.R, unitMultiplication d.S,
    compositionMultiplication d.R, compositionMultiplication d.S,
    unitStrictness d.R, unitStrictness d.S, compositionStrictness d.R,
    compositionStrictness d.S, tensorLaws d.R e.sigmaR, tensorLaws d.S e.sigmaS,
    kappa_unit d k e _normalized, kappa_comp d k e _normalized⟩

end CategoryTheory.CochainPullback.StrictCoefficient
