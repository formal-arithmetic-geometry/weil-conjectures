/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulatedSupplement
public import WeilConjectures.Algebra.Homology.KFlatTotalTensorModelSupplement
public import Mathlib.CategoryTheory.Products.Associator
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Localization.Pi

/-!
# Normalized derived tensor constraints and additivity

Source: Stacks Project, sites-cohomology.tex, Tag 0FPT
(lemma-symmetric-monoidal-derived), lemma-tensor-product-K-flat and
 definition-derived-tor (blueprint: lem-pur-derived-tensor-additive-constraints).

The tensor and representative comparison are the published descent constructions.
The auxiliary definitions just specialize existing categories, tensor functors and
chain isomorphisms. The statements include the empty product and unbounded objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w i e z

open CategoryTheory CategoryTheory.Limits MonoidalCategory CategoryTheory.Functor

namespace SheafOfModules.DerivedTensorConstraints

attribute [local irreducible] SheafOfModules.monoidalCategory
  siteDerivedTensorIndependentCoefficients KFlatFixedTensor.representativeIso

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance 4000] SheafOfModules.monoidalCategory

-- Prefer the native complex tensor when elaborating chain-level formulas.
attribute [local instance 4000] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory


section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift Z ℤ]
  (T : A ⥤ B ⥤ Z) [∀ X, (T.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.map f) ℤ]

private def genericRightShift (b : ℤ) :
    ((𝟭 A).prod (shiftFunctor B b)) ⋙ Functor.uncurry.obj T ≅
      Functor.uncurry.obj T ⋙ shiftFunctor Z b := by
  refine NatIso.ofComponents (fun E ↦ ((T.obj E.1).commShiftIso b).app E.2) ?_
  intro E F f
  dsimp [Functor.uncurry, CategoryTheory.Functor.prod, Functor.comp]
  rw [Category.assoc]
  erw [((T.obj F.1).commShiftIso b).hom.naturality]
  rw [← Category.assoc, ← NatTrans.shift_app_comm]
  simp only [Functor.comp_map, CategoryTheory.Functor.map_comp, Category.assoc]
end

section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift Z ℤ]
  (T : A ⥤ B ⥤ Z) [∀ X, (T.flip.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.flip.map f) ℤ]

private def genericLeftShift (a : ℤ) :
    ((shiftFunctor A a).prod (𝟭 B)) ⋙ Functor.uncurry.obj T ≅
      Functor.uncurry.obj T ⋙ shiftFunctor Z a := by
  refine NatIso.ofComponents (fun E ↦ ((T.flip.obj E.2).commShiftIso a).app E.1) ?_
  intro E F f
  dsimp [Functor.uncurry, CategoryTheory.Functor.prod, Functor.comp]
  rw [Category.assoc]
  erw [← NatTrans.shift_app_comm (T.flip.map f.2) a F.1]
  rw [← Category.assoc]
  erw [((T.flip.obj E.2).commShiftIso a).hom.naturality]
  simp only [Functor.comp_map, CategoryTheory.Functor.map_comp, Category.assoc]
  rfl
end

section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift Z ℤ]
  (T : A ⥤ B ⥤ Z) [∀ X, (T.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.map f) ℤ]
  [∀ X, (T.flip.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.flip.map f) ℤ]

private def genericShiftPair (a b : ℤ) :
    ((shiftFunctor A a).prod (shiftFunctor B b)) ⋙ Functor.uncurry.obj T ≅
      Functor.uncurry.obj T ⋙ shiftFunctor Z (a + b) :=
  isoWhiskerLeft ((shiftFunctor A a).prod (𝟭 B)) (genericRightShift T b) ≪≫
    isoWhiskerRight (genericLeftShift T a) (shiftFunctor Z b) ≪≫
    isoWhiskerLeft (Functor.uncurry.obj T) (shiftFunctorAdd Z a b).symm

end

section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [HasShift B ℤ] [HasShift Z ℤ]

private def genericShiftConjugate (i : A ⥤ B) (K : A × A ⥤ B)
    (q : B ⥤ Z) [q.CommShift ℤ] (T : Z × Z ⥤ Z) (S : ℤ → A ⥤ A)
    (e : ∀ a, S a ⋙ i ⋙ q ≅ i ⋙ q ⋙ shiftFunctor Z a)
    (r : K ⋙ q ≅ ((i ⋙ q).prod (i ⋙ q)) ⋙ T) (a b : ℤ)
    (c : ((S a).prod (S b)) ⋙ K ≅ K ⋙ shiftFunctor B (a + b)) :
    ((i ⋙ q).prod (i ⋙ q)) ⋙ ((shiftFunctor Z a).prod (shiftFunctor Z b)) ⋙ T ≅
      ((i ⋙ q).prod (i ⋙ q)) ⋙ T ⋙ shiftFunctor Z (a + b) :=
  isoWhiskerRight (NatIso.prod (e a).symm (e b).symm) T ≪≫
    (isoWhiskerLeft ((S a).prod (S b)) r).symm ≪≫
    isoWhiskerRight c q ≪≫ isoWhiskerLeft K (q.commShiftIso (a + b)) ≪≫
    isoWhiskerRight r (shiftFunctor Z (a + b))
private theorem genericShiftConjugate_hom_app
    (i : A ⥤ B) (K : A × A ⥤ B) (q : B ⥤ Z) [q.CommShift ℤ]
    (T : Z × Z ⥤ Z) (S : ℤ → A ⥤ A)
    (e : ∀ a, S a ⋙ i ⋙ q ≅ i ⋙ q ⋙ shiftFunctor Z a)
    (r : K ⋙ q ≅ ((i ⋙ q).prod (i ⋙ q)) ⋙ T) (a b : ℤ)
    (c : ((S a).prod (S b)) ⋙ K ≅ K ⋙ shiftFunctor B (a + b)) (X Y : A) :
    (genericShiftConjugate i K q T S e r a b c).hom.app (X, Y) =
      T.map (Prod.mkHom ((e a).inv.app X) ((e b).inv.app Y)) ≫
        r.inv.app ((S a).obj X, (S b).obj Y) ≫ q.map (c.hom.app (X, Y)) ≫
        (q.commShiftIso (a + b)).hom.app (K.obj (X, Y)) ≫
        (shiftFunctor Z (a + b)).map (r.hom.app (X, Y)) := rfl

end

section
variable {A CC H Z : Type*} [Category* A] [Category* CC] [Category* H] [Category* Z]
  {q : CC ⥤ H} {Q : H ⥤ Z} {F : CC × CC ⥤ CC} {P : ObjectProperty H}

private def genericPresentationComparison (i : A ⥤ CC)
    (t : KFlatFixedTensor.TensorPresentation q Q F P)
    (h : ∀ X, P (q.obj (i.obj X))) :
    (i.prod i) ⋙ F ⋙ q ⋙ Q ≅ ((i ⋙ q ⋙ Q).prod (i ⋙ q ⋙ Q)) ⋙ t.derivedTensor :=
  isoWhiskerLeft (i.prod i) (isoWhiskerRight t.homotopyComparison Q).symm ≪≫
    isoWhiskerLeft ((P.lift (i ⋙ q) h).prod (P.lift (i ⋙ q) h)) t.resolvingComparison


end

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- The existing ordinary module-sheaf category.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev Modules := KFlatFixedTensor.Modules R

/-- The existing category of integer-indexed, unbounded cochain complexes.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev Complex := CochainComplex (Modules R) ℤ

/-- The native complex monoidal dictionary, named once for the public tensor formulas.
Source: Mathlib.Algebra.Homology.Monoidal
(blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev complexMonoidal : MonoidalCategory (Complex R) :=
  HomologicalComplex.monoidalCategory (Modules R) (.up ℤ)

/-- The native complex tensor data, shared by the public formulas and their proofs.
Source: Mathlib.Algebra.Homology.Monoidal
(blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev complexMonoidalStruct : MonoidalCategoryStruct (Complex R) :=
  HomologicalComplex.monoidalCategoryStruct (Modules R) (.up ℤ)

attribute [local instance 4001] complexMonoidal complexMonoidalStruct

/-- The resolving property on complexes, using the recorded K-flatness and flatness.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
def resolvingComplex : ObjectProperty (Complex R) := fun E ↦
  CochainComplex.IsKFlatIndependentCoefficients E ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (E.X n)

/-- The full subcategory of flat-term K-flat complex representatives.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev Model := (resolvingComplex R).FullSubcategory

/-- The same resolving property in the homotopy category.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
def resolvingHomotopy : ObjectProperty (HomotopyCategory (Modules R) (.up ℤ)) :=
  fun E ↦ resolvingComplex R E.as

variable [HasDerivedCategory.{w} (Modules R)]

/-- The existing derived category, with independent localization universe.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev D := DerivedCategory (Modules R)

/-- The fixed tensor from site-derived-tensor descent; no new tensor is selected.
Source: Stacks 06YU and 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev tensor := siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R

/-- Localization restricted to the full resolving homotopy subcategory.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev localization := (resolvingHomotopy R).ι ⋙
  (DerivedCategory.Qh : HomotopyCategory (Modules R) (.up ℤ) ⥤ D R)

/-- The resolving subcategory presents the existing derived category. -/
private theorem localization_isLocalization :
    (localization R).IsLocalization
      ((HomotopyCategory.quasiIso (Modules R) (.up ℤ)).inverseImage
        (resolvingHomotopy R).ι) := by
  obtain ⟨P, hP, ⟨F, hF, ⟨e⟩⟩, _⟩ :=
    site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0} J R
  have hp : P = resolvingHomotopy R := funext fun X ↦ propext (hP X)
  subst P
  let := hF
  exact Functor.IsLocalization.of_iso _ e

/-- Total tensor with its resolving proof supplied by the recorded model theorem.
Source: Stacks 07A2 and 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
def totalModel (E F : Model R) : Model R :=
  ⟨E.obj ⊗ F.obj,
    (KFlatTotalTensorModel.kFlat_total_tensor_model R E.obj F.obj
      E.property.1 F.property.1 E.property.2 F.property.2).1,
    (KFlatTotalTensorModel.kFlat_total_tensor_model R E.obj F.obj
      E.property.1 F.property.1 E.property.2 F.property.2).2.1⟩

/-- Shift with the resolving proof supplied by the fixed-tensor theorem.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
def shiftModel (E : Model R) (a : ℤ) : Model R :=
  ⟨E.obj⟦a⟧,
    ((KFlatFixedTensor.kFlat_fixed_tensor_triangulated R).choose_spec
      E.obj E.property.1 E.property.2).2.1 a⟩

/-- The actual published representative isomorphism, on bundled resolving models.
Source: Stacks 06YU and 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
def representative (E F : Model R) :
    DerivedCategory.Q.obj (E.obj ⊗ F.obj) ≅
      (tensor R).obj (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) :=
  KFlatFixedTensor.representativeIso R E.obj F.obj
    E.property.1 F.property.1 E.property.2 F.property.2

/-- Extract the right shift first and the left shift second. The first map has
coefficient (-1)^(bp) in shifted first-factor degree p, and the second is unsigned.
Source: Stacks more-algebra.tex, sign rules, and sites-cohomology.tex, 0FPT
(blueprint: lem-pur-derived-tensor-additive-constraints). -/
def chainShift (E F : Complex R) (a b : ℤ) :
    (E⟦a⟧ ⊗ F⟦b⟧) ≅ (E ⊗ F)⟦a + b⟧ :=
  CochainComplex.mapBifunctorShift₂Iso (E⟦a⟧) F (KFlatFixedTensor.ordinaryTensor R) b ≪≫
    (shiftFunctor (Complex R) b).mapIso
      (CochainComplex.mapBifunctorShift₁Iso E F (KFlatFixedTensor.ordinaryTensor R) a) ≪≫
    ((shiftFunctorAdd (Complex R) a b).app (E ⊗ F)).symm

/-- The two-variable functor with shifts inside the fixed derived tensor.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev shiftedSource (a b : ℤ) :=
  ((shiftFunctor (D R) a).prod (shiftFunctor (D R) b)) ⋙ tensor R

/-- The two-variable functor with the sum of the shifts outside tensor.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev shiftedTarget (a b : ℤ) := tensor R ⋙ shiftFunctor (D R) (a + b)

/-- The left-parenthesized ternary derived tensor functor.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev leftAssociated := ((tensor R).prod (𝟭 (D R))) ⋙ tensor R

/-- The right-parenthesized ternary derived tensor functor on the same domain.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev rightAssociated := CategoryTheory.prod.associator (D R) (D R) (D R) ⋙
  ((𝟭 (D R)).prod (tensor R)) ⋙ tensor R

/-- The swapped tensor functor.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev swapped := CategoryTheory.Prod.swap (D R) (D R) ⋙ tensor R

/-- The normalized shift comparison on resolving pairs, with every comparison inserted.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
def shiftRepresentative (E F : Model R) (a b : ℤ) :
    (shiftedSource R a b).obj (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) ≅
      (shiftedTarget R a b).obj (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) :=
  (tensor R).mapIso (Iso.prod ((DerivedCategory.Q.commShiftIso a).app E.obj).symm
      ((DerivedCategory.Q.commShiftIso b).app F.obj).symm) ≪≫
    (representative R (shiftModel R E a) (shiftModel R F b)).symm ≪≫
    DerivedCategory.Q.mapIso (chainShift R E.obj F.obj a b) ≪≫
    (DerivedCategory.Q.commShiftIso (a + b)).app (E.obj ⊗ F.obj) ≪≫
    (shiftFunctor (D R) (a + b)).mapIso (representative R E F)

/-- Comparison from the iterated total to the left-parenthesized derived tensor.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
def leftRepresentative (E F G : Model R) :
    DerivedCategory.Q.obj ((E.obj ⊗ F.obj) ⊗ G.obj) ≅
      (leftAssociated R).obj
        ((DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj), DerivedCategory.Q.obj G.obj) :=
  representative R (totalModel R E F) G ≪≫
    (tensor R).mapIso (Iso.prod (representative R E F) (Iso.refl _))

/-- Comparison from the other iterated total to the right-parenthesized derived tensor.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
def rightRepresentative (E F G : Model R) :
    DerivedCategory.Q.obj (E.obj ⊗ (F.obj ⊗ G.obj)) ≅
      (rightAssociated R).obj
        ((DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj), DerivedCategory.Q.obj G.obj) :=
  representative R E (totalModel R F G) ≪≫
    (tensor R).mapIso (Iso.prod (Iso.refl _) (representative R F G))

/-- The complete representative normalization of the shift, associator and symmetry.
The equalities compare natural isomorphisms through their actual components.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
def IsNormalized
    (t : ∀ a b : ℤ, shiftedSource R a b ≅ shiftedTarget R a b)
    (α : leftAssociated R ≅ rightAssociated R) (σ : tensor R ≅ swapped R) : Prop :=
  (∀ (a b : ℤ) (E F : Model R),
    (t a b).app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) =
      shiftRepresentative R E F a b) ∧
  (∀ E F G : Model R,
    α.app ((DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj),
        DerivedCategory.Q.obj G.obj) =
      (leftRepresentative R E F G).symm ≪≫
        DerivedCategory.Q.mapIso (α_ E.obj F.obj G.obj) ≪≫ rightRepresentative R E F G) ∧
  (∀ E F : Model R,
    σ.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) =
      (representative R E F).symm ≪≫
        DerivedCategory.Q.mapIso (CochainComplex.Monoidal.braiding E.obj F.obj) ≪≫
        representative R F E)

section

omit [HasDerivedCategory.{w} (Modules R)] in
private theorem flat_of_isZero (P : Modules R) (hP : IsZero P) :
    SheafOfModules.IsFlatOnSite (J := J) (R := R) P := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive R
  have h : ObjectProperty.flat P := ObjectProperty.prop_of_isZero _ hP
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R P).symm h.2

omit [HasDerivedCategory.{w} (Modules R)] in
private theorem single_resolving (P : Modules R)
    (hP : SheafOfModules.IsFlatOnSite (J := J) (R := R) P) :
    resolvingComplex R ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj P) := by
  have hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R)
      (((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj P).X i) := by
    intro i
    by_cases hi : i = 0
    · subst i
      simpa only [HomologicalComplex.single_obj_X_self] using hP
    · exact flat_of_isZero R _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
  exact ⟨SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R _ 0 hf,
    hf⟩

omit [HasDerivedCategory.{w} (Modules R)] in
private theorem finite_resolving (n : ℕ) (E : Fin n → Complex R)
    (hE : ∀ j, resolvingComplex R (E j)) : resolvingComplex R (∐ E) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  have (P : Modules R) : PreservesColimitsOfSize.{0, 0} (tensorLeft P) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R P
    exact preservesColimitsOfSize_shrink _
  have (P : Modules R) : PreservesColimitsOfSize.{0, 0} (tensorRight P) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight P)
  constructor
  · intro F hF i
    let T := (KFlatFixedTensor.totalTensor R).obj F
    have : PreservesColimitsOfShape (Discrete (Fin n)) T := inferInstance
    let H := HomologicalComplex.homologyFunctor (Modules R) (.up ℤ) i
    have hc := isColimitOfPreserves H (isColimitOfPreserves T (coproductIsCoproduct E))
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    apply hc.isZero_pt
    apply (Functor.isZero_iff _).2
    intro j
    exact ((hE j.as).1 F hF i).isZero_homology
  · intro i
    have : HasFiniteBiproducts (Complex R) :=
      HasFiniteBiproducts.of_hasFiniteProducts
    let e : (∏ᶜ E) ≅ ∐ E :=
      (biproduct.isoProduct E).symm ≪≫ biproduct.isoCoproduct E
    have hp : ObjectProperty.flat ((∏ᶜ E).X i) :=
      ObjectProperty.prop_of_isLimit _
        (isLimitOfPreserves (HomologicalComplex.eval (Modules R) (.up ℤ) i)
          (productIsProduct E)) (fun j ↦ SheafOfModules.flat_to_cat R _ ((hE j.as).2 i))
    have hq : ObjectProperty.flat ((∐ E).X i) :=
      (ObjectProperty.flat (A := Modules R)).prop_of_iso
        ((HomologicalComplex.eval (Modules R) (.up ℤ) i).mapIso e) hp
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm hq.2

end

/-- Resolving models are closed under tensor, every integer shift and finite sums.
Flat sheaves give resolving degree-zero complexes, and their ordinary tensor is flat.
The degree-zero derived comparison is induced by r and the normalized chain comparison.
Source: Stacks 07A2, 06YU and 0FPT
(blueprint: lem-pur-derived-tensor-additive-constraints).

Proof: total tensors and shifts use the recorded model and fixed-tensor theorems.
Tensor preserves finite coproducts, and homology is additive, so tensoring a finite
sum of resolving complexes with an acyclic complex has zero homology. Evaluation
preserves products, and flat objects are closed under finite products, proving
termwise flatness. The bounded-above flat criterion applies to a flat sheaf in
degree zero; its other terms are zero. Flat objects are closed under tensor.
Compose the single-first-factor tensor comparison with singleMapHomologicalComplex;
the defining inclusion formula gives the required degree-zero normalization.
The derived comparison is its localization after the inverse representative map.
-/
theorem derived_tensor_model_closure :
    (∀ E F : Model R, resolvingComplex R (E.obj ⊗ F.obj)) ∧
    (∀ (E : Model R) (a : ℤ), resolvingComplex R (E.obj⟦a⟧)) ∧
    (∀ (n : ℕ) (E : Fin n → Complex R), (∀ j, resolvingComplex R (E j)) →
      resolvingComplex R (∐ E)) ∧
    (∀ P : Modules R, SheafOfModules.IsFlatOnSite (J := J) (R := R) P →
      resolvingComplex R ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj P)) ∧
    (∀ (P Q : Modules R),
      SheafOfModules.IsFlatOnSite (J := J) (R := R) P →
      SheafOfModules.IsFlatOnSite (J := J) (R := R) Q →
      SheafOfModules.IsFlatOnSite (J := J) (R := R) (P ⊗ Q) ∧
      ∃ c :
        ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj P ⊗
          (HomologicalComplex.single (Modules R) (.up ℤ) 0).obj Q) ≅
        (HomologicalComplex.single (Modules R) (.up ℤ) 0).obj (P ⊗ Q),
        (HomologicalComplex.ιTensorObj
            ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj P)
            ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj Q) 0 0 0 rfl ≫
          c.hom.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (P ⊗ Q)).hom =
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).hom ⊗ₘ
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom) ∧
        ∀ (hP : resolvingComplex R
              ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj P))
            (hQ : resolvingComplex R
              ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj Q)),
          ∃ d :
            (tensor R).obj
              (DerivedCategory.Q.obj
                  ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj P),
                DerivedCategory.Q.obj
                  ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj Q)) ≅
              DerivedCategory.Q.obj
                ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj (P ⊗ Q)),
            d = (representative R ⟨_, hP⟩ ⟨_, hQ⟩).symm ≪≫
              DerivedCategory.Q.mapIso c) := by
  refine ⟨(fun E F ↦ (totalModel R E F).property),
    (fun E a ↦ (shiftModel R E a).property), finite_resolving R, single_resolving R, ?_⟩
  intro P Q hP hQ
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive R
  have hPQ : SheafOfModules.IsFlatOnSite (J := J) (R := R) (P ⊗ Q) := by
    have h : ObjectProperty.flat (P ⊗ Q) :=
      ObjectProperty.prop_tensor (SheafOfModules.flat_to_cat R P hP)
        (SheafOfModules.flat_to_cat R Q hQ)
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm h.2
  let c := CochainComplex.mapBifunctorSingle₁Iso (KFlatFixedTensor.ordinaryTensor R) P
      ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj Q) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex
      ((KFlatFixedTensor.ordinaryTensor R).obj P) (.up ℤ) 0).app Q
  refine ⟨hPQ, c, ?_, ?_⟩
  · dsimp [c]
    simp only [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      Category.assoc]
    change CochainComplex.ιMapBifunctor _ _ _ _ _ _ _ ≫
        (CochainComplex.mapBifunctorSingle₁XIso _ _ _ _).hom ≫ _ = _
    simp [CochainComplex.mapBifunctorSingle₁XIso, MonoidalCategory.tensorHom_def]
    rfl
  · intro hP' hQ'
    exact ⟨_, rfl⟩

section


-- Expose the tensor aliases before comparing their total-complex object formulas.
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance 2000] KFlatFixedTensor.tensorAdditive
  KFlatFixedTensor.tensorObjAdditive KFlatFixedTensor.tensorHasMapBifunctor

attribute [local instance 2000] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory SheafOfModules.cochainModulesMonoidal

private def nativeBraiding (E F : Complex R) : E ⊗ F ≅ F ⊗ E :=
  CochainComplex.Monoidal.braiding E F

omit [HasDerivedCategory (Modules R)] in
private theorem nativeBraiding_naturality {E E' F F' : Complex R}
    (f : E ⟶ E') (g : F ⟶ F') :
    (f ⊗ₘ g) ≫ (nativeBraiding R E' F').hom =
      (nativeBraiding R E F).hom ≫ (g ⊗ₘ f) :=
  BraidedCategory.braiding_naturality f g

omit [HasDerivedCategory (Modules R)] in
private theorem totalTensor_map {E E' F F' : Complex R}
    (f : E ⟶ E') (g : F ⟶ F') :
    (Functor.uncurry.obj (KFlatFixedTensor.totalTensor R)).map (Prod.mkHom f g) =
      f ⊗ₘ g := by
  rw [MonoidalCategory.tensorHom_def]
  rfl

private abbrev modelLocalization : Model R ⥤ D R :=
  (resolvingComplex R).ι ⋙ DerivedCategory.Q

private abbrev nativeTensor : Complex R × Complex R ⥤ Complex R :=
  MonoidalCategory.tensor (Complex R)

private abbrev modelTotal : Model R × Model R ⥤ Complex R :=
  ((resolvingComplex R).ι.prod (resolvingComplex R).ι) ⋙ nativeTensor R

omit [HasDerivedCategory (Modules R)] in
private theorem modelTotal_map {E E' F F' : Model R}
    (f : E ⟶ E') (g : F ⟶ F') :
    (modelTotal R).map (Prod.mkHom f g) = f.hom ⊗ₘ g.hom := rfl

private def representativeNatIso :
    modelTotal R ⋙ DerivedCategory.Q ≅
      ((modelLocalization R).prod (modelLocalization R)) ⋙ tensor R :=
  let c := genericPresentationComparison (resolvingComplex R).ι
    (KFlatFixedTensor.selectedTensorPresentation R)
    (fun E ↦ (KFlatFixedTensor.resolvingProperty_spec R _).2 E.property)
  NatIso.ofComponents (F := modelTotal R ⋙ DerivedCategory.Q)
    (G := ((modelLocalization R).prod (modelLocalization R)) ⋙ tensor R)
    (fun E ↦ representative R E.1 E.2) (by
    intro E F f
    have h := c.hom.naturality f
    change DerivedCategory.Q.map
      ((Functor.uncurry.obj (KFlatFixedTensor.totalTensor R)).map
        (Prod.mkHom f.1.hom f.2.hom)) ≫ _ = _ at h
    rw [totalTensor_map] at h
    unfold representative KFlatFixedTensor.representativeIso
    exact h)

private theorem representativeNatIso_hom_app (E F : Model R) :
    (representativeNatIso R).hom.app (E, F) = (representative R E F).hom := rfl

private theorem representativeNatIso_inv_app (E F : Model R) :
    (representativeNatIso R).inv.app (E, F) = (representative R E F).inv := rfl

private theorem representativeNatIso_app (E F : Model R) :
    (representativeNatIso R).app (E, F) = representative R E F := rfl

attribute [local irreducible] representative

attribute [local irreducible] representativeNatIso

@[implicit_reducible] private def modelTotalFunctor : Model R × Model R ⥤ Model R :=
  (resolvingComplex R).lift (modelTotal R)
    (fun E ↦ (totalModel R E.1 E.2).property)

private def leftRepresentativeNatIso :
    (((modelTotalFunctor R).prod (𝟭 (Model R))) ⋙ modelTotal R) ⋙ DerivedCategory.Q ≅
      (((modelLocalization R).prod (modelLocalization R)).prod (modelLocalization R)) ⋙
        leftAssociated R :=
  isoWhiskerLeft ((modelTotalFunctor R).prod (𝟭 (Model R))) (representativeNatIso R) ≪≫
    isoWhiskerRight (NatIso.prod (representativeNatIso R) (Iso.refl _)) (tensor R)

private def rightRepresentativeNatIso :
    (CategoryTheory.prod.associator (Model R) (Model R) (Model R) ⋙
      ((𝟭 (Model R)).prod (modelTotalFunctor R)) ⋙ modelTotal R) ⋙ DerivedCategory.Q ≅
      (((modelLocalization R).prod (modelLocalization R)).prod (modelLocalization R)) ⋙
        rightAssociated R :=
  isoWhiskerLeft (CategoryTheory.prod.associator (Model R) (Model R) (Model R))
    (isoWhiskerLeft ((𝟭 (Model R)).prod (modelTotalFunctor R)) (representativeNatIso R) ≪≫
      isoWhiskerRight (NatIso.prod (Iso.refl _) (representativeNatIso R)) (tensor R))

private def modelAssociator :
    (((modelLocalization R).prod (modelLocalization R)).prod (modelLocalization R)) ⋙
        leftAssociated R ≅
      (((modelLocalization R).prod (modelLocalization R)).prod (modelLocalization R)) ⋙
        rightAssociated R := by
  let c : ((modelTotalFunctor R).prod (𝟭 (Model R))) ⋙ modelTotal R ≅
      CategoryTheory.prod.associator (Model R) (Model R) (Model R) ⋙
        ((𝟭 (Model R)).prod (modelTotalFunctor R)) ⋙ modelTotal R :=
    isoWhiskerLeft
      ((((resolvingComplex R).ι.prod (resolvingComplex R).ι).prod (resolvingComplex R).ι) ⋙
        CategoryTheory.prod.associator (Complex R) (Complex R) (Complex R))
      (MonoidalCategory.associatorNatIso (Complex R))
  exact (leftRepresentativeNatIso R).symm ≪≫
    isoWhiskerRight c DerivedCategory.Q ≪≫ rightRepresentativeNatIso R

private def modelSymmetry :
    ((modelLocalization R).prod (modelLocalization R)) ⋙ tensor R ≅
      ((modelLocalization R).prod (modelLocalization R)) ⋙ swapped R := by
  let c : modelTotal R ≅ CategoryTheory.Prod.swap (Model R) (Model R) ⋙ modelTotal R :=
    NatIso.ofComponents (F := modelTotal R)
      (G := CategoryTheory.Prod.swap (Model R) (Model R) ⋙ modelTotal R)
      (fun E ↦ by
      let b := nativeBraiding R E.1.obj E.2.obj
      change (E.1.obj ⊗ E.2.obj) ≅ (E.2.obj ⊗ E.1.obj)
      exact b)
      (by
        intro E F f
        change (modelTotal R).map f ≫ _ = _ ≫
          (modelTotal R).map (Prod.mkHom f.2 f.1)
        erw [modelTotal_map R f.1 f.2, modelTotal_map R f.2 f.1]
        have h := nativeBraiding_naturality R f.1.hom f.2.hom
        exact h)
  exact (representativeNatIso R).symm ≪≫ isoWhiskerRight c DerivedCategory.Q ≪≫
    isoWhiskerLeft (CategoryTheory.Prod.swap (Model R) (Model R)) (representativeNatIso R)

private def nativePairShift (a b : ℤ) :
    ((shiftFunctor (Complex R) a).prod (shiftFunctor (Complex R) b)) ⋙ nativeTensor R ≅
      nativeTensor R ⋙ shiftFunctor (Complex R) (a + b) := by
  let c := genericShiftPair (KFlatFixedTensor.totalTensor R) a b
  refine NatIso.ofComponents
    (F := ((shiftFunctor (Complex R) a).prod (shiftFunctor (Complex R) b)) ⋙ nativeTensor R)
    (G := nativeTensor R ⋙ shiftFunctor (Complex R) (a + b))
    (fun E ↦ chainShift R E.1 E.2 a b) ?_
  intro E F f
  have h := c.hom.naturality f
  change (Functor.uncurry.obj (KFlatFixedTensor.totalTensor R)).map
      (Prod.mkHom ((shiftFunctor (Complex R) a).map f.1)
        ((shiftFunctor (Complex R) b).map f.2)) ≫ _ =
      _ ≫ (shiftFunctor (Complex R) (a + b)).map
        ((Functor.uncurry.obj (KFlatFixedTensor.totalTensor R)).map f) at h
  erw [totalTensor_map R, totalTensor_map R f.1 f.2] at h
  exact h

omit [HasDerivedCategory (Modules R)] in
private theorem nativePairShift_hom_app (E F : Complex R) (a b : ℤ) :
    (nativePairShift R a b).hom.app (E, F) = (chainShift R E F a b).hom := rfl

attribute [local irreducible] nativePairShift

@[implicit_reducible] private def modelShiftFunctor (a : ℤ) : Model R ⥤ Model R :=
  (resolvingComplex R).lift ((resolvingComplex R).ι ⋙ shiftFunctor (Complex R) a)
    (fun E ↦ (shiftModel R E a).property)

private def modelShift (a b : ℤ) :
    ((modelLocalization R).prod (modelLocalization R)) ⋙ shiftedSource R a b ≅
      ((modelLocalization R).prod (modelLocalization R)) ⋙ shiftedTarget R a b := by
  exact genericShiftConjugate (resolvingComplex R).ι (modelTotal R)
    DerivedCategory.Q (tensor R) (modelShiftFunctor R)
    (fun n ↦ isoWhiskerLeft (resolvingComplex R).ι (DerivedCategory.Q.commShiftIso n))
    (representativeNatIso R) a b
    (isoWhiskerLeft (((resolvingComplex R).ι).prod (resolvingComplex R).ι)
      (nativePairShift R a b))

private theorem extendBinary (U V : D R × D R ⥤ D R)
    (e : ((modelLocalization R).prod (modelLocalization R)) ⋙ U ≅
      ((modelLocalization R).prod (modelLocalization R)) ⋙ V) :
    ∃ s : U ≅ V, ∀ E F : Model R,
      s.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) = e.app (E, F) := by
  let L := localization R
  let W := (HomotopyCategory.quasiIso (Modules R) (.up ℤ)).inverseImage
    (resolvingHomotopy R).ι
  have : L.IsLocalization W := localization_isLocalization R
  let c : (L.prod L) ⋙ U ≅ (L.prod L) ⋙ V :=
    NatIso.ofComponents (fun E ↦ e.app
      (⟨E.1.obj.as, E.1.property⟩, ⟨E.2.obj.as, E.2.property⟩)) (by
        intro E F f
        change U.map (Prod.mkHom (DerivedCategory.Qh.map f.1.hom)
          (DerivedCategory.Qh.map f.2.hom)) ≫ _ =
            _ ≫ V.map (Prod.mkHom (DerivedCategory.Qh.map f.1.hom)
              (DerivedCategory.Qh.map f.2.hom))
        rw [← HomotopyCategory.quotient_map_out f.1.hom,
          ← HomotopyCategory.quotient_map_out f.2.hom]
        exact e.hom.naturality (Prod.mkHom
          (ObjectProperty.homMk (P := resolvingComplex R)
            (X := ⟨E.1.obj.as, E.1.property⟩)
            (Y := ⟨F.1.obj.as, F.1.property⟩) f.1.hom.out)
          (ObjectProperty.homMk (P := resolvingComplex R)
            (X := ⟨E.2.obj.as, E.2.property⟩)
            (Y := ⟨F.2.obj.as, F.2.property⟩) f.2.hom.out)))
  obtain ⟨s, hs⟩ :=
    (Localization.fullyFaithfulWhiskeringLeft (L.prod L) (W.prod W) (D R)).isoEquiv.surjective c
  refine ⟨s, ?_⟩
  intro E F
  exact congrArg (fun t ↦ t.app
    (⟨(HomotopyCategory.quotient _ _).obj E.obj, E.property⟩,
      ⟨(HomotopyCategory.quotient _ _).obj F.obj, F.property⟩)) hs

private theorem extendTernary (U V : (D R × D R) × D R ⥤ D R)
    (e : (((modelLocalization R).prod (modelLocalization R)).prod (modelLocalization R)) ⋙ U ≅
      (((modelLocalization R).prod (modelLocalization R)).prod (modelLocalization R)) ⋙ V) :
    ∃ s : U ≅ V, ∀ E F G : Model R,
      s.app ((DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj),
        DerivedCategory.Q.obj G.obj) = e.app ((E, F), G) := by
  let L := localization R
  let W := (HomotopyCategory.quasiIso (Modules R) (.up ℤ)).inverseImage
    (resolvingHomotopy R).ι
  have : L.IsLocalization W := localization_isLocalization R
  let c : ((L.prod L).prod L) ⋙ U ≅ ((L.prod L).prod L) ⋙ V :=
    NatIso.ofComponents (fun E ↦ e.app
      ((⟨E.1.1.obj.as, E.1.1.property⟩, ⟨E.1.2.obj.as, E.1.2.property⟩),
        ⟨E.2.obj.as, E.2.property⟩)) (by
        intro E F f
        change U.map (Prod.mkHom
          (Prod.mkHom (DerivedCategory.Qh.map f.1.1.hom)
            (DerivedCategory.Qh.map f.1.2.hom))
          (DerivedCategory.Qh.map f.2.hom)) ≫ _ =
            _ ≫ V.map (Prod.mkHom
              (Prod.mkHom (DerivedCategory.Qh.map f.1.1.hom)
                (DerivedCategory.Qh.map f.1.2.hom)) (DerivedCategory.Qh.map f.2.hom))
        rw [← HomotopyCategory.quotient_map_out f.1.1.hom,
          ← HomotopyCategory.quotient_map_out f.1.2.hom,
          ← HomotopyCategory.quotient_map_out f.2.hom]
        exact e.hom.naturality (Prod.mkHom (Prod.mkHom
          (ObjectProperty.homMk (P := resolvingComplex R)
            (X := ⟨E.1.1.obj.as, E.1.1.property⟩)
            (Y := ⟨F.1.1.obj.as, F.1.1.property⟩) f.1.1.hom.out)
          (ObjectProperty.homMk (P := resolvingComplex R)
            (X := ⟨E.1.2.obj.as, E.1.2.property⟩)
            (Y := ⟨F.1.2.obj.as, F.1.2.property⟩) f.1.2.hom.out))
          (ObjectProperty.homMk (P := resolvingComplex R)
            (X := ⟨E.2.obj.as, E.2.property⟩)
            (Y := ⟨F.2.obj.as, F.2.property⟩) f.2.hom.out)))
  obtain ⟨s, hs⟩ := (Localization.fullyFaithfulWhiskeringLeft
    ((L.prod L).prod L) ((W.prod W).prod W) (D R)).isoEquiv.surjective c
  refine ⟨s, ?_⟩
  intro E F G
  exact congrArg (fun t ↦ t.app
    ((⟨(HomotopyCategory.quotient _ _).obj E.obj, E.property⟩,
      ⟨(HomotopyCategory.quotient _ _).obj F.obj, F.property⟩),
      ⟨(HomotopyCategory.quotient _ _).obj G.obj, G.property⟩)) hs

private theorem binary_iso_ext {U V : D R × D R ⥤ D R} (s t : U ≅ V)
    (h : ∀ E F : Model R,
      s.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) =
        t.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj)) : s = t := by
  let W := (HomotopyCategory.quasiIso (Modules R) (.up ℤ)).inverseImage
    (resolvingHomotopy R).ι
  have : (localization R).IsLocalization W := localization_isLocalization R
  apply Iso.ext
  apply Localization.natTrans_ext ((localization R).prod (localization R)) (W.prod W)
  intro E
  exact congrArg Iso.hom (h ⟨E.1.obj.as, E.1.property⟩ ⟨E.2.obj.as, E.2.property⟩)

private theorem ternary_iso_ext {U V : (D R × D R) × D R ⥤ D R} (s t : U ≅ V)
    (h : ∀ E F G : Model R,
      s.app ((DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj),
        DerivedCategory.Q.obj G.obj) =
      t.app ((DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj),
        DerivedCategory.Q.obj G.obj)) : s = t := by
  let L := localization R
  let W := (HomotopyCategory.quasiIso (Modules R) (.up ℤ)).inverseImage
    (resolvingHomotopy R).ι
  have : L.IsLocalization W := localization_isLocalization R
  apply Iso.ext
  apply Localization.natTrans_ext ((L.prod L).prod L) ((W.prod W).prod W)
  intro E
  exact congrArg Iso.hom (h ⟨E.1.1.obj.as, E.1.1.property⟩
    ⟨E.1.2.obj.as, E.1.2.property⟩ ⟨E.2.obj.as, E.2.property⟩)

private theorem modelShift_app (E F : Model R) (a b : ℤ) :
    (modelShift R a b).app (E, F) = shiftRepresentative R E F a b := by
  apply Iso.ext
  dsimp only [modelShift, Iso.app]
  rw [genericShiftConjugate_hom_app]
  change (tensor R).map
      (Prod.mkHom ((DerivedCategory.Q.commShiftIso a).inv.app E.obj)
        ((DerivedCategory.Q.commShiftIso b).inv.app F.obj)) ≫
      (representativeNatIso R).inv.app (shiftModel R E a, shiftModel R F b) ≫
      DerivedCategory.Q.map ((nativePairShift R a b).hom.app (E.obj, F.obj)) ≫
      (DerivedCategory.Q.commShiftIso (a + b)).hom.app (E.obj ⊗ F.obj) ≫
      (shiftFunctor (D R) (a + b)).map ((representativeNatIso R).hom.app (E, F)) = _
  erw [representativeNatIso_inv_app, nativePairShift_hom_app, representativeNatIso_hom_app]
  rfl

private theorem leftRepresentativeNatIso_app (E F G : Model R) :
    (leftRepresentativeNatIso R).app ((E, F), G) = leftRepresentative R E F G := by
  change (representativeNatIso R).app (totalModel R E F, G) ≪≫
    (tensor R).mapIso (Iso.prod ((representativeNatIso R).app (E, F)) (Iso.refl _)) = _
  rw [representativeNatIso_app, representativeNatIso_app]
  rfl

private theorem rightRepresentativeNatIso_app (E F G : Model R) :
    (rightRepresentativeNatIso R).app ((E, F), G) = rightRepresentative R E F G := by
  change (representativeNatIso R).app (E, totalModel R F G) ≪≫
    (tensor R).mapIso (Iso.prod (Iso.refl _) ((representativeNatIso R).app (F, G))) = _
  rw [representativeNatIso_app, representativeNatIso_app]
  rfl

private theorem modelAssociator_app (E F G : Model R) :
    (modelAssociator R).app ((E, F), G) =
      (leftRepresentative R E F G).symm ≪≫
        DerivedCategory.Q.mapIso (α_ E.obj F.obj G.obj) ≪≫
          rightRepresentative R E F G := by
  apply Iso.ext
  change ((leftRepresentativeNatIso R).app ((E, F), G)).inv ≫
      DerivedCategory.Q.map (α_ E.obj F.obj G.obj).hom ≫
      ((rightRepresentativeNatIso R).app ((E, F), G)).hom = _
  erw [leftRepresentativeNatIso_app, rightRepresentativeNatIso_app]
  rfl

private theorem modelSymmetry_app (E F : Model R) :
    (modelSymmetry R).app (E, F) =
      (representative R E F).symm ≪≫
        DerivedCategory.Q.mapIso (CochainComplex.Monoidal.braiding E.obj F.obj) ≪≫
          representative R F E := by
  apply Iso.ext
  change (representativeNatIso R).inv.app (E, F) ≫
      DerivedCategory.Q.map (nativeBraiding R E.obj F.obj).hom ≫
      (representativeNatIso R).hom.app (F, E) = _
  erw [representativeNatIso_inv_app, representativeNatIso_hom_app]
  rfl


end

attribute [local irreducible] modelShift modelAssociator modelSymmetry

/-- Unique derived natural constraints with the specified representative squares.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints).

Proof: restrict the recorded homotopy and resolving comparisons of the published
tensor presentation to resolving complexes. The generic component calculation
gives the published representative
map. This gives a natural comparison on resolving chain models.
Conjugate the native chain associator, Koszul braiding and right-then-left tensor
shift isomorphisms by these comparisons. All are natural isomorphisms, including
the localization shift comparisons. Every homotopy morphism is the image of a
chain map between the same complexes; hence the same component formulas are natural
on the resolving homotopy category. Its binary and ternary localization functors
are localizations by product localization. Fully faithful precomposition extends
each model isomorphism to the derived category. Computing components gives the
prescribed formulas on resolving complexes. Faithfulness proves uniqueness separately
for every shift pair, the associator and symmetry; product extensionality combines these.
-/
theorem existsUnique_derived_tensor_constraints :
    ∃! s : (∀ a b : ℤ, shiftedSource R a b ≅ shiftedTarget R a b) ×
        (leftAssociated R ≅ rightAssociated R) × (tensor R ≅ swapped R),
      IsNormalized R s.1 s.2.1 s.2.2 := by
  let := complexMonoidal R
  let := complexMonoidalStruct R
  have ht : ∀ a b : ℤ, ∃ s : shiftedSource R a b ≅ shiftedTarget R a b,
      ∀ E F : Model R,
        s.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) =
          shiftRepresentative R E F a b := by
    intro a b
    obtain ⟨s, hs⟩ := extendBinary R (shiftedSource R a b) (shiftedTarget R a b) (modelShift R a b)
    refine ⟨s, ?_⟩
    intro E F
    exact (hs E F).trans (modelShift_app R E F a b)
  choose t ht using ht
  obtain ⟨α, hα⟩ := extendTernary R (leftAssociated R) (rightAssociated R) (modelAssociator R)
  obtain ⟨σ, hσ⟩ := extendBinary R (tensor R) (swapped R) (modelSymmetry R)
  have hα' : ∀ E F G : Model R,
      α.app ((DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj),
        DerivedCategory.Q.obj G.obj) =
      (leftRepresentative R E F G).symm ≪≫
        DerivedCategory.Q.mapIso (α_ E.obj F.obj G.obj) ≪≫ rightRepresentative R E F G := by
    intro E F G
    exact (hα E F G).trans (modelAssociator_app R E F G)
  have hσ' : ∀ E F : Model R,
      σ.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) =
      (representative R E F).symm ≪≫
        DerivedCategory.Q.mapIso (CochainComplex.Monoidal.braiding E.obj F.obj) ≪≫
          representative R F E := by
    intro E F
    exact (hσ E F).trans (modelSymmetry_app R E F)
  refine ⟨(t, α, σ), ⟨ht, hα', hσ'⟩, ?_⟩
  intro s hs
  apply Prod.ext
  · funext a b
    apply binary_iso_ext R
    intro E F
    exact (hs.1 a b E F).trans (ht a b E F).symm
  · apply Prod.ext
    · apply ternary_iso_ext R
      intro E F G
      exact (hs.2.1 E F G).trans (hα' E F G).symm
    · apply binary_iso_ext R
      intro E F
      exact (hs.2.2 E F).trans (hσ' E F).symm

/-- Restriction in any finite number of variables is fully faithful, and detects
all equalities of natural transformations, including tensor/shift composites.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints).

Proof plan: the descent equivalence identifies resolving homotopy localization
with D. Apply lem-sfb-product-localization to q in every variable, including the
empty product, and lem-weil-pbc-localization-universal-property to get full
faithfulness of precomposition. Its faithfulness says exactly that two natural
transformations agree iff all their components on resolving tuples agree.
This tests ternary associativity and binary signed symmetry after substituting
the comparisons in IsNormalized; it does not test unrelated objectwise maps.
-/
theorem derived_tensor_restriction_fully_faithful
    (I : Type i) [Finite I] (E : Type e) [Category.{z} E] :
    Nonempty (((Functor.whiskeringLeft (I → (resolvingHomotopy R).FullSubcategory)
      (I → D R) E).obj (Functor.pi (fun _ : I ↦ localization R))).FullyFaithful) ∧
    (∀ (U V : (I → D R) ⥤ E) (η θ : U ⟶ V),
      η = θ ↔ ∀ x : I → (resolvingHomotopy R).FullSubcategory,
        η.app (fun j ↦ (localization R).obj (x j)) =
          θ.app (fun j ↦ (localization R).obj (x j))) := by
  let W := (HomotopyCategory.quasiIso (Modules R) (.up ℤ)).inverseImage
    (resolvingHomotopy R).ι
  have : (localization R).IsLocalization W := localization_isLocalization R
  let L := Functor.pi (fun _ : I ↦ localization R)
  let Wpi := MorphismProperty.pi (fun _ : I ↦ W)
  have : L.IsLocalization Wpi := Functor.IsLocalization.pi _ _
  refine ⟨⟨Localization.fullyFaithfulWhiskeringLeft L Wpi E⟩, ?_⟩
  intro U V η θ
  constructor
  · rintro rfl x
    rfl
  · intro h
    exact Localization.natTrans_ext L Wpi (fun x ↦ h x)

/-- The fixed derived tensor is separately additive on all derived morphisms,
and the actual images of every binary biproduct diagram are biproduct diagrams.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints).

Proof plan: resolve H by qA using lem-weil-pbc-site-derived-tensor-descent.
Tensoring qA on either side is exact by lem-weil-pbc-kflat-fixed-tensor-triangulated,
hence additive by def-weil-triangulated-category. Tensoring qA ≅ H gives a natural
isomorphism; conjugation preserves sums by bilinearity of composition. This applies
to arbitrary derived morphisms. Applying a fixed tensor functor to the biproduct
identities p_j i_k = delta_jk and i_1 p_1 + i_2 p_2 = 1 gives the same identities.
The sums of the corresponding composites give the unique maps into and out of the
image diagram. No flatness or boundedness is required of H or the other objects.
-/
theorem derived_tensor_additive :
    ∀ H : D R,
      ∃ (_ : ((KFlatFixedTensor.derivedTensor R).obj H).Additive)
        (_ : ((KFlatFixedTensor.derivedTensor R).flip.obj H).Additive),
      (∀ (X Y : D R) (b : BinaryBicone X Y), b.IsBilimit →
        Nonempty (((KFlatFixedTensor.derivedTensor R).obj H).mapBinaryBicone b).IsBilimit ∧
        Nonempty (((KFlatFixedTensor.derivedTensor R).flip.obj H).mapBinaryBicone b).IsBilimit) ∧
      (∀ (X Y : D R) (f g : X ⟶ Y),
        ((KFlatFixedTensor.derivedTensor R).obj H).map (f + g) =
          ((KFlatFixedTensor.derivedTensor R).obj H).map f +
            ((KFlatFixedTensor.derivedTensor R).obj H).map g) ∧
      (∀ (X Y : D R) (f g : X ⟶ Y),
        ((KFlatFixedTensor.derivedTensor R).flip.obj H).map (f + g) =
          ((KFlatFixedTensor.derivedTensor R).flip.obj H).map f +
            ((KFlatFixedTensor.derivedTensor R).flip.obj H).map g) := by
  intro H
  let W := (HomotopyCategory.quasiIso (Modules R) (.up ℤ)).inverseImage
    (resolvingHomotopy R).ι
  have : (localization R).IsLocalization W := localization_isLocalization R
  have := Localization.essSurj (localization R) W
  let A := (localization R).objPreimage H
  let e : DerivedCategory.Q.obj A.obj.as ≅ H :=
    (localization R).objObjPreimageIso H
  obtain ⟨s, hs⟩ := KFlatFixedTensor.kFlat_fixed_tensor_triangulated R
  let := s
  have h := (hs A.obj.as A.property.1 A.property.2).2.2.1
  have := h.1
  have := h.2
  have hL : ((KFlatFixedTensor.derivedTensor R).obj H).Additive :=
    Functor.additive_of_iso ((KFlatFixedTensor.derivedTensor R).mapIso e)
  have hR : ((KFlatFixedTensor.derivedTensor R).flip.obj H).Additive :=
    Functor.additive_of_iso ((KFlatFixedTensor.derivedTensor R).flip.mapIso e)
  refine ⟨hL, hR, ?_, ?_, ?_⟩
  · intro X Y b hb
    have := preservesBinaryBiproducts_of_preservesBiproducts
      ((KFlatFixedTensor.derivedTensor R).obj H)
    have := preservesBinaryBiproducts_of_preservesBiproducts
      ((KFlatFixedTensor.derivedTensor R).flip.obj H)
    exact ⟨⟨isBinaryBilimitOfPreserves _ hb⟩, ⟨isBinaryBilimitOfPreserves _ hb⟩⟩
  · intro X Y f g
    exact Functor.map_add _ (f := f) (g := g)
  · intro X Y f g
    exact Functor.map_add _ (f := f) (g := g)

end SheafOfModules.DerivedTensorConstraints
