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
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
public import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
public import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
public import Mathlib.CategoryTheory.Products.Associator
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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

end

section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift Z ℤ]
  (T : A ⥤ B ⥤ Z) [∀ X, (T.flip.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.flip.map f) ℤ]

end

section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift Z ℤ]
  (T : A ⥤ B ⥤ Z) [∀ X, (T.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.map f) ℤ]
  [∀ X, (T.flip.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.flip.map f) ℤ]

end

section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [HasShift B ℤ] [HasShift Z ℤ]

end

section
variable {A CC H Z : Type*} [Category* A] [Category* CC] [Category* H] [Category* Z]
  {q : CC ⥤ H} {Q : H ⥤ Z} {F : CC × CC ⥤ CC} {P : ObjectProperty H}

end

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

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

private theorem flat_of_isZero (P : Modules R) (hP : IsZero P) :
    SheafOfModules.IsFlatOnSite (J := J) (R := R) P := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive R
  have h : ObjectProperty.flat P := ObjectProperty.prop_of_isZero _ hP
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R P).symm h.2

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

omit [HasDerivedCategory.{w} (Modules R)] in
omit [HasDerivedCategory.{w} (Modules R)] in
omit [HasDerivedCategory.{w} (Modules R)] in
end

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

omit [HasDerivedCategory (Modules R)] in
omit [HasDerivedCategory (Modules R)] in
private theorem totalTensor_map {E E' F F' : Complex R}
    (f : E ⟶ E') (g : F ⟶ F') :
    (Functor.uncurry.obj (KFlatFixedTensor.totalTensor R)).map (Prod.mkHom f g) =
      f ⊗ₘ g := by
  rw [MonoidalCategory.tensorHom_def]
  rfl

private abbrev modelLocalization : Model R ⥤ D R :=
  (resolvingComplex R).ι ⋙ DerivedCategory.Q

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

omit [HasDerivedCategory (Modules R)] in
attribute [local irreducible] representative

attribute [local irreducible] representativeNatIso

omit [HasDerivedCategory (Modules R)] in
attribute [local irreducible] nativePairShift

end

attribute [local irreducible] modelShift modelAssociator modelSymmetry

end SheafOfModules.DerivedTensorConstraints
