/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
public import Sheaf.Algebra.Homology.KFlatTotalTensorModel
public import Mathlib.CategoryTheory.Products.Associator
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Localization.Pi
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

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

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.DerivedTensorConstraints

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- The existing ordinary module-sheaf category.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev Modules := KFlatFixedTensor.Modules R

/-- The existing category of integer-indexed, unbounded cochain complexes.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints). -/
abbrev Complex := CochainComplex (Modules R) ℤ

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

/-- Resolving models are closed under tensor, every integer shift and finite sums.
Flat sheaves give resolving degree-zero complexes, and their ordinary tensor is flat.
The degree-zero derived comparison is induced by r and the normalized chain comparison.
Source: Stacks 07A2, 06YU and 0FPT
(blueprint: lem-pur-derived-tensor-additive-constraints).

Proof plan: use lem-pur-kflat-total-tensor-model for tensor and termwise flatness,
lem-weil-pbc-kflat-fixed-tensor-triangulated for shifts, and lem-pc-kflat-closure
for finite sums by extending a finite family by zeros to a countable family.
A flat sheaf in degree zero is bounded above and flat, hence K-flat by that closure
lemma. Tensor two such models: all summands except (0,0) vanish. The surviving
summand identifies the total with the degree-zero ordinary tensor, which is flat
by termwise flatness. Compose this chain identification with the inverse of r to
obtain exactly the displayed derived comparison.
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
  sorry

/-- Unique derived natural constraints with the specified representative squares.
Source: Stacks 0FPT (blueprint: lem-pur-derived-tensor-additive-constraints).

Proof plan: (1) total tensors, shifts and finite sums stay resolving by
lem-pur-kflat-total-tensor-model, lem-weil-pbc-kflat-fixed-tensor-triangulated and
lem-pc-kflat-closure. (2) The descent equivalence makes q restricted to resolving
homotopy objects a localization. Apply lem-sfb-product-localization and the full
faithfulness in lem-weil-pbc-localization-universal-property for two and three
variables. (3) Use the unsigned chain associator, signed chain symmetry and the
right-then-left shift extraction of lem-pur-total-tensor-signed-coherence.
(4) Conjugate the chain associator by leftRepresentative and rightRepresentative.
(5) Insert the published r and Q.commShiftIso in the shift and symmetry formulas.
Extend each transformation and its inverse by full faithfulness; their composites
are identities by faithfulness. (6) Faithfulness gives uniqueness of the natural
isomorphisms with precisely these squares, rather than uniqueness of objectwise isos.
-/
theorem existsUnique_derived_tensor_constraints :
    ∃! s : (∀ a b : ℤ, shiftedSource R a b ≅ shiftedTarget R a b) ×
        (leftAssociated R ≅ rightAssociated R) × (tensor R ≅ swapped R),
      IsNormalized R s.1 s.2.1 s.2.2 := by
  sorry

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
  sorry

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
  sorry

end SheafOfModules.DerivedTensorConstraints
