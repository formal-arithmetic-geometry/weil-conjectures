# FiniteFieldDerivedTensor comparison interfaces

## Reason

Extract the original interfaces into their own module to let the chain retraction
and representative theorem depend on them without an import cycle. The assigned
module publicly imports that interface. All original public signatures and public
imports are preserved, and the source library is unchanged.

The ordinary tensor wrapper is checked against the original curried tensor by
`rfl`. The generic totalization now has a canonical model containing its functor
and bidegree inclusions. `exists_model` is proved using the concrete Mathlib
construction; `model_eq` determines all chosen data by equality to that construction.
`totalFunctor_eq_mathlib` identifies the new wrapper with the original functor.
Consequently the definitions still mean exactly the original constructions. No
model data comes from an unproved or undetermined existence assertion.

The chain file proves raw totalization for arbitrary categories, then transports
the whole result through the model equality using a model-parameterized predicate.
This avoids expensive conversion of chosen coproducts during sheaf specialization.
All retraction and totalization proof helpers stay in the chain file; no file or proof is split to evade the
compile limit. The assigned module explicitly transports its derived presentation
along the same equality. Its target statement is unchanged.

## Old

The following block occurred in `Sheaf.Paper.FiniteFieldDerivedTensorSummand`, in
`namespace FiniteFieldDerivedTensor` with the original variable context.

```lean
noncomputable abbrev coefficients (A : Type (max u v)) [CommRing A] :=
  (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of A)

/-- Its underlying ring sheaf, using the canonical forgetful functor.
Source: Stacks 03EK (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable abbrev rings (A : Type (max u v)) [CommRing A] :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj (coefficients J A)

/-- The recorded category of modules over the constant ring sheaf.
Source: Stacks 03EK (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable abbrev Modules (A : Type (max u v)) [CommRing A] :=
  ringedSiteModules.{max u v} (rings J A)

/-- Unbounded cochain complexes of those module sheaves.
Source: Stacks 06YN (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable abbrev Complexes (A : Type (max u v)) [CommRing A] :=
  CochainComplex (Modules J A) ℤ

/-- The existing total tensor bifunctor, with direct sums along integer diagonals.
Source: Stacks 06YU (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def total (A : Type (max u v)) [CommRing A] :
    Complexes J A × Complexes J A ⥤ Complexes J A :=
  Functor.uncurry.obj ((@curriedTensor (Modules J A) _
    (SheafOfModules.monoidalCategory (coefficients J A))).map₂HomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- The canonical constant section associated to an element of the coefficient ring.
Source: Stacks 03EK (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def constantSection (A : Type (max u v)) [CommRing A]
    (X : Cᵒᵖ) (a : A) : (coefficients J A).obj.obj X :=
  ((sheafificationAdjunction J CommRingCat.{max u v}).unit.app
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app X a

/-- A pure tensor in the sheaf tensor, through its sheafification presentation.
Source: Stacks 03EK, 0GMW (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def tensorSection (A : Type (max u v)) [CommRing A]
    (M N : Modules J A) (X : Cᵒᵖ) (m : M.val.obj X) (n : N.val.obj X) :
    ((@tensorObj (Modules J A) _ (SheafOfModules.monoidalCategory
      (coefficients J A)).toMonoidalCategoryStruct M N).val.obj X) :=
  ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app X)
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (rings J A).obj)).unit.app
      (PresheafOfModules.Monoidal.tensorObj M.val N.val)).app X
        (TensorProduct.tmul ((coefficients J A).obj.obj X) m n))

/-- A pure tensor in bidegree `(i,j)` included in the total complex.
Source: Stacks 06YU (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def generator (A : Type (max u v)) [CommRing A]
    (K L : Complexes J A) (i j : ℤ) (X : Cᵒᵖ)
    (m : (K.X i).val.obj X) (n : (L.X j).val.obj X) :
    (((total J A).obj (K, L)).X (i + j)).val.obj X :=
  ((CochainComplex.ιMapBifunctor K L (@curriedTensor (Modules J A) _
    (SheafOfModules.monoidalCategory (coefficients J A))) i j (i + j) rfl).val.app X)
      (tensorSection J A (K.X i) (L.X j) X m n)

/-- The existing constant-sheaf ring morphism of a field extension.
Source: Stacks 03EK (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def coefficientMap (F B : Type (max u v))
    [Field F] [Field B] [Algebra F B] : rings J F ⟶ rings J B :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).map
    ((constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom (algebraMap F B)))

/-- Termwise restriction of scalars, using the recorded restriction functor.
Source: Stacks 03EK (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def restrictComplex (F B : Type (max u v))
    [Field F] [Field B] [Algebra F B] : Complexes J B ⥤ Complexes J F :=
  (SheafOfModules.restrictScalars.{max u v} (coefficientMap J F B)).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- The full subcategory of compatible flat-term K-flat representatives.
Source: Stacks 06YN, 06YS (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def representatives (A : Type (max u v)) [CommRing A] :
    ObjectProperty (Complexes J A) :=
  fun K ↦ K.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, exactFunctor _ _
    ((@curriedTensor (Modules J A) _
      (SheafOfModules.monoidalCategory (coefficients J A))).flip.obj (K.X n))

variable (A : Type (max u v)) [CommRing A]
  [HasDerivedCategory.{w} (Modules J A)]

/-- The existing unbounded derived category.
Source: Stacks 06YU (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable abbrev Derived := DerivedCategory (Modules J A)

/-- The representative comparison for a tensor functor supplied by derived tensor descent.
This is packaging of the recorded tensor-computation clause, not another tensor definition.
Source: Stacks 06YU (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
structure Presentation where
  tensor : Derived J A × Derived J A ⥤ Derived J A
  comparison : ((representatives J A).ι.prod (representatives J A).ι) ⋙ total J A ⋙
    DerivedCategory.Q ≅
    (((representatives J A).ι ⋙ DerivedCategory.Q).prod
      ((representatives J A).ι ⋙ DerivedCategory.Q)) ⋙ tensor

variable {J}
variable {F B : Type (max u v)} [Field F] [Field B] [Algebra F B]
  [HasDerivedCategory.{w} (Modules J F)] [HasDerivedCategory.{w} (Modules J B)]

/-- The source tensor after restriction, as an existing tensor bifunctor composite.
Source: Stacks 06YU (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def source (TF : Presentation J F)
    (res : Derived J B ⥤ Derived J F) :
    Derived J B × Derived J B ⥤ Derived J F := (res.prod res) ⋙ TF.tensor

/-- The target tensor followed by restriction.
Source: Stacks 06YU (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def target (TB : Presentation J B)
    (res : Derived J B ⥤ Derived J F) :
    Derived J B × Derived J B ⥤ Derived J F := TB.tensor ⋙ res

/-- The canonical source comparison on compatible K-flat representatives.
Source: Stacks 06YU (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def sourceComparison (TF : Presentation J F)
    (res : Derived J B ⥤ Derived J F)
    (r : restrictComplex J F B ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ res)
    (K L : Complexes J B)
    (hK : representatives J F ((restrictComplex J F B).obj K))
    (hL : representatives J F ((restrictComplex J F B).obj L)) :
    DerivedCategory.Q.obj ((total J F).obj
      ((restrictComplex J F B).obj K, (restrictComplex J F B).obj L)) ≅
      (source TF res).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  TF.comparison.app (⟨(restrictComplex J F B).obj K, hK⟩,
    ⟨(restrictComplex J F B).obj L, hL⟩) ≪≫
      TF.tensor.mapIso ((r.app K).prod (r.app L))

/-- The canonical target comparison on flat-term K-flat representatives.
Source: Stacks 06YU (blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def targetComparison (TB : Presentation J B)
    (res : Derived J B ⥤ Derived J F)
    (r : restrictComplex J F B ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ res)
    (K L : Complexes J B) (hK : representatives J B K) (hL : representatives J B L) :
    DerivedCategory.Q.obj ((restrictComplex J F B).obj ((total J B).obj (K, L))) ≅
      (target TB res).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  r.app ((total J B).obj (K, L)) ≪≫ res.mapIso (TB.comparison.app (⟨K, hK⟩, ⟨L, hL⟩))

/-- The canonical coefficient action and balanced tensor map on total complexes,
with their pure-generator characterization in every bidegree.
Source: Stacks 03EK, 0GMW, 06YU
(blueprint: lem-pur-finite-field-derived-tensor-summand). -/
structure ChainComparison where
  chainAction : ∀ K L : Complexes J B,
    (B ⊗[F] B) →+* End ((total J F).obj
      ((restrictComplex J F B).obj K, (restrictComplex J F B).obj L))
  chainBalanced :
    ((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F ⟶
      total J B ⋙ restrictComplex J F B
  action_generator : ∀ (K L : Complexes J B) (a b : B) (i j : ℤ) (X : Cᵒᵖ)
      (m : (K.X i).val.obj X) (n : (L.X j).val.obj X),
    (((chainAction K L) (a ⊗ₜ[F] b)).f (i + j)).val.app X
      (generator J F ((restrictComplex J F B).obj K)
        ((restrictComplex J F B).obj L) i j X m n) =
    generator J F ((restrictComplex J F B).obj K)
      ((restrictComplex J F B).obj L) i j X
        (constantSection J B X a • m) (constantSection J B X b • n)
  balanced_generator : ∀ (K L : Complexes J B) (i j : ℤ) (X : Cᵒᵖ)
      (m : (K.X i).val.obj X) (n : (L.X j).val.obj X),
    (((chainBalanced.app (K, L)).f (i + j)).val.app X)
      (generator J F ((restrictComplex J F B).obj K)
        ((restrictComplex J F B).obj L) i j X m n) = generator J B K L i j X m n

/-- The natural split-retraction formulation of the asserted diagonal-summand isomorphism.
The pure-generator equations pin down the coefficient action and balanced quotient before
localization; the comparison squares pin them down on arbitrary derived objects and arrows.
`balanced ≫ splitting = action e` identifies the split image with the termwise e-image.
Source: Stacks 0C2X, 03EK, 06YU and the node's explicit derived formulation
(blueprint: lem-pur-finite-field-derived-tensor-summand). -/
noncomputable def HasDiagonalComparison (TF : Presentation J F) (TB : Presentation J B)
    (e : B ⊗[F] B) : Prop :=
  ∃ (res : Derived J B ⥤ Derived J F)
    (restriction : restrictComplex J F B ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ res)
    (compatible : ∀ K : Complexes J B, representatives J B K →
      representatives J F ((restrictComplex J F B).obj K))
    (action : (B ⊗[F] B) →+* End (source TF res))
    (balanced : source TF res ⟶ target TB res)
    (splitting : target TB res ⟶ source TF res)
    (chain : ChainComparison (J := J) (F := F) (B := B)),
    (splitting ≫ balanced = 𝟙 (target TB res)) ∧
    (balanced ≫ splitting = action e) ∧
    (∀ (K L : Complexes J B)
      (hK : representatives J B K) (hL : representatives J B L) (x : B ⊗[F] B),
      DerivedCategory.Q.map (chain.chainAction K L x) ≫
        (sourceComparison TF res restriction K L (compatible K hK) (compatible L hL)).hom =
      (sourceComparison TF res restriction K L (compatible K hK) (compatible L hL)).hom ≫
        (action x).app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ∧
    (∀ (K L : Complexes J B)
      (hK : representatives J B K) (hL : representatives J B L),
      DerivedCategory.Q.map (chain.chainBalanced.app (K, L)) ≫
        (targetComparison TB res restriction K L hK hL).hom =
      (sourceComparison TF res restriction K L (compatible K hK) (compatible L hL)).hom ≫
        balanced.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L))

```

## New

The complete replacement interface module is:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-!
# The diagonal summand for finite-field derived tensor

Source: Stacks Project, Tag 0C2X, finite-extension diagonal; Tags 03EK, 0GMW,
06YN, 06YS, 06YT and 06YU for the agent-formulated sheaf and derived comparison
(blueprint: def-pur-finite-field-derived-tensor-comparison).

The comparison is expressed as a natural split retraction. Its projector is the tensor-square
coefficient action, and both that action and the quotient map are specified on pure tensors
in every bidegree of the total complex. Thus its split image is exactly the termwise
idempotent summand, and its quotient map is the canonical balanced tensor morphism.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct

namespace CochainTensorBifunctor

variable {A B D : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} D]
  [HasZeroMorphisms A] [HasZeroMorphisms B] [Preadditive D] [HasCoproducts.{0} D]
  (F : A ⥤ B ⥤ D) [F.PreservesZeroMorphisms]
  [∀ X : A, (F.obj X).PreservesZeroMorphisms]

/-- Mathlib's direct-sum totalization, before packaging its generator API.
Source: Stacks 06YU (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable def rawFunctor :
    CochainComplex A ℤ × CochainComplex B ℤ ⥤ CochainComplex D ℤ :=
  Functor.uncurry.obj (F.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))

/-- A total functor and its bidegree inclusions.
Source: Stacks 06YU (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
structure Model where
  functor : CochainComplex A ℤ × CochainComplex B ℤ ⥤ CochainComplex D ℤ
  inclusion : ∀ (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (i j n : ℤ) (_h : i + j = n),
    (F.obj (K.X i)).obj (L.X j) ⟶ (functor.obj (K, L)).X n

/-- Mathlib's totalization and inclusions give the canonical model.
Source: Stacks 06YU (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable def rawModel : Model F where
  functor := rawFunctor F
  inclusion K L i j n h :=
    HomologicalComplex.ιMapBifunctor K L F (.up ℤ) i j n h

/-- The model is specified by equality with the concrete Mathlib construction.
Source: Stacks 06YU (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
theorem exists_model : ∃ M : Model F, M = rawModel F := ⟨_, rfl⟩

/-- The canonical model, with all data fixed by equality to `rawModel`.
Source: Stacks 06YU (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable def model : Model F := Classical.choose (exists_model F)

/-- Both the functor and every inclusion are exactly Mathlib's construction.
Source: Stacks 06YU (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
theorem model_eq : model F = rawModel F := Classical.choose_spec (exists_model F)

/-- The standard direct-sum totalization with a shared model API.
Source: Stacks 06YU (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable def totalFunctor :
    CochainComplex A ℤ × CochainComplex B ℤ ⥤ CochainComplex D ℤ :=
  (model F).functor

/-- The canonical inclusion of a bidegree into the total complex.
Source: Stacks 06YU (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable def inclusion (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (i j n : ℤ) (h : i + j = n) :
    (F.obj (K.X i)).obj (L.X j) ⟶ ((totalFunctor F).obj (K, L)).X n :=
  (model F).inclusion K L i j n h

/-- The shared total functor equals the original Mathlib total functor.
Source: Stacks 06YU (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
theorem totalFunctor_eq_mathlib : totalFunctor F = rawFunctor F := by
  unfold totalFunctor
  rw [model_eq]
  rfl

end CochainTensorBifunctor

namespace FiniteFieldDerivedTensor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{max u v}]

/-- The existing constant commutative-ring sheaf.
Source: Stacks 03EK (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable abbrev coefficients (A : Type (max u v)) [CommRing A] :=
  (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of A)

/-- Its underlying ring sheaf, using the canonical forgetful functor.
Source: Stacks 03EK (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable abbrev rings (A : Type (max u v)) [CommRing A] :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj (coefficients J A)

/-- The recorded category of modules over the constant ring sheaf.
Source: Stacks 03EK (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable abbrev Modules (A : Type (max u v)) [CommRing A] :=
  ringedSiteModules.{max u v} (rings J A)

/-- Unbounded cochain complexes of those module sheaves.
Source: Stacks 06YN (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable abbrev Complexes (A : Type (max u v)) [CommRing A] :=
  CochainComplex (Modules J A) ℤ

/-- The existing tensor bifunctor with its chosen module-sheaf monoidal structure.
Source: Stacks 03EK (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable def tensorFunctor (A : Type (max u v)) [CommRing A] :
    Modules J A ⥤ Modules J A ⥤ Modules J A :=
  @curriedTensor (Modules J A) _ (SheafOfModules.monoidalCategory (coefficients J A))

/-- The existing tensor bifunctor preserves zero morphisms in its first variable.
Source: Stacks 03EK (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
instance tensorFunctor_preservesZeroMorphisms (A : Type (max u v)) [CommRing A] :
    (tensorFunctor J A).PreservesZeroMorphisms :=
  inferInstanceAs ((@curriedTensor (Modules J A) _
    (SheafOfModules.monoidalCategory (coefficients J A))).PreservesZeroMorphisms)

/-- The existing tensor bifunctor preserves zero morphisms in its second variable.
Source: Stacks 03EK (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
instance tensorFunctor_obj_preservesZeroMorphisms (A : Type (max u v)) [CommRing A]
    (M : Modules J A) : ((tensorFunctor J A).obj M).PreservesZeroMorphisms :=
  inferInstanceAs (((@curriedTensor (Modules J A) _
    (SheafOfModules.monoidalCategory (coefficients J A))).obj M).PreservesZeroMorphisms)

private theorem tensorFunctor_eq_mathlib (A : Type (max u v)) [CommRing A] :
    tensorFunctor J A =
      @curriedTensor (Modules J A) _
        (SheafOfModules.monoidalCategory (coefficients J A)) := rfl

/-- The existing total tensor bifunctor, with direct sums along integer diagonals.
Source: Stacks 06YU (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable def total (A : Type (max u v)) [CommRing A] :
    Complexes J A × Complexes J A ⥤ Complexes J A :=
  CochainTensorBifunctor.totalFunctor (tensorFunctor J A)

-- The model equality fixes both the totalization functor and its bidegree inclusions.
-- Specialization can use this API without expanding the chosen direct sums.
private theorem total_eq_mathlib (A : Type (max u v)) [CommRing A] :
    total J A = Functor.uncurry.obj ((tensorFunctor J A).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :=
  CochainTensorBifunctor.totalFunctor_eq_mathlib (tensorFunctor J A)

/-- The canonical constant section associated to an element of the coefficient ring.
Source: Stacks 03EK (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable def constantSection (A : Type (max u v)) [CommRing A]
    (X : Cᵒᵖ) (a : A) : (coefficients J A).obj.obj X :=
  ((sheafificationAdjunction J CommRingCat.{max u v}).unit.app
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app X a

/-- A pure tensor in the sheaf tensor, through its sheafification presentation.
Source: Stacks 03EK, 0GMW (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable def tensorSection (A : Type (max u v)) [CommRing A]
    (M N : Modules J A) (X : Cᵒᵖ) (m : M.val.obj X) (n : N.val.obj X) :
    ((@tensorObj (Modules J A) _ (SheafOfModules.monoidalCategory
      (coefficients J A)).toMonoidalCategoryStruct M N).val.obj X) :=
  ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app X)
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (rings J A).obj)).unit.app
      (PresheafOfModules.Monoidal.tensorObj M.val N.val)).app X
        (TensorProduct.tmul ((coefficients J A).obj.obj X) m n))

/-- A pure tensor in bidegree `(i,j)` included in the total complex.
Source: Stacks 06YU (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable def generator (A : Type (max u v)) [CommRing A]
    (K L : Complexes J A) (i j : ℤ) (X : Cᵒᵖ)
    (m : (K.X i).val.obj X) (n : (L.X j).val.obj X) :
    (((total J A).obj (K, L)).X (i + j)).val.obj X :=
  ((CochainTensorBifunctor.inclusion (tensorFunctor J A) K L i j
    (i + j) rfl).val.app X)
      (tensorSection J A (K.X i) (L.X j) X m n)

/-- The existing constant-sheaf ring morphism of a field extension.
Source: Stacks 03EK (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable def coefficientMap (F B : Type (max u v))
    [Field F] [Field B] [Algebra F B] : rings J F ⟶ rings J B :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).map
    ((constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom (algebraMap F B)))

/-- Termwise restriction of scalars, using the recorded restriction functor.
Source: Stacks 03EK (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable def restrictComplex (F B : Type (max u v))
    [Field F] [Field B] [Algebra F B] : Complexes J B ⥤ Complexes J F :=
  (SheafOfModules.restrictScalars.{max u v} (coefficientMap J F B)).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- The full subcategory of compatible flat-term K-flat representatives.
Source: Stacks 06YN, 06YS (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable def representatives (A : Type (max u v)) [CommRing A] :
    ObjectProperty (Complexes J A) :=
  fun K ↦ K.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, exactFunctor _ _
    ((tensorFunctor J A).flip.obj (K.X n))

variable (A : Type (max u v)) [CommRing A]
  [HasDerivedCategory.{w} (Modules J A)]

/-- The existing unbounded derived category.
Source: Stacks 06YU (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable abbrev Derived := DerivedCategory (Modules J A)

/-- The representative comparison for a tensor functor supplied by derived tensor descent.
This is packaging of the recorded tensor-computation clause, not another tensor definition.
Source: Stacks 06YU (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
structure Presentation where
  tensor : Derived J A × Derived J A ⥤ Derived J A
  comparison : ((representatives J A).ι.prod (representatives J A).ι) ⋙ total J A ⋙
    DerivedCategory.Q ≅
    (((representatives J A).ι ⋙ DerivedCategory.Q).prod
      ((representatives J A).ι ⋙ DerivedCategory.Q)) ⋙ tensor

variable {J}
variable {F B : Type (max u v)} [Field F] [Field B] [Algebra F B]
  [HasDerivedCategory.{w} (Modules J F)] [HasDerivedCategory.{w} (Modules J B)]

/-- The source tensor after restriction, as an existing tensor bifunctor composite.
Source: Stacks 06YU (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable def source (TF : Presentation J F)
    (res : Derived J B ⥤ Derived J F) :
    Derived J B × Derived J B ⥤ Derived J F := (res.prod res) ⋙ TF.tensor

/-- The target tensor followed by restriction.
Source: Stacks 06YU (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable def target (TB : Presentation J B)
    (res : Derived J B ⥤ Derived J F) :
    Derived J B × Derived J B ⥤ Derived J F := TB.tensor ⋙ res

/-- The canonical source comparison on compatible K-flat representatives.
Source: Stacks 06YU (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable def sourceComparison (TF : Presentation J F)
    (res : Derived J B ⥤ Derived J F)
    (r : restrictComplex J F B ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ res)
    (K L : Complexes J B)
    (hK : representatives J F ((restrictComplex J F B).obj K))
    (hL : representatives J F ((restrictComplex J F B).obj L)) :
    DerivedCategory.Q.obj ((total J F).obj
      ((restrictComplex J F B).obj K, (restrictComplex J F B).obj L)) ≅
      (source TF res).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  TF.comparison.app (⟨(restrictComplex J F B).obj K, hK⟩,
    ⟨(restrictComplex J F B).obj L, hL⟩) ≪≫
      TF.tensor.mapIso ((r.app K).prod (r.app L))

/-- The canonical target comparison on flat-term K-flat representatives.
Source: Stacks 06YU (blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable def targetComparison (TB : Presentation J B)
    (res : Derived J B ⥤ Derived J F)
    (r : restrictComplex J F B ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ res)
    (K L : Complexes J B) (hK : representatives J B K) (hL : representatives J B L) :
    DerivedCategory.Q.obj ((restrictComplex J F B).obj ((total J B).obj (K, L))) ≅
      (target TB res).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  r.app ((total J B).obj (K, L)) ≪≫ res.mapIso (TB.comparison.app (⟨K, hK⟩, ⟨L, hL⟩))

/-- The canonical coefficient action and balanced tensor map on total complexes,
with their pure-generator characterization in every bidegree.
Source: Stacks 03EK, 0GMW, 06YU
(blueprint: def-pur-finite-field-derived-tensor-comparison). -/
structure ChainComparison where
  chainAction : ∀ K L : Complexes J B,
    (B ⊗[F] B) →+* End ((total J F).obj
      ((restrictComplex J F B).obj K, (restrictComplex J F B).obj L))
  chainBalanced :
    ((restrictComplex J F B).prod (restrictComplex J F B)) ⋙ total J F ⟶
      total J B ⋙ restrictComplex J F B
  action_generator : ∀ (K L : Complexes J B) (a b : B) (i j : ℤ) (X : Cᵒᵖ)
      (m : (K.X i).val.obj X) (n : (L.X j).val.obj X),
    (((chainAction K L) (a ⊗ₜ[F] b)).f (i + j)).val.app X
      (generator J F ((restrictComplex J F B).obj K)
        ((restrictComplex J F B).obj L) i j X m n) =
    generator J F ((restrictComplex J F B).obj K)
      ((restrictComplex J F B).obj L) i j X
        (constantSection J B X a • m) (constantSection J B X b • n)
  balanced_generator : ∀ (K L : Complexes J B) (i j : ℤ) (X : Cᵒᵖ)
      (m : (K.X i).val.obj X) (n : (L.X j).val.obj X),
    (((chainBalanced.app (K, L)).f (i + j)).val.app X)
      (generator J F ((restrictComplex J F B).obj K)
        ((restrictComplex J F B).obj L) i j X m n) = generator J B K L i j X m n

/-- The natural split-retraction formulation of the asserted diagonal-summand isomorphism.
The pure-generator equations pin down the coefficient action and balanced quotient before
localization; the comparison squares pin them down on arbitrary derived objects and arrows.
`balanced ≫ splitting = action e` identifies the split image with the termwise e-image.
Source: Stacks 0C2X, 03EK, 06YU and the node's explicit derived formulation
(blueprint: def-pur-finite-field-derived-tensor-comparison). -/
noncomputable def HasDiagonalComparison (TF : Presentation J F) (TB : Presentation J B)
    (e : B ⊗[F] B) : Prop :=
  ∃ (res : Derived J B ⥤ Derived J F)
    (restriction : restrictComplex J F B ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ res)
    (compatible : ∀ K : Complexes J B, representatives J B K →
      representatives J F ((restrictComplex J F B).obj K))
    (action : (B ⊗[F] B) →+* End (source TF res))
    (balanced : source TF res ⟶ target TB res)
    (splitting : target TB res ⟶ source TF res)
    (chain : ChainComparison (J := J) (F := F) (B := B)),
    (splitting ≫ balanced = 𝟙 (target TB res)) ∧
    (balanced ≫ splitting = action e) ∧
    (∀ (K L : Complexes J B)
      (hK : representatives J B K) (hL : representatives J B L) (x : B ⊗[F] B),
      DerivedCategory.Q.map (chain.chainAction K L x) ≫
        (sourceComparison TF res restriction K L (compatible K hK) (compatible L hL)).hom =
      (sourceComparison TF res restriction K L (compatible K hK) (compatible L hL)).hom ≫
        (action x).app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ∧
    (∀ (K L : Complexes J B)
      (hK : representatives J B K) (hL : representatives J B L),
      DerivedCategory.Q.map (chain.chainBalanced.app (K, L)) ≫
        (targetComparison TB res restriction K L hK hL).hom =
      (sourceComparison TF res restriction K L (compatible K hK) (compatible L hL)).hom ≫
        balanced.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L))

end FiniteFieldDerivedTensor
```

## Users

`tools/downstream.py` finds one current library importer of the assigned module.
The other rows are the modules introduced or adapted in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.FiniteFieldDerivedTensorSummand` | R1 | Publicly imports the extracted interfaces; proves the theorem and transports the presentation through the totalization equality. |
| `Sheaf.Paper.FiniteFieldDerivedTensorComparison` | R1 | Original interfaces plus a canonical model fixed to the Mathlib construction by proved equality. |
| `Sheaf.Paper.SeparableFieldTensorChain` | R1 | Uses the canonical model and proves totalization of the ordinary split retraction. |
| `Sheaf.Paper.SeparableFieldTensorSheaf` | R1 | States the ordinary sheaf retraction using the extracted interfaces. |
| `Sheaf.Paper.ConstantFieldRestrictionRepresentatives` | R1 | Proves representative compatibility using the extracted interfaces. |
| `Sheaf.CategoryTheory.DescentSplitTensorAction` | R1 | Proved generic descent helper used by the assigned proof. |
| `Sheaf.RingTheory.FiniteAlgebraExternalTensorFiltration` | unclaimed | Existing importer; source unchanged; compiled against the packet before delivery. |

The source restored after the returned landing is unrelated and is not edited here.
The original public imports move verbatim to the interface; none is hidden.

## Status

landed 20261022T002433-L-1930318 2026-10-22 (merge of deliver/R1/Sheaf.Paper.FiniteFieldDerivedTensorSummand)
