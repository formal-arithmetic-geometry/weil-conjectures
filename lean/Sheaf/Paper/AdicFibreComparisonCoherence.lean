/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.AdicFibreComparisonData

/-! # Normalization and coherence data for geometric fibres

Source: Bhatt--Scholze 6.8.4, 6.8.14 and 6.8.15
(blueprint: def-per-adic-fibre-coherence-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.AdicFibreComparison
open ContinuousRational

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (R : ContinuousRational.Family.{u} l)
variable (E L : Type u) [Field E] [Field L] [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The comparison family quantifies every finite coefficient field and every extension.
Source: BS 6.8.4, 6.8.14 (blueprint: def-per-adic-fibre-coherence-data). -/
abbrev AllComparisons (ω : Fibres (k := k) l R) :=
  ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B], Comparisons l R A B ω

/-- Equations for identities, composition, scalar associators and the mixed square.
All heart isomorphisms are fixed by their underlying raw comparisons.
Source: BS 6.8.4, 6.8.14--6.8.15
(blueprint: def-per-adic-fibre-coherence-data). -/
structure Coherence (ω : Fibres (k := k) l R) (c : AllComparisons l R ω) : Prop where
  pull_id : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (X : FiniteTypeBase k),
    ∃ e : heartPull l A R (𝟙 X.scheme) ≅ 𝟭 _,
      (∀ F, HEq (e.hom.app F).hom ((R.identity A (base l X)).raw.hom.app F.obj)) ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
        (F : NormalizedFibre.Heart l A (base l X)),
        HEq (((c A A).pull (𝟙 X.scheme) κ x).hom.app F)
          (((ω A X).point κ x).functor.map (e.hom.app F))
  pull_comp : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (X Y Z : FiniteTypeBase k)
    (g : Y.scheme ⟶ X.scheme) (h : Z.scheme ⟶ Y.scheme),
    ∃ e : heartPull l A R (h ≫ g) ≅ heartPull l A R g ⋙ heartPull l A R h,
      (∀ F, HEq (e.hom.app F).hom
        ((R.composition A (X := base l Y) (Y := base l X) (Z := base l Z) g h).raw.hom.app
          F.obj)) ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (z : Spec (.of κ) ⟶ Z.scheme)
        (F : NormalizedFibre.Heart l A (base l X)),
        HEq (((c A A).pull (h ≫ g) κ z).hom.app F)
          (((ω A Z).point κ z).functor.map (e.hom.app F) ≫
            ((c A A).pull h κ z).hom.app ((heartPull l A R g).obj F) ≫
              ((c A A).pull g κ (z ≫ h)).hom.app F)
  scalar_id : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (X : FiniteTypeBase k),
    ∃ e : heartScalar l A A (AlgHom.id ℚ_[l] A) X ≅ 𝟭 _,
      (∀ F, HEq (e.hom.app F).hom
        ((pbcRationalScalarUnit l A X.scheme (base l X).dimension
          (base l X).prime_unit).hom.app F.obj)) ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
        (F : NormalizedFibre.Heart l A (base l X)),
        ((c A A).scalar (AlgHom.id ℚ_[l] A) X κ x).hom.app F ≫
          (ModuleCat.extendScalarsId.{u, u + 1} A).hom.app
            (((ω A X).point κ x).functor.obj F) =
          ((ω A X).point κ x).functor.map (e.hom.app F)
  scalar_comp : ∀ (A B C : Type u) [Field A] [Field B] [Field C]
    [Algebra ℚ_[l] A] [Algebra ℚ_[l] B] [Algebra ℚ_[l] C]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    [FiniteDimensional ℚ_[l] C] (i : A →ₐ[ℚ_[l]] B) (j : B →ₐ[ℚ_[l]] C)
    (X : FiniteTypeBase k),
    ∃ e : heartScalar l A B i X ⋙ heartScalar l B C j X ≅
      heartScalar l A C (j.comp i) X,
      (∀ F, HEq (e.hom.app F).hom
        (pbcRationalScalarCompComponent l A B C i j X.scheme
          (base l X).dimension (base l X).prime_unit F.obj).hom) ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
        (F : NormalizedFibre.Heart l A (base l X)),
        ((ω C X).point κ x).functor.map (e.hom.app F) ≫
          ((c A C).scalar (j.comp i) X κ x).hom.app F ≫
            (ModuleCat.extendScalarsComp.{u, u + 1} i.toRingHom j.toRingHom).hom.app
              (((ω A X).point κ x).functor.obj F) =
          ((c B C).scalar j X κ x).hom.app ((heartScalar l A B i X).obj F) ≫
            (ModuleCat.extendScalars.{u, u, u + 1} j.toRingHom).map
              (((c A B).scalar i X κ x).hom.app F)
  mixed : ∀ (A B : Type u) [Field A] [Field B]
    [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (X Y : FiniteTypeBase k) (g : Y.scheme ⟶ X.scheme),
    ∃ e : heartScalar l A B i X ⋙ heartPull l B R g ≅
      heartPull l A R g ⋙ heartScalar l A B i Y,
      (∀ F, HEq (e.hom.app F).hom
        ((R.mixed A B i (X := base l Y) (Y := base l X) g).raw.hom.app F.obj)) ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme)
        (F : NormalizedFibre.Heart l A (base l X)),
        ((ω B Y).point κ y).functor.map (e.hom.app F) ≫
          ((c A B).scalar i Y κ y).hom.app ((heartPull l A R g).obj F) ≫
            (ModuleCat.extendScalars i.toRingHom).map (((c A A).pull g κ y).hom.app F) =
          ((c B B).pull g κ y).hom.app ((heartScalar l A B i X).obj F) ≫
            ((c A B).scalar i X κ (y ≫ g)).hom.app F

/-- A section germ in the intrinsic fibre, using precisely the tensor-adjunction unit.
Source: Stacks 03Q1; BS 6.8.4 (blueprint: def-per-adic-fibre-coherence-data). -/
def germ {X : Scheme.{u}} (M : pbcModules X (rationalCoefficientSheaf l X E))
    (κ : Type u) [Field κ] (x : Spec (.of κ) ⟶ X) (U : X.ProEt)
    (q : ProEt.mk (𝟙 (Spec (.of κ))) ⟶ (proEtaleBaseChange x).obj U)
    (m : M.val.obj (op U)) : (NormalizedFibre.ambient l E κ x).obj M :=
  ((modulePull x (NormalizedFibre.coefficient l E x)).obj M).val.map q.op
    (moduleUnit x (NormalizedFibre.coefficient l E x) M U m)

/-- Transport of an intrinsic fibre along a specified degree-zero presentation.
Source: BS 6.8.14 (blueprint: def-per-adic-fibre-coherence-data). -/
def presentedFibre (ω : Fibres (k := k) l R) (X : FiniteTypeBase k)
    (F : NormalizedFibre.Heart l E (base l X))
    (M : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
    (e : (R.realization E (base l X)).J.obj F.obj ≅
      (DerivedCategory.singleFunctor _ 0).obj M)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme) :
    ((ω E X).point κ x).functor.obj F ≅ (NormalizedFibre.ambient l E κ x).obj M :=
  (((ω E X).point κ x).intrinsic.app F) ≪≫
    (NormalizedFibre.ambient l E κ x).mapIso
      ((DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M)

/-- The derived pullback map to the ordinary module model, from the specified counit.
Source: BS 6.8.15 (blueprint: def-per-adic-fibre-coherence-data). -/
def pullModelMap {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme)
    (F : NormalizedFibre.Heart l E (base l X))
    (M : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
    (e : (R.realization E (base l X)).J.obj F.obj ≅
      (DerivedCategory.singleFunctor _ 0).obj M) :=
  letI : (modulePull g
    (R.along E (X := base l Y) (Y := base l X) g).coefficient).Additive :=
      (R.along E (X := base l Y) (Y := base l X) g).ordinaryAdditive
  (R.along E (X := base l Y) (Y := base l X) g).comparison.hom.app F.obj ≫
    (derivedPull g (R.along E (X := base l Y) (Y := base l X) g).coefficient).map e.hom ≫
    (R.along E (X := base l Y) (Y := base l X) g).counit.app
      ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (modulePull g (R.along E (X := base l Y) (Y := base l X) g).coefficient)
          (.up ℤ) 0).hom.app M)

/-- The scalar model uses the actual derived-change-of-rings counit, with no chosen map.
Source: BS 6.8.14 (blueprint: def-per-adic-fibre-coherence-data). -/
def scalarModelMap (i : E →ₐ[ℚ_[l]] L) (X : FiniteTypeBase k)
    (F : NormalizedFibre.Heart l E (base l X))
    (M : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
    (e : (R.realization E (base l X)).J.obj F.obj ≅
      (DerivedCategory.singleFunctor _ 0).obj M) :=
  (R.fieldChange E L i (base l X)).comparison.hom.app F.obj ≫
    (pbcDerivedExtend (R.fieldChange E L i (base l X)).coefficient).map e.hom ≫
    pbcComplexCounit (R.fieldChange E L i (base l X)).coefficient
      ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≫
    DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
      (pbcExtend (R.fieldChange E L i (base l X)).coefficient) (.up ℤ) 0).hom.app M)

/-- Normalization on section germs and pure tensors. These equations are imposed for every
presentation, so local lattice charts and their fractional transitions give the same maps.
Source: BS 6.8.4(1),(4),(6), 6.8.14--6.8.15; Stacks 03Q1
(blueprint: def-per-adic-fibre-coherence-data). -/
structure UnitNormalization (ω : Fibres (k := k) l R) (c : AllComparisons l R ω) : Prop where
  pull : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (X Y : FiniteTypeBase k) (g : Y.scheme ⟶ X.scheme)
    (F : NormalizedFibre.Heart l A (base l X))
    (M : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme A))
    (e : (R.realization A (base l X)).J.obj F.obj ≅
      (DerivedCategory.singleFunctor _ 0).obj M),
    ∃ e' : (R.realization A (base l Y)).J.obj ((heartPull l A R g).obj F).obj ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((modulePull g (R.along A (X := base l Y) (Y := base l X) g).coefficient).obj M),
      e'.hom = pullModelMap l R A g F M e ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme)
        (U : X.scheme.ProEt)
        (q : ProEt.mk (𝟙 (Spec (.of κ))) ⟶ (proEtaleBaseChange (y ≫ g)).obj U)
        (q' : ProEt.mk (𝟙 (Spec (.of κ))) ⟶
          (proEtaleBaseChange y).obj ((proEtaleBaseChange g).obj U))
        (_hq : q.left ≫ pullback.fst U.hom (y ≫ g) =
          q'.left ≫ pullback.fst ((proEtaleBaseChange g).obj U).hom y ≫
            pullback.fst U.hom g) (m : M.val.obj (op U)),
        (presentedFibre l R A ω X F M e κ (y ≫ g)).hom
          ((((c A A).pull g κ y).hom.app F)
            ((presentedFibre l R A ω Y ((heartPull l A R g).obj F) _ e' κ y).inv
              (germ l A _ κ y ((proEtaleBaseChange g).obj U) q'
                (moduleUnit g (R.along A (X := base l Y) (Y := base l X) g).coefficient
                  M U m)))) = germ l A M κ (y ≫ g) U q m
  scalar : ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (X : FiniteTypeBase k)
    (F : NormalizedFibre.Heart l A (base l X))
    (M : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme A))
    (e : (R.realization A (base l X)).J.obj F.obj ≅
      (DerivedCategory.singleFunctor _ 0).obj M),
    ∃ e' : (R.realization B (base l X)).J.obj ((heartScalar l A B i X).obj F).obj ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((pbcExtend (R.fieldChange A B i (base l X)).coefficient).obj M),
      e'.hom = scalarModelMap l R A B i X F M e ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
        (U : X.scheme.ProEt)
        (q : ProEt.mk (𝟙 (Spec (.of κ))) ⟶ (proEtaleBaseChange x).obj U)
        (m : M.val.obj (op U)),
        letI : Algebra A B := i.toAlgebra
        ∀ b : B,
        (presentedFibre l R B ω X ((heartScalar l A B i X).obj F) _ e' κ x).hom
          ((((c A B).scalar i X κ x).inv.app F)
            (b ⊗ₜ[A] (presentedFibre l R A ω X F M e κ x).inv
              (germ l A M κ x U q m))) =
          b • germ l B _ κ x U q
            (pbcTensorSection (R.fieldChange A B i (base l X)).coefficient M (op U) 1 m)

/-- Common-stage fibre comparisons are the descent of the finite-stage comparisons.
The transition equation controls the common-stage arrow formula as well as its object values.
Source: BS 6.8.14--6.8.15
(blueprint: def-per-adic-fibre-coherence-data). -/
structure Descent (ω : Fibres (k := k) l R) (c : AllComparisons l R ω)
    (V : CommonAssertions l R Ω ω) : Prop where
  scalar : ∀ (X : FiniteTypeBase k) (A B : Padic.FiniteCoefficientFields l Ω) (h : A ≤ B),
    ∃ z : ModuleCat.extendScalars (pbcFiniteFieldInclusion l Ω h).toRingHom ⋙
        ModuleCat.extendScalars (stageEmbedding l Ω B) ≅
          ModuleCat.extendScalars (stageEmbedding l Ω A),
    ∃ e : heartScalar l (pbcFiniteField.{u} l Ω A) (pbcFiniteField.{u} l Ω B)
        (pbcFiniteFieldInclusion l Ω h) X ⋙ stageHeart l Ω X B ≅ stageHeart l Ω X A,
      (∀ (M : ModuleCat.{u + 1} (pbcFiniteField.{u} l Ω A)),
        letI := (pbcFiniteFieldInclusion l Ω h).toAlgebra
        letI := (stageEmbedding l Ω A).toAlgebra
        letI := (stageEmbedding l Ω B).toAlgebra
        ∀ (a : pbcFiniteField.{u} l Ω B) (b : Ω) (m : M),
          z.hom.app M (b ⊗ₜ[pbcFiniteField.{u} l Ω B]
            (a ⊗ₜ[pbcFiniteField.{u} l Ω A] m)) =
              (b * stageEmbedding l Ω B a) ⊗ₜ[pbcFiniteField.{u} l Ω A] m) ∧
      (∀ F, HEq (e.hom.app F).hom
        (((pbcScalarSystem l Ω X.scheme (base l X).dimension
          (base l X).prime_unit).transIso h).hom.app F.obj)) ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
        (F : NormalizedFibre.Heart l (pbcFiniteField.{u} l Ω A) (base l X)),
        HEq ((V.point X κ x).functor.map (e.hom.app F) ≫
          ((V.point X κ x).finite_stage A).hom.app F)
          (((V.point X κ x).finite_stage B).hom.app
              ((heartScalar l (pbcFiniteField.{u} l Ω A) (pbcFiniteField.{u} l Ω B)
                (pbcFiniteFieldInclusion l Ω h) X).obj F) ≫
            (ModuleCat.extendScalars (stageEmbedding l Ω B)).map
              (((c (pbcFiniteField.{u} l Ω A) (pbcFiniteField.{u} l Ω B)).scalar
                (pbcFiniteFieldInclusion l Ω h) X κ x).hom.app F) ≫
            z.hom.app
                (((ω (pbcFiniteField.{u} l Ω A) X).point κ x).functor.obj F))
  pull : ∀ (X Y : FiniteTypeBase k) (g : Y.scheme ⟶ X.scheme)
    (A : Padic.FiniteCoefficientFields l Ω),
    ∃ e : stageHeart l Ω X A ⋙ commonHeartPull l Ω g ≅
        heartPull l (pbcFiniteField.{u} l Ω A) R g ⋙ stageHeart l Ω Y A,
      (∀ F, HEq (e.hom.app F).hom (𝟙
        ((pbcQbarCompletedPull l Ω g).obj ((stageHeart l Ω X A).obj F).obj))) ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme)
        (F : NormalizedFibre.Heart l (pbcFiniteField.{u} l Ω A) (base l X)),
        (V.pull g κ y).hom.app ((stageHeart l Ω X A).obj F) ≫
            ((V.point X κ (y ≫ g)).finite_stage A).hom.app F =
          (V.point Y κ y).functor.map (e.hom.app F) ≫
            ((V.point Y κ y).finite_stage A).hom.app
              ((heartPull l (pbcFiniteField.{u} l Ω A) R g).obj F) ≫
            (ModuleCat.extendScalars (stageEmbedding l Ω A)).map
              (((c (pbcFiniteField.{u} l Ω A) (pbcFiniteField.{u} l Ω A)).pull g κ y).hom.app F)

  identity : ∀ (X : FiniteTypeBase k),
    ∃ e : commonHeartPull l Ω (𝟙 X.scheme) ≅ 𝟭 _,
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
        (F : (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory),
        HEq ((V.pull (𝟙 X.scheme) κ x).hom.app F)
          ((V.point X κ x).functor.map (e.hom.app F))
  composition : ∀ (X Y Z : FiniteTypeBase k) (g : Y.scheme ⟶ X.scheme)
    (h : Z.scheme ⟶ Y.scheme),
    ∃ e : commonHeartPull l Ω (h ≫ g) ≅ commonHeartPull l Ω g ⋙ commonHeartPull l Ω h,
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (z : Spec (.of κ) ⟶ Z.scheme)
        (F : (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory),
        HEq ((V.pull (h ≫ g) κ z).hom.app F)
          ((V.point Z κ z).functor.map (e.hom.app F) ≫
            (V.pull h κ z).hom.app ((commonHeartPull l Ω g).obj F) ≫
              (V.pull g κ (z ≫ h)).hom.app F)


end AlgebraicGeometry.Scheme.AdicFibreComparison
