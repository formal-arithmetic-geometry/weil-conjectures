/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowersSupplement
public import WeilConjectures.Algebra.Homology.RegularQuotientConeBasic
public import WeilConjectures.CategoryTheory.SystemDerivedTransition
public import WeilConjectures.CategoryTheory.SystemScalarCoherence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Compatible normalized quotient error triangles

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
sk-lem-sp-tower.proof.md, second paragraph
(blueprint: def-sp-normalized-quotient-error-data).

Natural number `n` denotes the positive coefficient level `n+1`. A quotient diagram
is presented with its structural maps to the actual sheafified principal quotients;
these maps fix its transitions. All derived categories below are ordinary unbounded
localizations of the abelian categories indicated in their types.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open SheafOfModules.RegularQuotientCone

namespace SheafOfModules.NormalizedQuotientError

variable {S : Type u} [Category.{v} S] {J : GrothendieckTopology S}
  [EssentiallySmall.{r} S]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- The actual transition adjunct, not a separately chosen isomorphism.
Source: blueprint, second paragraph (blueprint: def-sp-normalized-quotient-error-data). -/
def normalization (A : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (C : DerivedCategory (StrictRingSystem B)) {m n : ℕ} (h : m ≤ n) :=
  ((systemDerivedTensorAdj A B h).homEquiv _ _).symm
    ((systemDerivedTransition B h).app C)

set_option maxHeartbeats 1600000 in
-- Scalar-restriction coherence unfolds the module structure at every section.
/-- Restrict a strict coefficient system along its actual structural ring maps.
Source: blueprint, second paragraph (blueprint: def-sp-normalized-quotient-error-data). -/
def underlyingDiagram (R : Sheaf J CommRingCat.{r})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B) (M : StrictRingSystem B) :
    ℕᵒᵖ ⥤ Modules R where
  obj n := (restriction (a.app n)).obj (M.level n.unop)
  map {n m} h := (restriction (a.app n)).map (M.transition (leOfHom h.unop)) ≫
    (systemScalarRestrictionComposition _ _ _ (by
      have hh : (homOfLE (leOfHom h.unop)).op = h := Subsingleton.elim _ _
      rw [hh]
      change a.app m = a.app n ≫ B.map h
      exact (Category.id_comp _).symm.trans (a.naturality h))).hom.app _
  map_id n := by ext U x; exact M.identity n.unop U x
  map_comp {n m l} h k := by
    ext U x
    exact M.compose (leOfHom k.unop) (leOfHom h.unop) U x

/-- Restriction retains the original system maps, including all iterated transitions.
Source: blueprint, second paragraph (blueprint: def-sp-normalized-quotient-error-data). -/
def underlyingDiagrams (R : Sheaf J CommRingCat.{r})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B) : StrictRingSystem B ⥤ (ℕᵒᵖ ⥤ Modules R) where
  obj := underlyingDiagram R B a
  map f := {
    app := fun n ↦ (restriction (a.app n)).map (f.app n.unop)
    naturality := by
      intro n m h
      ext U x
      exact (congrArg (fun z ↦ z.val.app U x) (f.comm (leOfHom h.unop))).symm }
  map_id M := by ext n U x; rfl
  map_comp f g := by ext n U x; rfl

/-- Componentwise additivity of restriction.
Source: Stacks 03CZ (blueprint: def-sp-normalized-quotient-error-data). -/
instance underlyingDiagramsAdditive (R : Sheaf J CommRingCat.{r})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B) : (underlyingDiagrams R B a).Additive where
  map_add := by
    intro M N f g
    apply NatTrans.ext
    funext n
    change (restriction (a.app n)).map ((systemEvaluation B n.unop).map (f + g)) = _
    rw [Functor.map_add, Functor.map_add]
    rfl

/-- Regard a complex of whole inverse systems as a strict inverse system of complexes.
Source: Stacks 0941 (blueprint: def-sp-normalized-quotient-error-data). -/
def towerView (R : Sheaf J CommRingCat.{r})
    (P : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (Modules R) ℤ where
  obj n := (((CategoryTheory.evaluation ℕᵒᵖ (Modules R)).obj n).mapHomologicalComplex (.up ℤ)).obj P
  map h := {
    f := fun i ↦ (P.X i).map h
    comm' := fun i j _ ↦ (P.d i j).naturality h }
  map_id n := by
    apply HomologicalComplex.hom_ext
    intro i
    exact (P.X i).map_id n
  map_comp h k := by
    apply HomologicalComplex.hom_ext
    intro i
    exact (P.X i).map_comp h k

/-- The tail begins at the positive level m+1.
Source: blueprint, second paragraph (blueprint: def-sp-normalized-quotient-error-data). -/
def tail (m : ℕ) : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (show ℕ ⥤ ℕ from (OrderHom.toFunctor ⟨fun n ↦ m + n, by
    intro i j h; exact Nat.add_le_add_left h m⟩)).op

/-- A constant system, formed before localization.
Source: blueprint, second paragraph (blueprint: def-sp-normalized-quotient-error-data). -/
def constantTower (R : Sheaf J CommRingCat.{r})
    (P : CochainComplex (Modules R) ℤ) : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ :=
  koszulTowerComplex R ((Functor.const ℕᵒᵖ).obj P)

/-- The standard ordinary unbounded derived category of the whole tower category.
Source: Stacks 015F (blueprint: def-sp-normalized-quotient-error-data). -/
instance towerHasDerived (R : Sheaf J CommRingCat.{r}) :
    HasDerivedCategory (ℕᵒᵖ ⥤ Modules R) := HasDerivedCategory.standard _

/-- Local sections of the unit module are sections of the ring sheaf.
Source: Stacks 03CZ (blueprint: def-sp-normalized-quotient-error-data). -/
def ringSection (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    (R.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections := ⟨t.val, t.property⟩

/-- The image of the specified global section along the actual coefficient map.
Source: blueprint, second paragraph (blueprint: def-sp-normalized-quotient-error-data). -/
def imageSection {R A : Sheaf J CommRingCat.{r}} (a : R ⟶ A)
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    (unit (derivedChangeRingIndependentCoefficients J A)).sections :=
  PresheafOfModules.sectionsMk (fun U ↦ (a.hom.app U).hom (t.val U)) (by
    intro U V f
    change (A.obj.map f).hom ((a.hom.app U).hom (t.val U)) = _
    rw [← CommRingCat.comp_apply, ← a.hom.naturality]
    exact congrArg ((a.hom.app V).hom) (t.property f))

/-- The existing simultaneous representative at one coefficient level.
Source: Zheng 4.1 (blueprint: def-sp-normalized-quotient-error-data). -/
abbrev level (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (P : CochainComplex (StrictRingSystem B) ℤ) (n : ℕ) :=
  ((systemEvaluation B n).mapHomologicalComplex (.up ℤ)).obj P

/-- The degree-zero coefficient unit into a total tensor with the quotient module.
Source: Stacks 03EK (blueprint: def-sp-normalized-quotient-error-data). -/
def tensorQuotientUnit {R A : Sheaf J CommRingCat.{r}} (a : R ⟶ A)
    (P : CochainComplex (Modules R) ℤ) :=
  koszulTensorUnitInclusion R P ≫ (koszulTensorFunctor R P).map
    ((CochainComplex.singleFunctor (Modules R) 0).map (ringMap a))

attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

/-- Inclusion of the degree -1 Koszul generator into the total tensor.
Source: blueprint, second paragraph (blueprint: def-sp-normalized-quotient-error-data).
Coefficients are the first tensor factor, so the second differential has sign (-1)^q. -/
def minusGenerator (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (m : ℕ) (P : CochainComplex (Modules R) ℤ) (i : ℤ) :
    P.X (i + 1) ⟶ ((koszulTensorFunctor R P).obj (principalKoszul R t m)).X i :=
  (MonoidalCategory.leftUnitor (P.X (i + 1))).inv ≫
    MonoidalCategory.whiskerRight
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (unit (derivedChangeRingIndependentCoefficients J R))).inv ≫
          (CochainComplex.mappingCone.inl
            (principalKoszulScalarComplex R t m)).v 0 (-1) (by decide)) (P.X (i + 1)) ≫
    HomologicalComplex.ιMapBifunctor _ _ (MonoidalCategory.curriedTensor (Modules R))
      (.up ℤ) (-1) (i + 1) i (by change -1 + (i + 1) = i; omega)

/-- Multiply every successor transition by t, retaining the complex at each level.
Source: blueprint, second paragraph (blueprint: def-sp-normalized-quotient-error-data). -/
def twist (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (F : ℕᵒᵖ ⥤ CochainComplex (Modules R) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (Modules R) ℤ :=
  Functor.ofOpSequence (X := fun n ↦ F.obj (op n)) (fun n ↦
    (complexScalar R t).app (F.obj (op (n + 1))) ≫
      F.map (homOfLE (Nat.le_add_right n 1)).op)

/-- Twisting the original maps, rather than choosing a new tower identification.
Source: blueprint, second paragraph (blueprint: def-sp-normalized-quotient-error-data). -/
def twistMap (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    {F G : ℕᵒᵖ ⥤ CochainComplex (Modules R) ℤ} (f : F ⟶ G) :
    twist R t F ⟶ twist R t G :=
  NatTrans.ofOpSequence (fun n ↦ f.app (op n)) (by
    intro n
    dsimp only [twist]
    rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ]
    rw [Category.assoc, f.naturality, ← Category.assoc]
    have hn := (complexScalar R t).naturality (f.app (op (n + 1)))
    dsimp only [Functor.id_map, Functor.id_obj] at hn
    exact (congrArg (fun z ↦ z ≫ G.map
      (homOfLE (Nat.le_add_right n 1)).op) hn.symm).trans (Category.assoc _ _ _))

/-- The constant complex with successor transition t, hence transition t^(n'-n).
Source: blueprint, second paragraph (blueprint: def-sp-normalized-quotient-error-data). -/
def powerTower (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex (Modules R) ℤ) : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ :=
  koszulTowerComplex R (twist R t ((Functor.const ℕᵒᵖ).obj P))

/-- Exact evaluation of a map between whole complexes of systems.
Source: Stacks 0941 (blueprint: def-sp-normalized-quotient-error-data). -/
def towerViewMap (R : Sheaf J CommRingCat.{r})
    {P Q : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ} (f : P ⟶ Q) :
    towerView R P ⟶ towerView R Q where
  app n := (((CategoryTheory.evaluation ℕᵒᵖ (Modules R)).obj n).mapHomologicalComplex
    (.up ℤ)).map f
  naturality n m h := by
    apply HomologicalComplex.hom_ext
    intro i
    exact (f.f i).naturality h

/-- The actual levelwise transition before deriving.
Source: Zheng 4.1 (blueprint: def-sp-normalized-quotient-error-data). -/
def transition (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (P : CochainComplex (StrictRingSystem B) ℤ) {m n : ℕ} (h : m ≤ n) :=
  (NatTrans.mapHomologicalComplex (strictSystemTransition B h) (.up ℤ)).app P

/-- The ordinary transition adjunct on a simultaneous representative.
Source: Stacks 03D7 (blueprint: def-sp-normalized-quotient-error-data). -/
def ordinaryNormalization (A : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (P : CochainComplex (StrictRingSystem B) ℤ) {m n : ℕ} (h : m ≤ n) :=
  (((systemTensorAdj A B h).mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm
    (transition B P h ≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (systemEvaluation B m ⋙ systemRestriction B h)) (.up ℤ)).inv.app P)

/-- Tensor every complex of a tower with one fixed coefficient complex.
Source: Stacks 06YN (blueprint: def-sp-normalized-quotient-error-data). -/
def coefficientTensor (R : Sheaf J CommRingCat.{r})
    (K : CochainComplex (Modules R) ℤ) :
    CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ :=
  (MonoidalCategory.curriedTensor (Modules R)).map₂CochainComplex.obj K

/-- The Koszul model of reduction on the tail, with all original transition maps.
Source: blueprint, second paragraph (blueprint: def-sp-normalized-quotient-error-data). -/
def middle (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) (m : ℕ)
    (P : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) :=
  koszulTowerComplex R (tail m ⋙ towerView R P ⋙ coefficientTensor R (principalKoszul R t m))

/-- Shift each evaluated complex before reassembling the whole inverse system.
Source: Stacks 014A (blueprint: def-sp-normalized-quotient-error-data). -/
def shiftedTwist (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (V : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) :=
  koszulTowerComplex R (twist R t (towerView R V ⋙ shiftFunctor _ (1 : ℤ)))

/-- Shift and twist an actual whole-system morphism.
Source: Stacks 014A (blueprint: def-sp-normalized-quotient-error-data). -/
def shiftedTwistMap (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    {V W : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ} (f : V ⟶ W) :
    shiftedTwist R t V ⟶ shiftedTwist R t W :=
  koszulTowerComplexMap R (twistMap R t
    (Functor.whiskerRight (towerViewMap R f) (shiftFunctor _ (1 : ℤ))))

/-- Restrict a simultaneous strict representative to the original ring.
Source: Zheng 4.1 (blueprint: def-sp-normalized-quotient-error-data). -/
abbrev representative (R : Sheaf J CommRingCat.{r})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B) (P : CochainComplex (StrictRingSystem B) ℤ) :=
  ((underlyingDiagrams R B a).mapHomologicalComplex (.up ℤ)).obj P

/-- The original-ring complex at a coefficient level.
Source: Stacks 03CZ (blueprint: def-sp-normalized-quotient-error-data). -/
abbrev restrictedLevel (R : Sheaf J CommRingCat.{r})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B) (P : CochainComplex (StrictRingSystem B) ℤ)
    (n : ℕ) :=
  ((restriction (a.app (op n))).mapHomologicalComplex (.up ℤ)).obj (level B P n)

set_option maxHeartbeats 1600000 in
-- The witnesses retain the total tensors, full-system cones, and their component equations.
/-- The compatible strict models and the normalized comparison of their whole derived triangle.
Source: blueprint sk-lem-sp-tower proof, second paragraph
(blueprint: def-sp-normalized-quotient-error-data).
The two component equations for the error fix the Koszul-generator map and its zero
component in the target summand of the cocone. The tensor comparison is fixed on the
unit generators, so none of these is an arbitrary identification of isomorphic objects. -/
structure ErrorTriangle (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B) (A : SystemScalarAssignment (J := J))
    (P : CochainComplex (StrictRingSystem B) ℤ) (m : ℕ) where
  /-- The right coefficient tensor system, before normalization. -/
  V : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ
  /-- Its actual ordinary scalar-extension representative at each tail level. -/
  ν : ∀ n : ℕ, (towerView R V).obj (op n) ≅
    ((restriction (a.app (op m))).mapHomologicalComplex (.up ℤ)).obj
      (((systemTensor A B (Nat.le_add_right m n)).mapHomologicalComplex (.up ℤ)).obj
        (level B P (m + n)))
  /-- The balanced comparison with the original-ring quotient tensor. -/
  μ : ∀ n : ℕ,
    (koszulTensorFunctor R (restrictedLevel R B a P (m + n))).obj
      ((CochainComplex.singleFunctor (Modules R) 0).obj
        ((restriction (a.app (op m))).obj
          (unit (derivedChangeRingIndependentCoefficients J (B.obj (op m)))))) ≅
    ((restriction (a.app (op m))).mapHomologicalComplex (.up ℤ)).obj
      (((systemTensor A B (Nat.le_add_right m n)).mapHomologicalComplex (.up ℤ)).obj
        (level B P (m + n)))
  /-- The comparison sends x tensor 1 to the ordinary extension unit of x. -/
  μ_unit : ∀ (n : ℕ) (i : ℤ) (U : Sᵒᵖ)
    (x : ((restrictedLevel R B a P (m + n)).X i).val.obj U),
    (((tensorQuotientUnit (a.app (op m)) (restrictedLevel R B a P (m + n)) ≫
      (μ n).hom).f i).val.app U x) =
    systemModelTmul (A (B.map (homOfLE (Nat.le_add_right m n)).op)).model
      ((level B P (m + n)).X i) U 1 x
  /-- The canonical quotient augmentation, described on both cone summands. -/
  augmentation : principalKoszul R t m ⟶
    (CochainComplex.singleFunctor (Modules R) 0).obj
      ((restriction (a.app (op m))).obj
        (unit (derivedChangeRingIndependentCoefficients J (B.obj (op m)))))
  /-- Its degree-zero component is the actual ring quotient. -/
  augmentation_inr : CochainComplex.mappingCone.inr (principalKoszulScalarComplex R t m) ≫
    augmentation = (CochainComplex.singleFunctor (Modules R) 0).map (ringMap (a.app (op m)))
  /-- Its shifted generator component is zero. -/
  augmentation_inl : (CochainComplex.mappingCone.inl
    (principalKoszulScalarComplex R t m)).v 0 (-1) (by decide) ≫
      augmentation.f (-1) = 0
  /-- The augmentation map of whole inverse systems. -/
  ε : middle R t m (representative R B a P) ⟶ V
  /-- Every component is the stated quotient augmentation tensored with P_n. -/
  ε_eq : ∀ n : ℕ, (towerViewMap R ε).app (op n) ≫ (ν n).hom =
    (koszulTensorFunctor R (restrictedLevel R B a P (m + n))).map augmentation ≫ (μ n).hom
  /-- Normalization to the constant level-m complex using the original transitions. -/
  N : V ⟶ constantTower R (restrictedLevel R B a P m)
  /-- The normalization components are the actual transition adjuncts. -/
  N_eq : ∀ n : ℕ, (towerViewMap R N).app (op n) = (ν n).hom ≫
    ((restriction (a.app (op m))).mapHomologicalComplex (.up ℤ)).map
      (ordinaryNormalization A B P (Nat.le_add_right m n))
  /-- Normalization is invertible in the derived category of whole systems. -/
  N_quasiIso : QuasiIso N
  /-- The error comparison before inverting normalization. -/
  j : shiftedTwist R t V ⟶ CochainComplex.mappingCocone ε
  /-- The left comparison is a quasi-isomorphism of whole-system complexes. -/
  j_quasiIso : QuasiIso j
  /-- Its left component is the degree-minus-one generator multiplied by t^(n-m). -/
  j_generator : ∀ (n : ℕ) (i : ℤ) (U : Sᵒᵖ)
    (x : ((restrictedLevel R B a P (m + n)).X (i + 1)).val.obj U),
    ((((j ≫ CochainComplex.mappingCocone.fst ε).f i).app (op n)).val.app U
      (((CochainComplex.shiftFunctorObjXIso ((towerView R V).obj (op n))
        (1 : ℤ) i (i + 1) rfl).inv).val.app U
        (((ν n).inv.f (i + 1)).val.app U
          (systemModelTmul (A (B.map (homOfLE (Nat.le_add_right m n)).op)).model
            ((level B P (m + n)).X (i + 1)) U 1 x)))) =
    (minusGenerator R t m (restrictedLevel R B a P (m + n)) i).val.app U
      (((endoPow ((complexScalar R t).app (restrictedLevel R B a P (m + n))) n).f
        (i + 1)).val.app U x)
  /-- Its component in the quotient target summand is zero. -/
  j_target : ∀ (i : ℤ), j.f i ≫
    (CochainComplex.mappingCocone.snd ε).v i (i - 1) (by omega) = 0
  /-- The normalized error tower has exactly scalar successor maps t. -/
  errorIso : DerivedCategory.Q.obj
    (shiftedTwist R t (constantTower R (restrictedLevel R B a P m))) ≅
    DerivedCategory.Q.obj (CochainComplex.mappingCocone ε)
  /-- The error isomorphism is induced by the specified j and the actual normalization. -/
  errorIso_eq : DerivedCategory.Q.map (shiftedTwistMap R t N) ≫ errorIso.hom =
    DerivedCategory.Q.map j
  /-- The actual augmentation triangle is distinguished in the whole-system derived category. -/
  distinguished : (DerivedCategory.Q.mapTriangle.obj
    (CochainComplex.mappingCocone.triangle ε)) ∈ distTriang _

/-- The ordinary balanced quotient tensor and its actual transition-adjoint map.
Source: blueprint sk-lem-sp-tower proof, second paragraph
(blueprint: def-sp-normalized-quotient-error-data).
This retains the ordinary part of ErrorTriangle before either quasi-isomorphism is proved. -/
structure QuotientModel (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B) (A : SystemScalarAssignment (J := J))
    (P : CochainComplex (StrictRingSystem B) ℤ) (m : ℕ) where
  /-- The right coefficient tensor system, before normalization. -/
  V : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ
  /-- Its actual ordinary scalar-extension representative at each tail level. -/
  ν : ∀ n : ℕ, (towerView R V).obj (op n) ≅
    ((restriction (a.app (op m))).mapHomologicalComplex (.up ℤ)).obj
      (((systemTensor A B (Nat.le_add_right m n)).mapHomologicalComplex (.up ℤ)).obj
        (level B P (m + n)))
  /-- The balanced comparison with the original-ring quotient tensor. -/
  μ : ∀ n : ℕ,
    (koszulTensorFunctor R (restrictedLevel R B a P (m + n))).obj
      ((CochainComplex.singleFunctor (Modules R) 0).obj
        ((restriction (a.app (op m))).obj
          (unit (derivedChangeRingIndependentCoefficients J (B.obj (op m)))))) ≅
    ((restriction (a.app (op m))).mapHomologicalComplex (.up ℤ)).obj
      (((systemTensor A B (Nat.le_add_right m n)).mapHomologicalComplex (.up ℤ)).obj
        (level B P (m + n)))
  /-- The comparison sends x tensor 1 to the ordinary extension unit of x. -/
  μ_unit : ∀ (n : ℕ) (i : ℤ) (U : Sᵒᵖ)
    (x : ((restrictedLevel R B a P (m + n)).X i).val.obj U),
    (((tensorQuotientUnit (a.app (op m)) (restrictedLevel R B a P (m + n)) ≫
      (μ n).hom).f i).val.app U x) =
    systemModelTmul (A (B.map (homOfLE (Nat.le_add_right m n)).op)).model
      ((level B P (m + n)).X i) U 1 x
  /-- The canonical quotient augmentation, described on both cone summands. -/
  augmentation : principalKoszul R t m ⟶
    (CochainComplex.singleFunctor (Modules R) 0).obj
      ((restriction (a.app (op m))).obj
        (unit (derivedChangeRingIndependentCoefficients J (B.obj (op m)))))
  /-- Its degree-zero component is the actual ring quotient. -/
  augmentation_inr : CochainComplex.mappingCone.inr (principalKoszulScalarComplex R t m) ≫
    augmentation = (CochainComplex.singleFunctor (Modules R) 0).map (ringMap (a.app (op m)))
  /-- Its shifted generator component is zero. -/
  augmentation_inl : (CochainComplex.mappingCone.inl
    (principalKoszulScalarComplex R t m)).v 0 (-1) (by decide) ≫
      augmentation.f (-1) = 0
  /-- The augmentation map of whole inverse systems. -/
  ε : middle R t m (representative R B a P) ⟶ V
  /-- Every component is the stated quotient augmentation tensored with P_n. -/
  ε_eq : ∀ n : ℕ, (towerViewMap R ε).app (op n) ≫ (ν n).hom =
    (koszulTensorFunctor R (restrictedLevel R B a P (m + n))).map augmentation ≫ (μ n).hom
  /-- Normalization to the constant level-m complex using the original transitions. -/
  N : V ⟶ constantTower R (restrictedLevel R B a P m)
  /-- The normalization components are the actual transition adjuncts. -/
  N_eq : ∀ n : ℕ, (towerViewMap R N).app (op n) = (ν n).hom ≫
    ((restriction (a.app (op m))).mapHomologicalComplex (.up ℤ)).map
      (ordinaryNormalization A B P (Nat.le_add_right m n))

end SheafOfModules.NormalizedQuotientError
