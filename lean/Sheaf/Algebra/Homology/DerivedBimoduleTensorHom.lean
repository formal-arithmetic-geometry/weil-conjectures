/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.Algebra.Homology.AlgebraicShriekDerivedHomAdjunction
public import Sheaf.Algebra.Homology.DerivedCoinductionEnrichedClass
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

/-! # Mixed-ring derived tensor-Hom with retained scalars

Source: Stacks Project, dga.tex, Tags 09LN and 09LT, specialized to commutative
rings in degree zero; sites-cohomology.tex, Tags 0A95, 0A96 and 08J9
(blueprint: lem-trf-derived-bimodule-tensor-hom).

The closed structure is the existing K-flat derived tensor and its internal Hom.
Coinduction gives a concrete construction of J_E, with no choices of an arbitrary
right adjoint. The representative comparison below identifies its action with
precomposition on the S-linear total Hom complex.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace ModuleCat

variable {S B : Type u} [CommRing S] [CommRing B]
  [HasDerivedCategory.{u} (ModuleCat.{u} S)]
  [HasDerivedCategory.{u} (ModuleCat.{u} B)]

/-- J_E(V) = RHom_B(E, Coind_S^B(V)). Evaluation at one identifies its complex model
with Hom_S(E,I), carrying (b h)(e) = h(be).
Source: Stacks 09LN and 09LT (blueprint: lem-trf-derived-bimodule-tensor-hom). -/
def derivedBimoduleHom (f : S →+* B) (E : DerivedCategory (ModuleCat.{u} B)) :
    DerivedCategory (ModuleCat.{u} S) ⥤ DerivedCategory (ModuleCat.{u} B) :=
  derivedCoinduction f ⋙ ihom E

/-- Tensor with E, retaining B-scalars until the final exact restriction.
Source: Stacks 09LT (blueprint: lem-trf-derived-bimodule-tensor-hom). -/
def derivedBimoduleTensor (f : S →+* B) (E : DerivedCategory (ModuleCat.{u} B)) :
    DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} S) :=
  tensorRight E ⋙ (restrictScalars f).mapDerivedCategory

/-- The actual tensor/coinduction composite adjunction. The braiding is the one
induced by the signed symmetry of complexes through K-flat localization.
Source: Stacks 09LN and 09LT (blueprint: lem-trf-derived-bimodule-tensor-hom). -/
def derivedBimoduleAdjunction (f : S →+* B) (E : DerivedCategory (ModuleCat.{u} B)) :
    derivedBimoduleTensor f E ⊣ derivedBimoduleHom f E :=
  letI := DerivedCategory.braidedCategory' (ModuleCat.{u} B)
  ((ihom.adjunction E).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight E)).comp
    (derivedCoinductionAdjunction f)

/-- Derived evaluation h tensor e ↦ h(e), expressed by the closed evaluation,
the canonical signed exchange, and the coinduction evaluation at one.
Source: Stacks 09LN and 09LT (blueprint: lem-trf-derived-bimodule-tensor-hom). -/
def derivedBimoduleEvaluation (f : S →+* B) (E : DerivedCategory (ModuleCat.{u} B))
    (V : DerivedCategory (ModuleCat.{u} S)) :
    (derivedBimoduleTensor f E).obj ((derivedBimoduleHom f E).obj V) ⟶ V :=
  letI := DerivedCategory.braidedCategory' (ModuleCat.{u} B)
  (restrictScalars f).mapDerivedCategory.map
      ((β_ E ((derivedBimoduleHom f E).obj V)).inv ≫
        (ihom.ev E).app ((derivedCoinduction f).obj V)) ≫
    (derivedCoinductionAdjunction f).counit.app V

/-- The normalized enriched coinduction comparison already characterized by evaluation
at one in algebraicShriek_derivedHom_adjunction. That theorem fixes its natural
transformation uniquely: its models are transposed signed evaluation, and its chain
comparison is z ↦ (x ↦ z(x)(1)). Only the proof of that characterization is postponed.
Source: Stacks 0A70 and 0A71 (blueprint: lem-trf-derived-bimodule-tensor-hom). -/
abbrev bimoduleCoinductionHomIso (f : S →+* B) :
    coinductionHomLeft f ≅ coinductionHomRight f :=
  coinductionEnrichedHomIso f

/-- Closed currying, in the order X tensor E. It is the transpose of the two
successive evaluations, after the canonical exchange of X and E.
Source: Stacks 09LN (blueprint: lem-trf-derived-bimodule-tensor-hom). -/
def bimoduleClosedCurry (X E Y : DerivedCategory (ModuleCat.{u} B)) :
    (ihom X).obj ((ihom E).obj Y) ⟶ (ihom (X ⊗ E)).obj Y :=
  letI := DerivedCategory.braidedCategory' (ModuleCat.{u} B)
  MonoidalClosed.curry
    ((β_ X E).hom ▷ ((ihom X).obj ((ihom E).obj Y)) ≫
      (α_ E X ((ihom X).obj ((ihom E).obj Y))).hom ≫
      E ◁ (ihom.ev X).app ((ihom E).obj Y) ≫ (ihom.ev E).app Y)

/-- The canonical S-linear comparison, obtained by closed currying over B followed
by the existing enriched coinduction comparison. No replacement of RHom_S by RHom_K
is involved when these maps are subsequently restricted.
Source: Stacks 09LN and 09LT (blueprint: lem-trf-derived-bimodule-tensor-hom). -/
def derivedBimoduleComparison (f : S →+* B)
    (E X : DerivedCategory (ModuleCat.{u} B)) (V : DerivedCategory (ModuleCat.{u} S)) :
    (restrictScalars f).mapDerivedCategory.obj
        ((ihom X).obj ((derivedBimoduleHom f E).obj V)) ⟶
      (ihom ((derivedBimoduleTensor f E).obj X)).obj V :=
  (restrictScalars f).mapDerivedCategory.map
      (bimoduleClosedCurry X E ((derivedCoinduction f).obj V)) ≫
    (bimoduleCoinductionHomIso f).hom.app (op (X ⊗ E), V)

/-- The source bifunctor U RHom_B(X,J_E(V)).
Source: Stacks 09LN (blueprint: lem-trf-derived-bimodule-tensor-hom). -/
def derivedBimoduleHomLeft (f : S →+* B) (E : DerivedCategory (ModuleCat.{u} B)) :
    (DerivedCategory (ModuleCat.{u} B))ᵒᵖ × DerivedCategory (ModuleCat.{u} S) ⥤
      DerivedCategory (ModuleCat.{u} S) :=
  (𝟭 _).prod (derivedBimoduleHom f E) ⋙
    Functor.uncurry.obj MonoidalClosed.internalHom ⋙ (restrictScalars f).mapDerivedCategory

/-- The target bifunctor RHom_S(U(X tensor E),V).
Source: Stacks 09LN (blueprint: lem-trf-derived-bimodule-tensor-hom). -/
def derivedBimoduleHomRight (f : S →+* B) (E : DerivedCategory (ModuleCat.{u} B)) :
    (DerivedCategory (ModuleCat.{u} B))ᵒᵖ × DerivedCategory (ModuleCat.{u} S) ⥤
      DerivedCategory (ModuleCat.{u} S) :=
  (derivedBimoduleTensor f E).op.prod (𝟭 _) ⋙
    Functor.uncurry.obj MonoidalClosed.internalHom

/-- The canonical map S[0] → U(B[0]), expressed using the existing single-functor
comparisons and the ring map f as an S-linear map.
Source: Stacks 09LN (blueprint: lem-trf-derived-bimodule-tensor-hom). -/
abbrev bimoduleScalarUnit (f : S →+* B) :
    𝟙_ (DerivedCategory (ModuleCat.{u} S)) ⟶
      (restrictScalars f).mapDerivedCategory.obj (𝟙_ (DerivedCategory (ModuleCat.{u} B))) :=
  coinductionScalarUnit f

/-- The canonical comparison from the B-linear Hom complex into J, using the existing
transposed evaluation comparison and the canonical K-injective coinduction model.
Source: Stacks 09LN, 0A95 and 0A96 (blueprint: lem-trf-derived-bimodule-tensor-hom). -/
def derivedBimoduleHomModel (f : S →+* B)
    (E : CochainComplex (ModuleCat.{u} B) ℤ)
    (I : CochainComplex (ModuleCat.{u} S) ℤ) [I.IsKInjective] :
    DerivedCategory.Q.obj
        (CochainComplex.moduleHomComplex E ((coinductionComplexFunctor f).obj I)) ⟶
      (derivedBimoduleHom f (DerivedCategory.Q.obj E)).obj (DerivedCategory.Q.obj I) :=
  coinductionHomComparison E ((coinductionComplexFunctor f).obj I) ≫
    (ihom (DerivedCategory.Q.obj E)).map (derivedCoinductionModel f I).inv


private lemma closedCurry_eq (X E Y : DerivedCategory (ModuleCat.{u} B)) :
    bimoduleClosedCurry X E Y =
      MonoidalClosed.ihomUncurry E X Y ≫
        (MonoidalClosed.pre
          ((DerivedCategory.braidedCategory' (ModuleCat.{u} B)).braiding X E).hom).app Y := by
  let := DerivedCategory.braidedCategory' (ModuleCat.{u} B)
  exact (MonoidalClosed.curry_pre_app (β_ X E).hom _).symm

private lemma closedCurry_isIso (X E Y : DerivedCategory (ModuleCat.{u} B)) :
    IsIso (bimoduleClosedCurry X E Y) := by
  let := DerivedCategory.braidedCategory' (ModuleCat.{u} B)
  rw [closedCurry_eq]
  have : IsIso (MonoidalClosed.ihomUncurry E X Y) :=
    inferInstanceAs (IsIso (MonoidalClosed.ihomCurryIso E X Y).inv)
  have : IsIso ((MonoidalClosed.pre (β_ X E).hom).app Y) :=
    inferInstanceAs (IsIso ((MonoidalClosed.internalHom.mapIso (β_ X E).op).app Y).hom)
  infer_instance

private lemma closedCurry_naturality
    {X X' E E' Y Y' : DerivedCategory (ModuleCat.{u} B)}
    (a : X' ⟶ X) (b : E' ⟶ E) (c : Y ⟶ Y') :
    (MonoidalClosed.pre a).app ((ihom E).obj Y) ≫
        (ihom X').map ((MonoidalClosed.pre b).app Y ≫ (ihom E').map c) ≫
        bimoduleClosedCurry X' E' Y' =
      bimoduleClosedCurry X E Y ≫ (MonoidalClosed.pre (a ⊗ₘ b)).app Y ≫
        (ihom (X' ⊗ E')).map c := by
  let := DerivedCategory.braidedCategory' (ModuleCat.{u} B)
  apply MonoidalClosed.uncurry_injective
  conv_rhs => rw [← Category.assoc, MonoidalClosed.uncurry_natural_right,
    MonoidalClosed.uncurry_pre_app]
  simp only [bimoduleClosedCurry, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, associator_naturality_right_assoc]
  have hinner :
      X' ◁ (MonoidalClosed.pre a).app ((ihom E).obj Y) ≫
          X' ◁ (ihom X').map ((MonoidalClosed.pre b).app Y ≫ (ihom E').map c) ≫
          (ihom.ev X').app ((ihom E').obj Y') =
        a ▷ ((ihom X).obj ((ihom E).obj Y)) ≫
          (ihom.ev X).app ((ihom E).obj Y) ≫
          (MonoidalClosed.pre b).app Y ≫ (ihom E').map c := by
    rw [ihom.ev_naturality, ← Category.assoc,
      MonoidalClosed.id_tensor_pre_app_comp_ev]
    simp only [Category.assoc]
  have houter :
      E' ◁ (MonoidalClosed.pre b).app Y ≫
          E' ◁ (ihom E').map c ≫ (ihom.ev E').app Y' =
        b ▷ ((ihom E).obj Y) ≫ (ihom.ev E).app Y ≫ c := by
    rw [ihom.ev_naturality, ← Category.assoc,
      MonoidalClosed.id_tensor_pre_app_comp_ev]
    simp only [Category.assoc]
  have hw := congrArg (fun t ↦ E' ◁ t) hinner
  simp only [whiskerLeft_comp] at hw
  rw [reassoc_of% hw]
  rw [houter]
  rw [whisker_exchange_assoc]
  rw [← associator_naturality_middle_assoc]
  rw [← associator_naturality_left_assoc]
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
  rw [Category.assoc (β_ X' E').hom, ← tensorHom_def',
    ← BraidedCategory.braiding_naturality]
  simp only [comp_whiskerRight, Category.assoc]

private lemma closedCurry_class (X E Y : DerivedCategory (ModuleCat.{u} B))
    (g : X ⟶ (ihom E).obj Y) :
    MonoidalClosed.curry' g ≫ bimoduleClosedCurry X E Y =
      MonoidalClosed.curry'
        (((DerivedCategory.braidedCategory' (ModuleCat.{u} B)).braiding E X).inv ≫
          MonoidalClosed.uncurry g) := by
  let := DerivedCategory.symmetricCategory (ModuleCat.{u} B)
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left]
  dsimp only [bimoduleClosedCurry]
  rw [MonoidalClosed.uncurry_curry]
  rw [whisker_exchange_assoc, associator_naturality_right_assoc]
  rw [← whiskerLeft_comp_assoc, MonoidalClosed.whiskerLeft_curry'_ihom_ev_app]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [MonoidalClosed.curry', MonoidalClosed.uncurry_curry]
  rw [← rightUnitor_tensor_hom_assoc, rightUnitor_naturality_assoc]
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding]
  simp only [MonoidalClosed.uncurry_eq]

private lemma bimoduleComparison_naturality (f : S →+* B)
    {E E' X X' : DerivedCategory (ModuleCat.{u} B)}
    {V V' : DerivedCategory (ModuleCat.{u} S)}
    (a : X' ⟶ X) (b : E' ⟶ E) (c : V ⟶ V') :
    (restrictScalars f).mapDerivedCategory.map
        ((MonoidalClosed.pre a).app ((derivedBimoduleHom f E).obj V) ≫
          (ihom X').map ((MonoidalClosed.pre b).app ((derivedCoinduction f).obj V) ≫
            (ihom E').map ((derivedCoinduction f).map c))) ≫
        derivedBimoduleComparison f E' X' V' =
      derivedBimoduleComparison f E X V ≫
        (MonoidalClosed.pre
          ((restrictScalars f).mapDerivedCategory.map (a ⊗ₘ b))).app V ≫
        (ihom ((restrictScalars f).mapDerivedCategory.obj (X' ⊗ E'))).map c := by
  have h := (bimoduleCoinductionHomIso f).hom.naturality
    (X := (op (X ⊗ E), V)) (Y := (op (X' ⊗ E'), V')) ((a ⊗ₘ b).op, c)
  change (restrictScalars f).mapDerivedCategory.map
      ((MonoidalClosed.pre (a ⊗ₘ b)).app ((derivedCoinduction f).obj V) ≫
        (ihom (X' ⊗ E')).map ((derivedCoinduction f).map c)) ≫
      (bimoduleCoinductionHomIso f).hom.app (op (X' ⊗ E'), V') =
    (bimoduleCoinductionHomIso f).hom.app (op (X ⊗ E), V) ≫
      (MonoidalClosed.pre
        ((restrictScalars f).mapDerivedCategory.map (a ⊗ₘ b))).app V ≫
      (ihom ((restrictScalars f).mapDerivedCategory.obj (X' ⊗ E'))).map c at h
  dsimp only [derivedBimoduleComparison, derivedBimoduleHom, Functor.comp_obj]
  rw [← Category.assoc, ← Functor.map_comp]
  simp only [Category.assoc]
  rw [closedCurry_naturality a b ((derivedCoinduction f).map c),
    Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  simpa only [Functor.map_comp, Category.assoc] using congrArg
    (fun t ↦ (restrictScalars f).mapDerivedCategory.map
      (bimoduleClosedCurry X E ((derivedCoinduction f).obj V)) ≫ t) h

private lemma bimoduleComparison_isIso (f : S →+* B)
    (E X : DerivedCategory (ModuleCat.{u} B))
    (V : DerivedCategory (ModuleCat.{u} S)) :
    IsIso (derivedBimoduleComparison f E X V) := by
  have := closedCurry_isIso X E ((derivedCoinduction f).obj V)
  unfold derivedBimoduleComparison
  infer_instance

private def bimoduleComparisonNatIso (f : S →+* B)
    (E : DerivedCategory (ModuleCat.{u} B)) :
    derivedBimoduleHomLeft f E ≅ derivedBimoduleHomRight f E := by
  let t : derivedBimoduleHomLeft f E ⟶ derivedBimoduleHomRight f E :=
    { app Z := derivedBimoduleComparison f E Z.1.unop Z.2
      naturality Z Z' g := by
        have h := bimoduleComparison_naturality f g.1.unop (𝟙 E) g.2
        change (restrictScalars f).mapDerivedCategory.map
            ((MonoidalClosed.pre g.1.unop).app ((derivedBimoduleHom f E).obj Z.2) ≫
              (ihom Z'.1.unop).map ((ihom E).map ((derivedCoinduction f).map g.2))) ≫
            derivedBimoduleComparison f E Z'.1.unop Z'.2 =
          derivedBimoduleComparison f E Z.1.unop Z.2 ≫
            (MonoidalClosed.pre
              ((restrictScalars f).mapDerivedCategory.map (g.1.unop ▷ E))).app Z.2 ≫
            (ihom ((restrictScalars f).mapDerivedCategory.obj (Z'.1.unop ⊗ E))).map g.2
        dsimp only [derivedBimoduleHom, Functor.comp_obj] at h ⊢
        simpa only [MonoidalClosed.pre_id, NatTrans.id_app, Category.id_comp,
          CategoryTheory.Functor.map_id, Functor.map_comp, Category.comp_id, tensorHom_id,
          Category.assoc] using h }
  have : ∀ Z, IsIso (t.app Z) := fun Z ↦
    bimoduleComparison_isIso f E Z.1.unop Z.2
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

private lemma curry'_pre {C : Type*} [Category C] [MonoidalCategory C]
    [MonoidalClosed C] {X Y Z : C} (g : X ⟶ Y) (k : Y ⟶ Z) :
    MonoidalClosed.curry' k ≫ (MonoidalClosed.pre g).app Z =
      MonoidalClosed.curry' (g ≫ k) := by
  simp only [MonoidalClosed.curry', MonoidalClosed.curry_pre_app,
    ← Category.assoc, rightUnitor_naturality]

private lemma class_of_naturality
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
    (F : C ⥤ D) {X Z : C} {Y : D} (g : X ⟶ Z)
    (ι : 𝟙_ D ⟶ F.obj (𝟙_ C))
    (s : F.obj ((ihom Z).obj Z) ⟶ (ihom (F.obj Z)).obj Y)
    (t : F.obj ((ihom X).obj Z) ⟶ (ihom (F.obj X)).obj Y) (e : F.obj Z ⟶ Y)
    (hn : F.map ((MonoidalClosed.pre g).app Z) ≫ t =
      s ≫ (MonoidalClosed.pre (F.map g)).app Y)
    (hc : ι ≫ F.map (MonoidalClosed.curry' (𝟙 Z)) ≫ s = MonoidalClosed.curry' e) :
    ι ≫ F.map (MonoidalClosed.curry' g) ≫ t =
      MonoidalClosed.curry' (F.map g ≫ e) := by
  have hg : MonoidalClosed.curry' (𝟙 Z) ≫ (MonoidalClosed.pre g).app Z =
      MonoidalClosed.curry' g := by simpa using curry'_pre g (𝟙 Z)
  rw [← hg, F.map_comp, Category.assoc, hn]
  simpa only [Category.assoc, curry'_pre] using congrArg
    (fun h ↦ h ≫ (MonoidalClosed.pre (F.map g)).app Y) hc

private lemma coinduction_class (f : S →+* B)
    (X : DerivedCategory (ModuleCat.{u} B)) (V : DerivedCategory (ModuleCat.{u} S))
    (g : X ⟶ (derivedCoinduction f).obj V) :
    bimoduleScalarUnit f ≫
        (restrictScalars f).mapDerivedCategory.map (MonoidalClosed.curry' g) ≫
        (bimoduleCoinductionHomIso f).hom.app (op X, V) =
      MonoidalClosed.curry' (((derivedCoinductionAdjunction f).homEquiv X V).symm g) := by
  have hn := (bimoduleCoinductionHomIso f).hom.naturality
    (X := (op ((derivedCoinduction f).obj V), V)) (Y := (op X, V)) (g.op, 𝟙 V)
  change (restrictScalars f).mapDerivedCategory.map
      ((MonoidalClosed.pre g).app ((derivedCoinduction f).obj V) ≫
        (ihom X).map ((derivedCoinduction f).map (𝟙 V))) ≫
      (bimoduleCoinductionHomIso f).hom.app (op X, V) =
    (bimoduleCoinductionHomIso f).hom.app (op ((derivedCoinduction f).obj V), V) ≫
      (MonoidalClosed.pre ((restrictScalars f).mapDerivedCategory.map g)).app V ≫
      (ihom ((restrictScalars f).mapDerivedCategory.obj X)).map (𝟙 V) at hn
  erw [CategoryTheory.Functor.map_id] at hn
  erw [CategoryTheory.Functor.map_id] at hn
  erw [Category.comp_id] at hn
  erw [CategoryTheory.Functor.map_id] at hn
  erw [Category.comp_id] at hn
  have hc' : bimoduleScalarUnit f ≫
      (restrictScalars f).mapDerivedCategory.map
        (MonoidalClosed.curry' (𝟙 ((derivedCoinduction f).obj V))) ≫
      (bimoduleCoinductionHomIso f).hom.app (op ((derivedCoinduction f).obj V), V) =
    MonoidalClosed.curry' ((derivedCoinductionAdjunction f).counit.app V) :=
      derived_coinduction_enriched_class f V
  simpa only [Adjunction.homEquiv_counit] using
    class_of_naturality (restrictScalars f).mapDerivedCategory g (bimoduleScalarUnit f)
      ((bimoduleCoinductionHomIso f).hom.app (op ((derivedCoinduction f).obj V), V))
      ((bimoduleCoinductionHomIso f).hom.app (op X, V))
      ((derivedCoinductionAdjunction f).counit.app V) hn hc'

private lemma bimodule_class (f : S →+* B)
    (E X : DerivedCategory (ModuleCat.{u} B)) (V : DerivedCategory (ModuleCat.{u} S))
    (g : X ⟶ (derivedBimoduleHom f E).obj V) :
    bimoduleScalarUnit f ≫
        (restrictScalars f).mapDerivedCategory.map (MonoidalClosed.curry' g) ≫
        derivedBimoduleComparison f E X V =
      MonoidalClosed.curry' (((derivedBimoduleAdjunction f E).homEquiv X V).symm g) := by
  let := DerivedCategory.braidedCategory' (ModuleCat.{u} B)
  change bimoduleScalarUnit f ≫
      (restrictScalars f).mapDerivedCategory.map (MonoidalClosed.curry' g) ≫
      (restrictScalars f).mapDerivedCategory.map
        (bimoduleClosedCurry X E ((derivedCoinduction f).obj V)) ≫
      (bimoduleCoinductionHomIso f).hom.app (op (X ⊗ E), V) = _
  rw [← Functor.map_comp_assoc, closedCurry_class]
  have h := coinduction_class f (X ⊗ E) V
    ((β_ E X).inv ≫ MonoidalClosed.uncurry g)
  have hclosed :
      (((ihom.adjunction E).ofNatIsoLeft
        (BraidedCategory.tensorLeftIsoTensorRight E)).homEquiv X
          ((derivedCoinduction f).obj V)).symm g =
        (β_ E X).inv ≫ MonoidalClosed.uncurry g := by
    rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
    rfl
  rw [derivedBimoduleAdjunction, Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
  change _ = MonoidalClosed.curry'
    (((derivedCoinductionAdjunction f).homEquiv (X ⊗ E) V).symm
      ((((ihom.adjunction E).ofNatIsoLeft
        (BraidedCategory.tensorLeftIsoTensorRight E)).homEquiv X
          ((derivedCoinduction f).obj V)).symm g))
  rw [hclosed]
  exact h

private lemma bimodule_counit (f : S →+* B)
    (E : DerivedCategory (ModuleCat.{u} B)) (V : DerivedCategory (ModuleCat.{u} S)) :
    (derivedBimoduleAdjunction f E).counit.app V = derivedBimoduleEvaluation f E V := by
  let := DerivedCategory.braidedCategory' (ModuleCat.{u} B)
  simp [derivedBimoduleHom, derivedBimoduleAdjunction, derivedBimoduleEvaluation,
    Adjunction.comp_counit_app, Adjunction.ofNatIsoLeft]

/-- The mixed-ring tensor-Hom isomorphism, its representative with precomposition
B-action, the induced H⁰ adjunction, evaluation counit, and restriction compatibility.
Here H⁰ of an R-derived object is represented by maps from the derived tensor unit
R[0]. Thus curry' sends a derived morphism to exactly its H⁰ class. The scalar unit
S[0] → U(B[0]) gives the corresponding class after restriction.
Source: Stacks Project, dga.tex, Tags 09LN and 09LT; sites-cohomology.tex, Tags 0A95,
0A96 and 08J9 (blueprint: lem-trf-derived-bimodule-tensor-hom).

Proof (the seven steps of the DAG):
1. Choose an S-K-injective representative I of V and a B-K-flat resolution Q of
E (prop-pur-kinjective-resolutions-exist, lem-pc-kflat-resolution). The ordinary
coinduction adjunction identifies Hom_B(E,Hom_S(B,I)) with Hom_S(E,I), by evaluation
at one, with inverse z(e)(b)=z(be). This intertwines the B-action with precomposition.
The action commutes with the differential because b has degree zero. The invariance
lemma lem-pur-rhom-well-defined compares this model with Hom_S(Q,I) and proves
independence of representatives and resolutions.
2. Chain currying sends f to (x tensor e ↦ f(x)(e)). B-balancing follows from
f(bx)(e)=f(x)(be). Products over all degree pairs identify the unbounded terms.
Both differentials evaluate to d_I f(x)(e) - (-1)^(p+n) f(x)(d_Q e)
- (-1)^n f(d_X x)(e). Hence this is an S-linear chain isomorphism, natural in
all three variables (def-sc-module-total-hom-complex, def-pc-tensor-complex-sheaves).
3. Hom_S(Q,I) is B-K-injective: for acyclic A, the complex A tensor_B Q is acyclic
by def-pc-kflat-complex. Restriction preserves acyclicity. Chain currying and
lem-sc-module-hom-complex-quotient identify maps from A into Hom_S(Q,I), up to
homotopy, with maps from U(A tensor Q) into I, which vanish by K-injectivity.
This does not require restriction to preserve K-injectives.
4. Resolve a representative C of X by B-K-flat P. The zigzag
P tensor E ← P tensor Q → C tensor Q consists of quasi-isomorphisms by
lem-pc-derived-tensor-second-factor-functor and def-pc-module-kflat-complex.
Thus C tensor Q represents X tensor^L E, and Hom_B(C,Hom_S(Q,I)) computes the
left derived Hom. Localize the chain isomorphism of step 2 to obtain the comparison.
The native closed tensor/Hom structures compute precisely these objects, by
def-pur-derived-internal-hom; its ordinary-module normalization is supplied by
lem-trf-algebraic-shriek-derived-hom-adjunction.
5. Precomposition in C and Q and postcomposition in I commute with currying.
The quasi-isomorphisms of models are inverted by lem-pur-rhom-well-defined and
lem-pc-derived-tensor-second-factor-functor. The localization description in
def-weil-abstract-derived-category extends the commuting squares to every derived
morphism. This gives the natural isomorphisms and their E-naturality equation.
6. Apply H⁰ and lem-pur-rhom-into-kinjective-local. The degree-zero currying map
is the Hom-set adjunction. Under the closed-structure identification H⁰=Hom(R[0],-),
its square is exactly the displayed curry' equation. The inverse sends a map g to
(x tensor e ↦ g(x)(e)); at the identity it is evaluation. The unit sends x to
(e ↦ x tensor e). Evaluating these formulas proves the two triangle identities;
the constructed derivedBimoduleAdjunction is this composite adjunction.
7. Restrict every S-object and S-map along any K → S. Restriction is exact and
keeps underlying differentials and cohomology, so it preserves the comparison
quasi-isomorphisms. All balancing, currying, action, unit and evaluation formulas
are unchanged. Applying restriction to the H⁰ square and counit equality gives
the last clause. This restricts RHom_S itself, never replaces it by RHom_K.
No flatness of B/S, perfection of E, or bound on V was used. -/
theorem derived_bimodule_tensor_hom (f : S →+* B) :
    (∀ (E : CochainComplex (ModuleCat.{u} B) ℤ)
        (I : CochainComplex (ModuleCat.{u} S) ℤ) [I.IsKInjective],
      IsIso (derivedBimoduleHomModel f E I)) ∧
    (∃ T : ∀ (E : CochainComplex (ModuleCat.{u} B) ℤ)
        (I : CochainComplex (ModuleCat.{u} S) ℤ),
        ((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
            (CochainComplex.moduleHomComplex E ((coinductionComplexFunctor f).obj I)) ≅
          CochainComplex.moduleHomComplex
            (((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj E) I,
      (∀ (E : CochainComplex (ModuleCat.{u} B) ℤ)
        (I : CochainComplex (ModuleCat.{u} S) ℤ) (n p q : ℤ) (h : p + n = q)
        (z : (CochainComplex.moduleHomComplex E
          ((coinductionComplexFunctor f).obj I)).X n) (x : E.X p),
        (((T E I).hom.f n z).v p q h) x =
          (coinductionEvaluation f I).f q ((z.v p q h) x)) ∧
      (∀ (E : CochainComplex (ModuleCat.{u} B) ℤ)
        (I : CochainComplex (ModuleCat.{u} S) ℤ) (n p q : ℤ) (h : p + n = q)
        (z : (CochainComplex.moduleHomComplex
          (((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj E) I).X n)
        (x : E.X p) (b : B),
        (coinductionEvaluation f I).f q
            (b • (((T E I).inv.f n z).v p q h) x) = (z.v p q h) (b • x))) ∧
    (∀ E : DerivedCategory (ModuleCat.{u} B),
      ∃ θ : derivedBimoduleHomLeft f E ≅ derivedBimoduleHomRight f E,
        ∀ (X : DerivedCategory (ModuleCat.{u} B)) (V : DerivedCategory (ModuleCat.{u} S)),
          θ.hom.app (op X, V) = derivedBimoduleComparison f E X V) ∧
    (∀ (E E' X : DerivedCategory (ModuleCat.{u} B))
        (V : DerivedCategory (ModuleCat.{u} S)) (a : E ⟶ E'),
      (restrictScalars f).mapDerivedCategory.map
          ((ihom X).map ((MonoidalClosed.pre a).app ((derivedCoinduction f).obj V))) ≫
          derivedBimoduleComparison f E X V =
        derivedBimoduleComparison f E' X V ≫
          (MonoidalClosed.pre ((restrictScalars f).mapDerivedCategory.map (X ◁ a))).app V) ∧
    (∀ (E X : DerivedCategory (ModuleCat.{u} B)) (V : DerivedCategory (ModuleCat.{u} S)),
      Function.Bijective (fun g : X ⟶ (derivedBimoduleHom f E).obj V ↦
        bimoduleScalarUnit f ≫
          (restrictScalars f).mapDerivedCategory.map (MonoidalClosed.curry' g)) ∧
      ∀ g : X ⟶ (derivedBimoduleHom f E).obj V,
        bimoduleScalarUnit f ≫
            (restrictScalars f).mapDerivedCategory.map (MonoidalClosed.curry' g) ≫
            derivedBimoduleComparison f E X V =
          MonoidalClosed.curry' (((derivedBimoduleAdjunction f E).homEquiv X V).symm g)) ∧
    (∀ (E : DerivedCategory (ModuleCat.{u} B)) (V : DerivedCategory (ModuleCat.{u} S)),
      (derivedBimoduleAdjunction f E).counit.app V = derivedBimoduleEvaluation f E V) ∧
    (∀ (K : Type u) [CommRing K] [HasDerivedCategory.{u} (ModuleCat.{u} K)] (k : K →+* S)
        (E X : DerivedCategory (ModuleCat.{u} B)) (V : DerivedCategory (ModuleCat.{u} S)),
      IsIso ((restrictScalars k).mapDerivedCategory.map (derivedBimoduleComparison f E X V)) ∧
      (∀ g : X ⟶ (derivedBimoduleHom f E).obj V,
        (restrictScalars k).mapDerivedCategory.map
            (bimoduleScalarUnit f ≫
              (restrictScalars f).mapDerivedCategory.map (MonoidalClosed.curry' g) ≫
              derivedBimoduleComparison f E X V) =
          (restrictScalars k).mapDerivedCategory.map
            (MonoidalClosed.curry'
              (((derivedBimoduleAdjunction f E).homEquiv X V).symm g))) ∧
      (restrictScalars k).mapDerivedCategory.map
          ((derivedBimoduleAdjunction f E).counit.app V) =
        (restrictScalars k).mapDerivedCategory.map (derivedBimoduleEvaluation f E V)) := by
  obtain ⟨hJ, eS, eB, T, θ, κ, heS, heB, hT, hTi, hθ, hκ, hscalar⟩ :=
    algebraicShriek_derivedHom_adjunction f
  refine ⟨?_, ⟨T, hT, hTi⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro E I hI
    have : ((coinductionComplexFunctor f).obj I).IsKInjective := hJ I hI
    have hmodel : IsIso (coinductionHomComparison E ((coinductionComplexFunctor f).obj I)) := by
      rw [← heB E _ (hJ I hI)]
      infer_instance
    unfold derivedBimoduleHomModel
    infer_instance
  · intro E
    exact ⟨bimoduleComparisonNatIso f E, fun _ _ ↦ rfl⟩
  · intro E E' X V a
    have h := bimoduleComparison_naturality f (𝟙 X) a (𝟙 V)
    simpa using h
  · intro E X V
    refine ⟨?_, bimodule_class f E X V⟩
    have hi := bimoduleComparison_isIso f E X V
    let e := (derivedBimoduleAdjunction f E).homEquiv X V
    let c := MonoidalClosed.curryHomEquiv'
      (X := (derivedBimoduleTensor f E).obj X) (Y := V)
    let q := (asIso (derivedBimoduleComparison f E X V)).homToEquiv
      (Z := 𝟙_ (DerivedCategory (ModuleCat.{u} S)))
    have h : Function.Bijective (fun g : X ⟶ (derivedBimoduleHom f E).obj V ↦
        (bimoduleScalarUnit f ≫
          (restrictScalars f).mapDerivedCategory.map (MonoidalClosed.curry' g)) ≫
          derivedBimoduleComparison f E X V) := by
      have heq : (fun g : X ⟶ (derivedBimoduleHom f E).obj V ↦
          (bimoduleScalarUnit f ≫
            (restrictScalars f).mapDerivedCategory.map (MonoidalClosed.curry' g)) ≫
            derivedBimoduleComparison f E X V) =
          fun g ↦ MonoidalClosed.curry'
            (((derivedBimoduleAdjunction f E).homEquiv X V).symm g) := by
        funext g
        simpa only [Category.assoc] using bimodule_class f E X V g
      rw [heq]
      exact c.bijective.comp e.symm.bijective
    exact (Function.Bijective.of_comp_iff' q.bijective _).mp h
  · exact bimodule_counit f
  · intro K _ _ k E X V
    have := bimoduleComparison_isIso f E X V
    refine ⟨inferInstance, ?_, ?_⟩
    · intro g
      exact congrArg ((restrictScalars k).mapDerivedCategory.map) (bimodule_class f E X V g)
    · exact congrArg ((restrictScalars k).mapDerivedCategory.map) (bimodule_counit f E V)

end ModuleCat
