/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.CochainTensorCoherenceData
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

public import Sheaf.Paper.RingedTopoiTensorSections
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.Paper.KFlatRingedToposPullback
import all Sheaf.Algebra.Homology.DerivedCoefficientMapDescent
import all Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all Sheaf.Paper.ResolvingRepresentativeWhiskering
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Homology.Functor

/-! # Normalized derived pullback of strict reduction towers

Source: Stacks Project, Tags 06YS, 06YY, 07A4 and 03EL
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


universe a b c d w w' t t'
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace CategoryTheory.StrictReduction

variable {A : Type a} [Category.{b} A] [Abelian A] [MonoidalCategory A]

/-- Tensor with the actual coefficient tower, retaining every transition.
Source: Stacks 06YY, applied to strict towers
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def reduction (Q : ℕᵒᵖ ⥤ A) : A ⥤ (ℕᵒᵖ ⥤ A) :=
  Functor.const ℕᵒᵖ ⋙ tensorRight Q

/-- The ordinary augmentation induced by the coefficient unit.
Source: Stacks 03CZ and 06YY
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def augmentation (Q : ℕᵒᵖ ⥤ A) (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q) :
    Functor.const ℕᵒᵖ ⟶ reduction Q :=
  Functor.whiskerLeft (Functor.const ℕᵒᵖ)
    ((rightUnitorNatIso (ℕᵒᵖ ⥤ A)).inv ≫ (curriedTensor (ℕᵒᵖ ⥤ A)).flip.map e)

variable [MonoidalPreadditive A]

/-- Additivity of termwise tensor reduction.
Source: Stacks 03EK, bilinearity of tensor
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
instance reduction_additive (Q : ℕᵒᵖ ⥤ A) : (reduction Q).Additive where
  map_add {M N} f g := by
    ext n
    change (f + g) ▷ Q.obj n = f ▷ Q.obj n + g ▷ Q.obj n
    exact (tensorRight (Q.obj n)).map_add (f := f) (g := g)

/-- Exact termwise pullback on strict towers.
Source: Stacks 02MZ, limits and colimits in diagram categories
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
abbrev termwise {B : Type c} [Category.{d} B] (F : A ⥤ B) :=
  (Functor.whiskeringRight ℕᵒᵖ A B).obj F

variable {B : Type c} [Category.{d} B] [Abelian B]

/-- Termwise preservation of finite limits, using pointwise limits.
Source: Stacks 02MZ (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
instance termwise_limits (F : A ⥤ B) [PreservesFiniteLimits F] :
    PreservesFiniteLimits (termwise F) where
  preservesFiniteLimits L := preservesLimitsOfShape_of_evaluation _ L (fun n ↦
    inferInstanceAs (PreservesLimitsOfShape L ((evaluation ℕᵒᵖ A).obj n ⋙ F)))

/-- Termwise preservation of finite colimits, using pointwise colimits.
Source: Stacks 02MZ (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
instance termwise_colimits (F : A ⥤ B) [PreservesFiniteColimits F] :
    PreservesFiniteColimits (termwise F) where
  preservesFiniteColimits L := preservesColimitsOfShape_of_evaluation _ L (fun n ↦
    inferInstanceAs (PreservesColimitsOfShape L ((evaluation ℕᵒᵖ A).obj n ⋙ F)))

/-- Constant towers commute with actual termwise pullback.
Source: Stacks 06YY (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def constantSquare (F : A ⥤ B) :
    Functor.const ℕᵒᵖ ⋙ termwise F ≅ F ⋙ Functor.const ℕᵒᵖ :=
  NatIso.ofComponents (fun M ↦ Functor.constComp ℕᵒᵖ M F)

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ℕᵒᵖ ⥤ A)]

/-- The universal derived reduction and its augmentation. The counit is part of the
left-derived universal property, and is required to compute every good representative.
Source: Stacks 06YY and 06XN (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
structure Model (Q : ℕᵒᵖ ⥤ A) (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q)
    (good : CochainComplex A ℤ → Prop) where
  B : DerivedCategory A ⥤ DerivedCategory (ℕᵒᵖ ⥤ A)
  counit : DerivedCategory.Q ⋙ B ⟶
    (reduction Q).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : B.IsLeftDerivedFunctor counit (HomologicalComplex.quasiIso A (.up ℤ))
  computes : ∀ P, good P → IsIso (counit.app P)
  i : (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory ⟶ B
  augmentation_eq : ∀ P, good P →
    i.app (DerivedCategory.Q.obj P) ≫ counit.app P =
      (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (augmentation Q e) (.up ℤ)).app P)

variable [MonoidalCategory B]

/-- The pulled-back coefficient unit, using the normalized pullback unit isomorphism.
Source: Stacks 03EL (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def pulledUnit (F : A ⥤ B) (j : F.obj (𝟙_ A) ≅ 𝟙_ B)
    (Q : ℕᵒᵖ ⥤ A) (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q) :
    (Functor.const ℕᵒᵖ).obj (𝟙_ B) ⟶ Q ⋙ F :=
  (Functor.const ℕᵒᵖ).map j.inv ≫ (Functor.constComp ℕᵒᵖ (𝟙_ A) F).inv ≫
    Functor.whiskerRight e F

/-- The ordinary comparison as one isomorphism of strict towers, natural in the input.
Source: Stacks 03EL (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def ordinaryComparison (F : A ⥤ B)
    (mu : ∀ M N, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (hmu : ∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (mu M' N').hom =
        (mu M N).hom ≫ (F.map f ⊗ₘ F.map g)) (Q : ℕᵒᵖ ⥤ A) :
    reduction Q ⋙ termwise F ≅ F ⋙ reduction (Q ⋙ F) :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun n ↦ mu M (Q.obj n))
    (fun {m n} g ↦ by
      change F.map (𝟙 M ⊗ₘ Q.map g) ≫ (mu M (Q.obj n)).hom =
        (mu M (Q.obj m)).hom ≫ (𝟙 (F.obj M) ⊗ₘ F.map (Q.map g))
      simpa only [F.map_id] using hmu (𝟙 M) (Q.map g)))
    (fun {M N} f ↦ by
      ext n
      change F.map (f ▷ Q.obj n) ≫ (mu N (Q.obj n)).hom =
        (mu M (Q.obj n)).hom ≫ (F.map f ▷ F.obj (Q.obj n))
      simpa only [F.map_id, tensorHom_id] using hmu f (𝟙 (Q.obj n)))

variable [HasDerivedCategory.{w'} B] [HasDerivedCategory.{t'} (ℕᵒᵖ ⥤ B)]

/-- The canonical localization of the constant-tower square.
Source: Stacks 06YY (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def constantDerivedSquare (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory ⋙ (termwise F).mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory :=
  letI : PreservesFiniteLimits (Functor.const ℕᵒᵖ ⋙ termwise F) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits (Functor.const ℕᵒᵖ ⋙ termwise F) :=
    comp_preservesFiniteColimits _ _
  letI : PreservesFiniteLimits (F ⋙ Functor.const ℕᵒᵖ) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits (F ⋙ Functor.const ℕᵒᵖ) :=
    comp_preservesFiniteColimits _ _
  (Functor.mapDerivedCategoryCompIso (Functor.const ℕᵒᵖ) (termwise F)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (constantSquare F) ≪≫
      Functor.mapDerivedCategoryCompIso F (Functor.const ℕᵒᵖ)

variable [MonoidalPreadditive B]

/-- Normalization by the universal reduction counits on every good representative.
The equation is the conjugation formula, with both exact-localization factors explicit.
Source: Stacks 06YY and 07A4
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def IsNormalized (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (Q : ℕᵒᵖ ⥤ A) (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q)
    (j : F.obj (𝟙_ A) ≅ 𝟙_ B)
    (goodA : CochainComplex A ℤ → Prop) (goodB : CochainComplex B ℤ → Prop)
    (MY : Model Q e goodA) (MX : Model (Q ⋙ F) (pulledUnit F j Q e) goodB)
    (mu : ∀ M N, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (hmu : ∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (mu M' N').hom =
        (mu M N).hom ≫ (F.map f ⊗ₘ F.map g))
    (tau : MY.B ⋙ (termwise F).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ MX.B) : Prop :=
  ∀ P, goodA P →
    (termwise F).mapDerivedCategory.map (MY.counit.app P) ≫
        (termwise F).mapDerivedCategoryFactors.hom.app
          (((reduction Q).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryComparison F mu hmu Q) (.up ℤ)).hom.app P) =
      tau.hom.app (DerivedCategory.Q.obj P) ≫
        MX.B.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        MX.counit.app ((F.mapHomologicalComplex (.up ℤ)).obj P)

/-- Evaluation of the universal reduction counit, with its exact localization factor.
Source: Stacks 06YY, levelwise computation
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def evaluationCounit (Q : ℕᵒᵖ ⥤ A)
    (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q)
    (good : CochainComplex A ℤ → Prop) (M : Model Q e good) (n : ℕ) :
    DerivedCategory.Q ⋙ M.B ⋙ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ⟶
      (reduction Q).mapHomologicalComplex (.up ℤ) ⋙
        ((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight M.counit ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ≫
    Functor.whiskerLeft ((reduction Q).mapHomologicalComplex (.up ℤ))
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom

end CategoryTheory.StrictReduction

open CategoryTheory.Functor in
private theorem cochainDerivedExists
    {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type c} [Category.{d} B] [Abelian B] [HasDerivedCategory.{t} B]
    (E : A ⥤ B) [E.Additive] (good : CochainComplex A ℤ → Prop)
    (res : ∀ K, ∃ (L : CochainComplex A ℤ) (p : L ⟶ K), good L ∧ QuasiIso p)
    (inverts : ∀ {K L : CochainComplex A ℤ} (p : K ⟶ L), QuasiIso p →
      good K → good L → QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map p)) :
    ∃ (T : DerivedCategory A ⥤ DerivedCategory B)
      (β : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
      T.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso A (.up ℤ)) ∧
      ∀ K, good K → IsIso (β.app K) := by
  classical
  let q := HomotopyCategory.quotient A (.up ℤ)
  let F := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  let P : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex A ℤ, good K ∧ q.obj K = X
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X),
        Y ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, p, hL, hp⟩ := res K
    exact ⟨q.obj L, q.map p, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp⟩
  have hinv : ∀ (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y),
      X ∈ P → Y ∈ P → HomotopyCategory.quasiIso A (.up ℤ) s → IsIso (F.map s) := by
    rintro X Y s ⟨K, hK, rfl⟩ ⟨L, hL, rfl⟩ hs
    obtain ⟨a, rfl⟩ := q.map_surjective s
    have ha := (HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 hs
    have hg := inverts a ha hK hL
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hg)
  obtain ⟨hpw, T, ε, huniv, _, hcomp⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) F P hres hinv
  let : F.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (.up ℤ)) := hpw
  let : T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) := huniv
  let α := (Functor.associator q DerivedCategory.Qh T).hom ≫ Functor.whiskerLeft q ε
  have hα := pointwise_precomp_full q DerivedCategory.Qh F T ε
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor T ε
      (HomotopyCategory.quasiIso A (.up ℤ)))
  let iq := DerivedCategory.quotientCompQhIso A
  let jq : q ⋙ F ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let β : DerivedCategory.Q ⋙ T ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight iq.inv T ≫ α ≫ jq.hom
  have hβ := pointwise_change_iso T iq jq α hα
  have huni : T.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso A (.up ℤ)) :=
    ⟨hβ.isRightKanExtension⟩
  let := huni
  refine ⟨T, β, huni, ?_⟩
  intro K hK
  have := hcomp (q.obj K) ⟨K, hK, rfl⟩
  dsimp [β, α]
  infer_instance

private theorem cochainCounitPostcompose
    {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type c} [Category.{d} B] [Abelian B] [HasDerivedCategory.{t} B]
    (E : A ⥤ B) [E.Additive] (good : CochainComplex A ℤ → Prop)
    (res : ∀ K, ∃ (L : CochainComplex A ℤ) (p : L ⟶ K), good L ∧ QuasiIso p)
    (T : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (huni : T.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ)))
    (computes : ∀ K, good K → IsIso (ε.app K))
    {D : Type w'} [Category.{t'} D] (H : DerivedCategory B ⥤ D) :
    (T ⋙ H).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Q T H).inv ≫ Functor.whiskerRight ε H)
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
  classical
  let q := HomotopyCategory.quotient A (.up ℤ)
  let G := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  let iq := DerivedCategory.quotientCompQhIso A
  let jq : q ⋙ G ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let α₀ := Functor.whiskerRight iq.hom T ≫ ε ≫ jq.inv
  let αpre : q ⋙ (DerivedCategory.Qh ⋙ T) ⟶ q ⋙ G :=
    (Functor.associator _ _ _).inv ≫ α₀
  let α : DerivedCategory.Qh ⋙ T ⟶ G :=
    ((Functor.whiskeringLeft _ _ _).obj q).preimage αpre
  have hαpre : Functor.whiskerLeft q α = αpre :=
    ((Functor.whiskeringLeft _ _ _).obj q).map_preimage αpre
  have hα : T.IsRightKanExtension α := by
    apply Functor.kan_of_precomp_quotient _ _ _ α
    let := huni
    have := Functor.IsLeftDerivedFunctor.isRightKanExtension T ε
      (HomologicalComplex.quasiIso A (.up ℤ))
    have hh := Functor.kan_change_iso T iq.symm jq.symm ε
    have he : (Functor.associator q DerivedCategory.Qh T).hom ≫
        Functor.whiskerLeft q α = α₀ := by
      rw [hαpre]
      simp [αpre]
    rw [he]
    exact hh
  let P : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex A ℤ, good K ∧ q.obj K = X
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X),
        Y ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, p, hL, hp⟩ := res K
    exact ⟨q.obj L, q.map p, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp⟩
  have hαiso : ∀ X, X ∈ P → IsIso (α.app X) := by
    rintro X ⟨K, hK, rfl⟩
    have := computes K hK
    have he := NatTrans.congr_app hαpre K
    change α.app (q.obj K) = _ at he
    rw [he]
    dsimp [αpre, α₀]
    infer_instance
  have hinv : ∀ (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y),
      X ∈ P → Y ∈ P → HomotopyCategory.quasiIso A (.up ℤ) s → IsIso (G.map s) := by
    intro X Y s hX hY hs
    have := hαiso X hX
    have := hαiso Y hY
    have : IsIso (DerivedCategory.Qh.map s) :=
      Localization.inverts DerivedCategory.Qh _ _ hs
    rw [← isIso_comp_left_iff (α.app X), ← α.naturality s]
    change IsIso (T.map (DerivedCategory.Qh.map s) ≫ α.app Y)
    infer_instance
  have : (HomotopyCategory.quasiIso A (.up ℤ)).HasTwoOutOfThreeProperty :=
    (HomotopyCategory.quasiIso_saturated_triangulated A).2.2.2.2.1
  have habs : H.PreservesRightKanExtension G DerivedCategory.Qh :=
    Functor.pro_absolute (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh G H
      (fun X ↦ by
        obtain ⟨Y, _, hY, _⟩ := Functor.resolvingClass_essentialConstancy
          (HomotopyCategory.quasiIso A (.up ℤ)) G P hres hinv X
        exact ⟨Y, hY⟩)
  let := hα
  let := habs
  let αH := (Functor.associator DerivedCategory.Qh T H).inv ≫
    Functor.whiskerRight α H
  have hαH : (T ⋙ H).IsRightKanExtension αH := by infer_instance
  let := hαH
  have hpre := Functor.kan_precomp_quotient DerivedCategory.Qh (G ⋙ H) (T ⋙ H) αH
  let jH : q ⋙ (G ⋙ H) ≅
      (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙ H :=
    (Functor.associator q G H).symm ≪≫ Functor.isoWhiskerRight jq H
  let δpre := (Functor.associator q DerivedCategory.Qh (T ⋙ H)).hom ≫
    Functor.whiskerLeft q αH
  let δ := Functor.whiskerRight iq.inv (T ⋙ H) ≫ δpre ≫ jH.hom
  have hδ : (T ⋙ H).IsRightKanExtension δ := by
    let := hpre
    exact Functor.kan_change_iso (T ⋙ H) iq jH δpre
  have heq : δ = (Functor.associator DerivedCategory.Q T H).inv ≫
      Functor.whiskerRight ε H := by
    ext K
    have he := NatTrans.congr_app hαpre K
    change α.app (q.obj K) = _ at he
    dsimp [δ, δpre, αH, jH]
    rw [he]
    dsimp [αpre, α₀]
    simp only [Category.assoc, Category.id_comp]
    erw [Category.id_comp]
    rw [← H.map_comp_assoc, ← T.map_comp_assoc, Iso.inv_hom_id_app,
      T.map_id, Category.id_comp, ← H.map_comp, Category.assoc, Iso.inv_hom_id_app]
    change H.map (ε.app K ≫ 𝟙 _) = H.map (ε.app K)
    exact H.congr_map (Category.comp_id _)
  exact ⟨heq ▸ hδ⟩

private noncomputable def cochainRepresentativeWhiskering
    {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory.{w} A]
    (good : CochainComplex A ℤ → Prop)
    (res : ∀ K, ∃ (L : CochainComplex A ℤ) (p : L ⟶ K), good L ∧ QuasiIso p)
    (E : Type c) [Category.{d} E] :
    ((Functor.whiskeringLeft _ _ E).obj
      (ObjectProperty.ι good ⋙ DerivedCategory.Q)).FullyFaithful := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let P : ObjectProperty (CochainComplex A ℤ) := good
  let S : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ good X.as
  let f := S.lift (P.ι ⋙ q) (fun X ↦ X.property)
  have : f.Full := ⟨by
    intro X Y g
    obtain ⟨a, ha⟩ := q.map_surjective g.hom
    refine ⟨ObjectProperty.homMk a, ?_⟩
    exact ObjectProperty.hom_ext _ ha⟩
  have : f.EssSurj := ⟨by
    intro X
    obtain ⟨Y, hy⟩ := HomotopyCategory.quotient_obj_surjective X.obj
    refine ⟨⟨Y, ?_⟩, ⟨ObjectProperty.isoMk S (eqToIso hy)⟩⟩
    change S (q.obj Y)
    rw [hy]
    exact X.property⟩
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : S.FullSubcategory) (s : Y.obj ⟶ X), HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨L, p, hL, hp⟩ := res X.as
    exact ⟨⟨q.obj L, hL⟩, q.map p,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp⟩
  have : (S.ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage S.ι) :=
    CategoryTheory.restriction_localization _ _ S hres
  let ff := (Localization.fullyFaithfulWhiskeringLeft (S.ι ⋙ DerivedCategory.Qh)
    ((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage S.ι) E).comp
      (CategoryTheory.fullyFaithfulWhiskeringOfFullEssSurj f E)
  exact ff.ofIso ((Functor.whiskeringLeft _ _ E).mapIso
    (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso A)))

namespace CategoryTheory.StrictReduction

private theorem genericModelExists
    {A : Type a} [Category.{b} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{t} (ℕᵒᵖ ⥤ A)]
    (Q : ℕᵒᵖ ⥤ A) (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q)
    (good : CochainComplex A ℤ → Prop)
    (res : ∀ K, ∃ (L : CochainComplex A ℤ) (p : L ⟶ K), good L ∧ QuasiIso p)
    (inverts : ∀ {P P' : CochainComplex A ℤ} (a : P ⟶ P'), QuasiIso a → good P → good P' →
      QuasiIso (((reduction Q).mapHomologicalComplex (.up ℤ)).map a)) :
    Nonempty (Model Q e good) := by
  obtain ⟨T, β, huni, hcomp⟩ := cochainDerivedExists (reduction Q)
    good res inverts
  let := huni
  let δ : DerivedCategory.Q ⋙ (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⟶
      (reduction Q).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight (NatTrans.mapHomologicalComplex (augmentation Q e) (.up ℤ))
        DerivedCategory.Q
  refine ⟨{ B := T
            counit := β
            universal := huni
            computes := ?_
            i := T.leftDerivedLift β (HomologicalComplex.quasiIso A (.up ℤ)) _ δ
            augmentation_eq := ?_ }⟩
  · exact hcomp
  · intro K _
    exact T.leftDerived_fac_app β (HomologicalComplex.quasiIso A (.up ℤ)) _ δ K

end CategoryTheory.StrictReduction

namespace CategoryTheory.StrictReduction

open CochainPullback


universe uC vC uD vD r dR dS dTY dTX

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}

/-- Exactly the flat-term K-flat representatives in the statement.
Source: Stacks 06YS (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def flatRepresentatives (R : Sheaf J CommRingCat.{r}) (P : Complex R) : Prop :=
  P.IsKFlatIndependentCoefficients ∧ ∀ n : ℤ, SheafOfModules.IsFlatOnSite (P.X n)

private theorem tensor_kflat_quasiIso
    {P P' N : Complex R} (a : P ⟶ P') (ha : QuasiIso a)
    (hP : P.IsKFlatIndependentCoefficients) (hP' : P'.IsKFlatIndependentCoefficients) :
    QuasiIso (HomologicalComplex.mapBifunctorMap a (𝟙 N)
      (curriedTensor (Modules R)) (.up ℤ)) := by
  obtain ⟨E, t, hE, _, ht, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) N
  let T := (curriedTensor (Modules R)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)
  have : QuasiIso ((T.map a).app E) := SheafOfModules.tensor_right_quasiIso a ha hE
  have : QuasiIso ((T.obj P).map t) := SheafOfModules.tensor_left_quasiIso t ht hP
  have : QuasiIso ((T.obj P').map t) := SheafOfModules.tensor_left_quasiIso t ht hP'
  have : QuasiIso ((T.obj P).map t ≫ (T.map a).app N) := by
    rw [(T.map a).naturality t]
    infer_instance
  exact quasiIso_of_comp_left ((T.obj P).map t) ((T.map a).app N)

private theorem fixedTensor_quasiIso
    {P P' : Complex R} (a : P ⟶ P') (ha : QuasiIso a)
    (hP : P.IsKFlatIndependentCoefficients) (hP' : P'.IsKFlatIndependentCoefficients)
    (N : Modules R) :
    QuasiIso (((tensorRight N).mapHomologicalComplex (.up ℤ)).map a) := by
  let N₀ := (HomologicalComplex.single (Modules R) (.up ℤ) 0).obj N
  let T := (curriedTensor (Modules R)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)
  let e := CochainComplex.map₂HomologicalComplexFlipObjSingleIso
    (curriedTensor (Modules R)) N
  have : QuasiIso ((T.map a).app N₀) := tensor_kflat_quasiIso a ha hP hP'
  have h := e.hom.naturality a
  change (T.map a).app N₀ ≫ e.hom.app P' =
    e.hom.app P ≫ ((tensorRight N).mapHomologicalComplex (.up ℤ)).map a at h
  have : QuasiIso (e.hom.app P ≫
      ((tensorRight N).mapHomologicalComplex (.up ℤ)).map a) := by
    rw [← h]
    infer_instance
  exact quasiIso_of_comp_left (e.hom.app P) _

private theorem resolves (P : Complex R) :
    ∃ (L : Complex R) (p : L ⟶ P), flatRepresentatives R L ∧ QuasiIso p := by
  obtain ⟨L, p, hL, hflat, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
  exact ⟨L, p, ⟨hL, fun n ↦ (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (L.X n)).symm (hflat n)⟩, hp⟩

private theorem reductionInverts (Q : ℕᵒᵖ ⥤ Modules R)
    {P P' : Complex R} (a : P ⟶ P') (ha : QuasiIso a)
    (hP : flatRepresentatives R P) (hP' : flatRepresentatives R P') :
    QuasiIso (((reduction Q).mapHomologicalComplex (.up ℤ)).map a) := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro n
  exact fixedTensor_quasiIso a ha hP.1 hP'.1 (Q.obj n)

private theorem pullbackGood (f : RingedPullback R S)
    (P : Complex R) (hP : flatRepresentatives R P) :
    flatRepresentatives S ((f.L.mapHomologicalComplex (.up ℤ)).obj P) := by
  let : PreservesFiniteLimits f.uInv := f.finiteLimits
  exact SheafOfModules.isKFlat_ringedToposPullback f.uInv f.uPush f.adj
    f.I f.coefficient f.L f.hobj f.hmap P hP.1 hP.2

variable [HasDerivedCategory.{dR} (Modules R)]
  [HasDerivedCategory.{dS} (Modules S)]
  [HasDerivedCategory.{dTY} (ℕᵒᵖ ⥤ Modules R)]
  [HasDerivedCategory.{dTX} (ℕᵒᵖ ⥤ Modules S)]

/-- The universal strict-tower reduction with its coefficient-unit augmentation.
Source: Stacks 06YY (blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
abbrev RingedModel (Q : ℕᵒᵖ ⥤ Modules R)
    (e : (Functor.const ℕᵒᵖ).obj (𝟙_ (Modules R)) ⟶ Q) :=
  Model Q e (flatRepresentatives R)

/-- Generator normalization of the inverse ordinary comparison. These are exactly the
scalar-extension-adjunction generators: the mate sends Fx tensor Fq to F(x tensor q).
The insertion maps k.q are fixed by k.q_one, not arbitrary maps of sheaves.
Source: Stacks 03CZ and 03EL
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower). -/
def IsInversePureNormalized (f : RingedPullback R S) (k : Comparison f)
    (M N : Modules R) (a : f.L.obj M ⊗ f.L.obj N ⟶ f.L.obj (M ⊗ N)) : Prop :=
  ∀ (Z : Sheaf J (Type r))
    (x : Z ⟶ (underlying R).obj M) (y : Z ⟶ (underlying R).obj N)
    (z : Z ⟶ (underlying R).obj (M ⊗ N)),
    (∀ (U : Cᵒᵖ) (t : Z.obj.obj U), z.hom.app U t =
      (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)).unit.app
            (M.val ⊗ N.val)).app U
              (x.hom.app U t ⊗ₜ[R.obj.obj U] y.hom.app U t))) →
    ∀ (V : Dᵒᵖ) (t : (f.uInv.obj Z).obj.obj V),
      a.val.app V
        ((SheafOfModules.tensorObjIsoSheafification (f.L.obj M) (f.L.obj N)).inv.val.app V
          (((PresheafOfModules.sheafificationAdjunction (𝟙
            ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)).unit.app
              ((f.L.obj M).val ⊗ (f.L.obj N).val)).app V
                ((f.uInv.map x ≫ f.I.moduleUnderlying.inv.app M ≫ k.q M).hom.app V t
                  ⊗ₜ[S.obj.obj V]
                  (f.uInv.map y ≫ f.I.moduleUnderlying.inv.app N ≫ k.q N).hom.app V t))) =
        (f.uInv.map z ≫ f.I.moduleUnderlying.inv.app (M ⊗ N) ≫ k.q (M ⊗ N)).hom.app V t

private theorem modelExists (Q : ℕᵒᵖ ⥤ Modules R)
    (e : (Functor.const ℕᵒᵖ).obj (𝟙_ (Modules R)) ⟶ Q) :
    Nonempty (RingedModel Q e) :=
  genericModelExists Q e (flatRepresentatives R) resolves (reductionInverts Q)

private noncomputable def representativeWhiskering
    (E : Type a) [Category.{b} E] :
    ((Functor.whiskeringLeft _ _ E).obj
      (ObjectProperty.ι (flatRepresentatives R) ⋙ DerivedCategory.Q)).FullyFaithful :=
  cochainRepresentativeWhiskering (flatRepresentatives R) resolves E

private theorem genericEvaluationUniversal
    {A : Type a} [Category.{b} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{t} (ℕᵒᵖ ⥤ A)]
    (good : CochainComplex A ℤ → Prop)
    (res : ∀ K, ∃ (L : CochainComplex A ℤ) (p : L ⟶ K), good L ∧ QuasiIso p)
    (Q : ℕᵒᵖ ⥤ A) (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q)
    (M : Model Q e good) (n : ℕ) :
    (M.B ⋙ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory).IsLeftDerivedFunctor
      (evaluationCounit Q e good M n)
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
  let H := ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory
  let rc := (reduction Q).mapHomologicalComplex (.up ℤ)
  let δ := (Functor.associator DerivedCategory.Q M.B H).inv ≫
    Functor.whiskerRight M.counit H
  have hδ := cochainCounitPostcompose (reduction Q) good res
    M.B M.counit M.universal M.computes H
  have : (M.B ⋙ H).IsRightKanExtension δ := hδ.isRightKanExtension
  let j : (rc ⋙ DerivedCategory.Q) ⋙ H ≅
      rc ⋙ ((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft rc
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors
  have h := Functor.kan_change_iso (M.B ⋙ H) (Iso.refl DerivedCategory.Q) j δ
  have heq : Functor.whiskerRight (Iso.refl DerivedCategory.Q).inv (M.B ⋙ H) ≫
      δ ≫ j.hom = evaluationCounit Q e good M n := by
    ext P
    simp [δ, j, evaluationCounit, H, rc]
  exact ⟨heq ▸ h⟩

private theorem evaluationUniversal
    (Q : ℕᵒᵖ ⥤ Modules R) (e : (Functor.const ℕᵒᵖ).obj (𝟙_ (Modules R)) ⟶ Q)
    (M : RingedModel Q e) (n : ℕ) :
    (M.B ⋙ ((evaluation ℕᵒᵖ (Modules R)).obj (op n)).mapDerivedCategory).IsLeftDerivedFunctor
      (evaluationCounit Q e (flatRepresentatives R) M n)
      (HomologicalComplex.quasiIso (Modules R) (.up ℤ)) :=
  genericEvaluationUniversal (flatRepresentatives R) resolves Q e M n

private theorem ordinaryAugmentationGeneric
    {A : Type a} [Category.{b} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A]
    {B : Type c} [Category.{d} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive B]
    (F : A ⥤ B) (mu : ∀ M N, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (hmu : ∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (mu M' N').hom =
        (mu M N).hom ≫ (F.map f ⊗ₘ F.map g))
    (j : F.obj (𝟙_ A) ≅ 𝟙_ B)
    (hu : ∀ M, (mu M (𝟙_ A)).hom ≫ F.obj M ◁ j.hom ≫
      (ρ_ (F.obj M)).hom = F.map (ρ_ M).hom)
    (Q : ℕᵒᵖ ⥤ A) (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q) :
    Functor.whiskerRight (augmentation Q e) (termwise F) ≫
        (ordinaryComparison F mu hmu Q).hom =
      (constantSquare F).hom ≫ Functor.whiskerLeft F
        (augmentation (Q ⋙ F) (pulledUnit F j Q e)) := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  change F.map ((ρ_ M).inv ≫ M ◁ e.app n) ≫ (mu M (Q.obj n)).hom =
    𝟙 _ ≫ (ρ_ (F.obj M)).inv ≫
      F.obj M ◁ (j.inv ≫ 𝟙 _ ≫ F.map (e.app n))
  simp only [Functor.map_comp, Category.assoc, Category.id_comp]
  rw [show F.map (M ◁ e.app n) ≫ (mu M (Q.obj n)).hom =
      (mu M (𝟙_ A)).hom ≫
        F.obj M ◁ F.map (e.app n) by
    simpa only [id_tensorHom, F.map_id] using hmu (M := M) (M' := M) (N := 𝟙_ A)
      (N' := Q.obj n) (𝟙 M) (e.app n)]
  have hunit : F.map (ρ_ M).inv ≫ (mu M (𝟙_ A)).hom =
      (ρ_ (F.obj M)).inv ≫ F.obj M ◁ j.inv := by
    apply (cancel_mono (F.obj M ◁ j.hom ≫
      (ρ_ (F.obj M)).hom)).1
    simp only [Category.assoc]
    rw [hu M, ← F.map_comp, Iso.inv_hom_id, F.map_id]
    simp [← MonoidalCategory.whiskerLeft_comp, ← Category.assoc]
  rw [← Category.assoc, hunit, Category.assoc, ← MonoidalCategory.whiskerLeft_comp]


private theorem constantDerivedSquare_fac
    {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type c} [Category.{d} B] [Abelian B] [HasDerivedCategory.{w'} B]
    [HasDerivedCategory.{t} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{t'} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (P : CochainComplex A ℤ) :
    (constantDerivedSquare F).hom.app (DerivedCategory.Q.obj P) ≫
        (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.map
          (F.mapDerivedCategoryFactors.hom.app P) ≫
        (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      (termwise F).mapDerivedCategory.map
        ((Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategoryFactors.hom.app P) ≫
        (termwise F).mapDerivedCategoryFactors.hom.app
          (((Functor.const ℕᵒᵖ : A ⥤ _).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (constantSquare F) (.up ℤ)).hom.app P) := by
  let CY := (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A)
  let CX := (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B)
  let : PreservesFiniteLimits (CY ⋙ termwise F) := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits (CY ⋙ termwise F) := comp_preservesFiniteColimits _ _
  let : PreservesFiniteLimits (F ⋙ CX) := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits (F ⋙ CX) := comp_preservesFiniteColimits _ _
  have h1 := Functor.mapDerivedCategoryCompIso_fac F CX P
  have hc1 : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ CX))
      (.up ℤ)).hom.app P = 𝟙 _ := rfl
  erw [hc1, DerivedCategory.Q.map_id, Category.comp_id] at h1
  have h2 := Functor.mapDerivedCategoryCompIso_fac CY (termwise F) P
  have hc2 : (Functor.mapHomologicalComplexCompIso (Iso.refl (CY ⋙ termwise F))
      (.up ℤ)).hom.app P = 𝟙 _ := rfl
  erw [hc2, DerivedCategory.Q.map_id, Category.comp_id] at h2
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso CY (termwise F)).hom.app
    (DerivedCategory.Q.obj P))).1
  dsimp only [CY, CX] at h1 h2 ⊢
  dsimp only [constantDerivedSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  erw [h1, Functor.mapDerivedCategoryNatIso_fac]
  erw [← h2]
  simp only [Category.assoc]
  rfl

private theorem comparisonGeneric
    {A : Type a} [Category.{b} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasDerivedCategory.{w} A]
    {B : Type c} [Category.{d} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive B] [HasDerivedCategory.{w'} B]
    [HasDerivedCategory.{t} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{t'} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (mu : ∀ M N, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (hmu : ∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (mu M' N').hom =
        (mu M N).hom ≫ (F.map f ⊗ₘ F.map g))
    (j : F.obj (𝟙_ A) ≅ 𝟙_ B)
    (goodA : CochainComplex A ℤ → Prop) (goodB : CochainComplex B ℤ → Prop)
    (hgood : ∀ P, goodA P → goodB ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (ff : ((Functor.whiskeringLeft _ _ (DerivedCategory (ℕᵒᵖ ⥤ B))).obj
      (ObjectProperty.ι goodA ⋙ DerivedCategory.Q)).FullyFaithful)
    (Q : ℕᵒᵖ ⥤ A) (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q)
    (MY : Model Q e goodA) (MX : Model (Q ⋙ F) (pulledUnit F j Q e) goodB) :
    ∃ tau : MY.B ⋙ (termwise F).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ MX.B,
      IsNormalized F Q e j goodA goodB
        MY MX mu hmu tau ∧
      ∀ tau', IsNormalized F Q e j
        goodA goodB MY MX mu hmu tau' →
          tau' = tau := by
  let P : ObjectProperty (CochainComplex A ℤ) := goodA
  let l := P.ι ⋙ DerivedCategory.Q
  let FD := F.mapDerivedCategory
  let FT := (termwise F).mapDerivedCategory
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let rc := (reduction Q).mapHomologicalComplex (.up ℤ)
  let rx := (reduction (Q ⋙ F)).mapHomologicalComplex (.up ℤ)
  let ord := NatIso.mapHomologicalComplex
    (ordinaryComparison F mu hmu Q) (.up ℤ)
  let a : l ⋙ (MY.B ⋙ FT) ⟶ P.ι ⋙ Fc ⋙ rx ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (Functor.whiskerLeft P.ι MY.counit) FT ≫
      Functor.whiskerLeft (P.ι ⋙ rc) (termwise F).mapDerivedCategoryFactors.hom ≫
      Functor.whiskerLeft P.ι (Functor.whiskerRight ord.hom DerivedCategory.Q)
  let b : l ⋙ (FD ⋙ MX.B) ⟶ P.ι ⋙ Fc ⋙ rx ⋙ DerivedCategory.Q :=
    Functor.whiskerLeft P.ι
      (Functor.whiskerRight F.mapDerivedCategoryFactors.hom MX.B ≫
        Functor.whiskerLeft Fc MX.counit)
  have ha (Y : P.FullSubcategory) : IsIso (a.app Y) := by
    have := MY.computes Y.obj Y.property
    dsimp [a]
    infer_instance
  have hb (Y : P.FullSubcategory) : IsIso (b.app Y) := by
    have := MX.computes (Fc.obj Y.obj) (hgood Y.obj Y.property)
    dsimp [b]
    infer_instance
  have : IsIso a := NatIso.isIso_of_isIso_app a
  have : IsIso b := NatIso.isIso_of_isIso_app b
  let tau := ff.preimageIso (asIso a ≪≫ (asIso b).symm)
  have heq : Functor.whiskerLeft l tau.hom ≫ b = a := by
    rw [show Functor.whiskerLeft l tau.hom =
      (asIso a ≪≫ (asIso b).symm).hom from ff.map_preimage _]
    simp
  refine ⟨tau, ?_, ?_⟩
  · intro K hK
    exact (NatTrans.congr_app heq ⟨K, hK⟩).symm
  · intro tau' h'
    apply Iso.ext
    apply ff.map_injective
    apply (cancel_mono b).1
    ext Y
    exact (h' Y.obj Y.property).symm.trans (NatTrans.congr_app heq Y).symm

private theorem comparisonExists
    (f : RingedPullback R S) [PreservesFiniteLimits f.L] [PreservesFiniteColimits f.L]
    (k : Comparison f) (Q : ℕᵒᵖ ⥤ Modules R)
    (e : (Functor.const ℕᵒᵖ).obj (𝟙_ (Modules R)) ⟶ Q)
    (MY : RingedModel Q e)
    (MX : RingedModel (Q ⋙ f.L) (pulledUnit f.L (moduleUnit f k) Q e)) :
    ∃ tau : MY.B ⋙ (termwise f.L).mapDerivedCategory ≅ f.L.mapDerivedCategory ⋙ MX.B,
      IsNormalized f.L Q e (moduleUnit f k) (flatRepresentatives R) (flatRepresentatives S)
        MY MX k.mu k.naturality tau ∧
      ∀ tau', IsNormalized f.L Q e (moduleUnit f k)
        (flatRepresentatives R) (flatRepresentatives S) MY MX k.mu k.naturality tau' →
          tau' = tau := by
  exact comparisonGeneric f.L k.mu k.naturality (moduleUnit f k)
    (flatRepresentatives R) (flatRepresentatives S) (pullbackGood f)
    (representativeWhiskering (R := R) _) Q e MY MX

private theorem augmentationGeneric
    {A : Type a} [Category.{b} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasDerivedCategory.{w} A]
    {B : Type c} [Category.{d} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive B] [HasDerivedCategory.{w'} B]
    [HasDerivedCategory.{t} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{t'} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (mu : ∀ M N, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (hmu : ∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (mu M' N').hom =
        (mu M N).hom ≫ (F.map f ⊗ₘ F.map g))
    (j : F.obj (𝟙_ A) ≅ 𝟙_ B)
    (goodA : CochainComplex A ℤ → Prop) (goodB : CochainComplex B ℤ → Prop)
    (hgood : ∀ P, goodA P → goodB ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (ff : ((Functor.whiskeringLeft _ _ (DerivedCategory (ℕᵒᵖ ⥤ B))).obj
      (ObjectProperty.ι goodA ⋙ DerivedCategory.Q)).FullyFaithful)
    (Q : ℕᵒᵖ ⥤ A) (e : (Functor.const ℕᵒᵖ).obj (𝟙_ A) ⟶ Q)
    (MY : Model Q e goodA) (MX : Model (Q ⋙ F) (pulledUnit F j Q e) goodB)
    (hu : ∀ M, (mu M (𝟙_ A)).hom ≫ F.obj M ◁ j.hom ≫
      (ρ_ (F.obj M)).hom = F.map (ρ_ M).hom)
    (tau : MY.B ⋙ (termwise F).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ MX.B)
    (hnorm : IsNormalized F Q e j
      goodA goodB MY MX mu hmu tau) :
    ∀ L, (termwise F).mapDerivedCategory.map (MY.i.app L) ≫ tau.hom.app L =
      (constantDerivedSquare F).hom.app L ≫ MX.i.app (F.mapDerivedCategory.obj L) := by
  let FT := (termwise F).mapDerivedCategory
  let Ftc := (termwise F).mapHomologicalComplex (.up ℤ)
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let CY := (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A)
  let CX := (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B)
  have heq : Functor.whiskerRight MY.i FT ≫ tau.hom =
      (constantDerivedSquare F).hom ≫ Functor.whiskerLeft F.mapDerivedCategory MX.i := by
    apply ff.map_injective
    ext Y
    let P := Y.obj
    have hP : goodA P := Y.property
    have hFP := hgood P hP
    let ay := (NatTrans.mapHomologicalComplex (augmentation Q e) (.up ℤ)).app P
    let ax := (NatTrans.mapHomologicalComplex
      (augmentation (Q ⋙ F) (pulledUnit F j Q e)) (.up ℤ)).app (Fc.obj P)
    let oc := (NatIso.mapHomologicalComplex
      (ordinaryComparison F mu hmu Q) (.up ℤ)).hom.app P
    let cc := (NatIso.mapHomologicalComplex (constantSquare F) (.up ℤ)).hom.app P
    let s := F.mapDerivedCategoryFactors.hom.app P
    let cy := MY.counit.app P
    let cx := MX.counit.app (Fc.obj P)
    have : IsIso cx := MX.computes (Fc.obj P) hFP
    have : IsIso (MX.B.map s ≫ cx) := by dsimp [s]; infer_instance
    have hN := hnorm P hP
    have hY := MY.augmentation_eq P hP
    have hX := MX.augmentation_eq (Fc.obj P) hFP
    have hOrd : Ftc.map ay ≫ oc = cc ≫ ax := by
      apply HomologicalComplex.Hom.ext
      funext i
      exact NatTrans.congr_app (ordinaryAugmentationGeneric F mu hmu j hu Q e) (P.X i)
    change FT.map (MY.i.app (DerivedCategory.Q.obj P)) ≫
        tau.hom.app (DerivedCategory.Q.obj P) =
      (constantDerivedSquare F).hom.app (DerivedCategory.Q.obj P) ≫
        MX.i.app (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P))
    apply (cancel_mono (MX.B.map s ≫ cx)).1
    calc
      _ = FT.map (MY.i.app (DerivedCategory.Q.obj P)) ≫
          (FT.map cy ≫ (termwise F).mapDerivedCategoryFactors.hom.app
            (((reduction Q).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map oc) := by
        rw [hN]
        simp only [Category.assoc]
        rfl
      _ = FT.map (MY.i.app (DerivedCategory.Q.obj P) ≫ cy) ≫
          (termwise F).mapDerivedCategoryFactors.hom.app
            (((reduction Q).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map oc := by rw [FT.map_comp]; simp [Category.assoc]
      _ = FT.map (CY.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map ay) ≫
          (termwise F).mapDerivedCategoryFactors.hom.app
            (((reduction Q).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map oc := by rw [hY]
      _ = FT.map (CY.mapDerivedCategoryFactors.hom.app P) ≫
          (termwise F).mapDerivedCategoryFactors.hom.app
            ((CY.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (Ftc.map ay ≫ oc) := by
        rw [FT.map_comp]
        simp only [Category.assoc]
        erw [(termwise F).mapDerivedCategoryFactors.hom.naturality_assoc ay]
        rw [DerivedCategory.Q.map_comp]
        rfl
      _ = FT.map (CY.mapDerivedCategoryFactors.hom.app P) ≫
          (termwise F).mapDerivedCategoryFactors.hom.app
            ((CY.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (cc ≫ ax) := by rw [hOrd]
      _ = (constantDerivedSquare F).hom.app (DerivedCategory.Q.obj P) ≫
          CX.mapDerivedCategory.map s ≫ CX.mapDerivedCategoryFactors.hom.app (Fc.obj P) ≫
          DerivedCategory.Q.map ax := by
        simpa only [Category.assoc, DerivedCategory.Q.map_comp] using
          congrArg (fun z ↦ z ≫ DerivedCategory.Q.map ax)
            (constantDerivedSquare_fac F P).symm
      _ = (constantDerivedSquare F).hom.app (DerivedCategory.Q.obj P) ≫
          CX.mapDerivedCategory.map s ≫ MX.i.app (DerivedCategory.Q.obj (Fc.obj P)) ≫ cx := by
        simpa only [Category.assoc] using congrArg (fun z ↦
          (constantDerivedSquare F).hom.app (DerivedCategory.Q.obj P) ≫
            CX.mapDerivedCategory.map s ≫ z) hX.symm
      _ = _ := by erw [← Category.assoc (CX.mapDerivedCategory.map s), MX.i.naturality s]
                  simp only [Category.assoc]
                  rfl
  intro L
  exact NatTrans.congr_app heq L

private theorem augmentationComparison
    (f : RingedPullback R S) [PreservesFiniteLimits f.L] [PreservesFiniteColimits f.L]
    (k : Comparison f) (Q : ℕᵒᵖ ⥤ Modules R)
    (e : (Functor.const ℕᵒᵖ).obj (𝟙_ (Modules R)) ⟶ Q)
    (MY : RingedModel Q e)
    (MX : RingedModel (Q ⋙ f.L) (pulledUnit f.L (moduleUnit f k) Q e))
    (tau : MY.B ⋙ (termwise f.L).mapDerivedCategory ≅ f.L.mapDerivedCategory ⋙ MX.B)
    (hnorm : IsNormalized f.L Q e (moduleUnit f k)
      (flatRepresentatives R) (flatRepresentatives S) MY MX k.mu k.naturality tau) :
    ∀ L, (termwise f.L).mapDerivedCategory.map (MY.i.app L) ≫ tau.hom.app L =
      (constantDerivedSquare f.L).hom.app L ≫ MX.i.app (f.L.mapDerivedCategory.obj L) := by
  apply augmentationGeneric f.L k.mu k.naturality (moduleUnit f k)
    (flatRepresentatives R) (flatRepresentatives S) (pullbackGood f)
    (representativeWhiskering (R := R) _) Q e MY MX _ tau hnorm
  intro M
  have h := (Classical.choose_spec
    (SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_unit
      R S f.RI f.uInv f.I f.coefficient f.L f.hobj f.hmap k)).1 M
  change (k.mu M (𝟙_ (Modules R))).hom ≫
    (𝟙 (f.L.obj M) ⊗ₘ (moduleUnit f k).hom) ≫ (ρ_ (f.L.obj M)).hom =
      f.L.map (ρ_ M).hom at h
  simpa only [id_tensorHom] using h

/-- Pullback of a strict tower of commutative algebras commutes uniquely with derived
reduction, normalized by the universal counits. The index n encodes the paper's n+1.
Source: Stacks 06YS, 06YY, 07A4 and 03EL
(blueprint: lem-weil-pbc-reduction-pullback-derived-tower).

Proof:
1. Resolve every complex by a flat-term K-flat complex. A quasi-isomorphism between
K-flat complexes remains a quasi-isomorphism after tensoring with any complex: resolve
that second complex by a K-flat one and use two-out-of-three on the tensor square.
Specializing the second complex to Q_n in degree zero identifies total tensor with
termwise tensor. Quasi-isomorphisms of tower complexes are detected by evaluation, so
strict reduction inverts quasi-isomorphisms between the chosen representatives.
2. Apply the resolving-class derived-functor criterion on homotopy categories, then
transfer its universal computing counit to complexes through the full homotopy quotient.
The universal property lifts the coefficient-unit augmentation to the derived reduction.
3. The supplied Comparison already contains the natural tensor isomorphism and its
pure-tensor equation. Apply its inverse to that equation to obtain inverse normalization.
The normalized moduleUnit and naturality in Q_n imply compatibility with augmentation.
4. Restriction from derived objects to good representatives is fully faithful: restrict
the homotopy localization to its resolving full subcategory and precompose with the full,
essentially surjective homotopy quotient. Pullback preserves the good representatives.
The ordinary comparison, conjugated by the two computing counits and exact-localization
factors, is therefore the restriction of a unique derived natural isomorphism.
5. Check the augmentation equation after restricting to good representatives and cancel
the invertible counit. Use ordinary augmentation compatibility, naturality of the exact
localization factors, and their composition and natural-isomorphism equations. Fully
faithful restriction proves the equation on every derived object.
6. The right Kan extension defining a computing counit is absolute: the resolving-class
criterion makes the associated pro-diagrams essentially constant. Postcompose with
exact derived evaluation and insert its localization factor. This is exactly the stated
evaluationCounit and proves its left-derived universal property for both models.
All transitions are retained by functors to the strict tower category. No flatness of
Q_n, perfection, boundedness, completeness or adic hypothesis is used. -/
theorem reductionPullbackDerivedTower
    (f : RingedPullback R S) [IsIso f.coefficient]
    [PreservesFiniteLimits f.L] [PreservesFiniteColimits f.L]
    (k : Comparison f) (Q : CommMon (ℕᵒᵖ ⥤ Modules R)) :
    (∀ (M : Modules R) (n : ℕ),
      IsInversePureNormalized f k M (Q.X.obj (op n)) (k.mu M (Q.X.obj (op n))).inv) ∧
    Nonempty (RingedModel Q.X (MonObj.one (X := Q.X))) ∧
    Nonempty (RingedModel (Q.X ⋙ f.L)
      (pulledUnit f.L (moduleUnit f k) Q.X (MonObj.one (X := Q.X)))) ∧
    ∀ (MY : RingedModel Q.X (MonObj.one (X := Q.X)))
      (MX : RingedModel (Q.X ⋙ f.L)
        (pulledUnit f.L (moduleUnit f k) Q.X (MonObj.one (X := Q.X)))),
      ∃ tau : MY.B ⋙ (termwise f.L).mapDerivedCategory ≅ f.L.mapDerivedCategory ⋙ MX.B,
        IsNormalized f.L Q.X (MonObj.one (X := Q.X)) (moduleUnit f k)
          (flatRepresentatives R) (flatRepresentatives S) MY MX k.mu k.naturality tau ∧
        (∀ tau' : MY.B ⋙ (termwise f.L).mapDerivedCategory ≅ f.L.mapDerivedCategory ⋙ MX.B,
          IsNormalized f.L Q.X (MonObj.one (X := Q.X)) (moduleUnit f k)
            (flatRepresentatives R) (flatRepresentatives S) MY MX k.mu k.naturality tau' →
          tau' = tau) ∧
        (∀ L : DerivedCategory (Modules R),
          (termwise f.L).mapDerivedCategory.map (MY.i.app L) ≫ tau.hom.app L =
            (constantDerivedSquare f.L).hom.app L ≫ MX.i.app (f.L.mapDerivedCategory.obj L)) ∧
        (∀ n : ℕ,
          (MY.B ⋙ ((evaluation ℕᵒᵖ (Modules R)).obj (op n)).mapDerivedCategory).IsLeftDerivedFunctor
            (evaluationCounit Q.X (MonObj.one (X := Q.X))
              (flatRepresentatives R) MY n)
                (HomologicalComplex.quasiIso (Modules R) (.up ℤ))) ∧
        (∀ n : ℕ,
          (MX.B ⋙ ((evaluation ℕᵒᵖ (Modules S)).obj (op n)).mapDerivedCategory).IsLeftDerivedFunctor
            (evaluationCounit (Q.X ⋙ f.L)
              (pulledUnit f.L (moduleUnit f k) Q.X (MonObj.one (X := Q.X)))
              (flatRepresentatives S) MX n)
                (HomologicalComplex.quasiIso (Modules S) (.up ℤ)))  := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M n Z x y z hz V t
    have h := k.pure M (Q.X.obj (op n)) Z x y z hz V t
    change (k.mu M (Q.X.obj (op n))).hom.val.app V
      ((f.uInv.map z ≫ f.I.moduleUnderlying.inv.app (M ⊗ Q.X.obj (op n)) ≫
        k.q (M ⊗ Q.X.obj (op n))).hom.app V t) = _ at h
    rw [← h]
    exact congrArg (fun a ↦ a.val.app V
      ((f.uInv.map z ≫ f.I.moduleUnderlying.inv.app (M ⊗ Q.X.obj (op n)) ≫
        k.q (M ⊗ Q.X.obj (op n))).hom.app V t))
      (k.mu M (Q.X.obj (op n))).hom_inv_id
  · exact modelExists _ _
  · exact modelExists _ _
  · intro MY MX
    obtain ⟨tau, hnorm, huniq⟩ := comparisonExists f k Q.X (MonObj.one (X := Q.X)) MY MX
    refine ⟨tau, hnorm, huniq, ?_, ?_, ?_⟩
    · exact augmentationComparison f k Q.X (MonObj.one (X := Q.X)) MY MX tau hnorm
    · exact evaluationUniversal _ _ MY
    · exact evaluationUniversal _ _ MX

end CategoryTheory.StrictReduction
