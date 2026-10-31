/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.FiniteStagePairCategory
public import WeilConjectures.CategoryTheory.StageSystem.Triangulated
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
import WeilConjectures.CategoryTheory.Triangulated.TExactTruncationComparison
import WeilConjectures.CategoryTheory.Triangulated.CohomologyComparisonPasting

/-! # Descent of t-exact coefficient families

Source: the abstract transport argument in the DAG, Steps 1--10; Bhatt--Scholze,
Proposition 6.8.14(1)--(2) and Remark 6.8.15 give its coefficient context, rather than
stating this abstract lemma. Canonical comparisons use BBD, Proposition 1.3.3,
Theorem 1.3.6 and Proposition 1.3.17
(blueprint: lem-a1-texact-coefficient-stage-descent).

The structures below package the hypotheses and conclusions of this single lemma.
They use the existing raw tensor-Hom localization and the existing StageSystem quotient.
In particular no Karoubi completion or faithful-transition hypothesis is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe r w u v u' v' u'' v'' u''' v'''

namespace CategoryTheory.CoefficientStageDescent

open Limits Pretriangulated Triangulated TensorProduct TStructure

section Comparisons

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D]

/-- The cohomology convention in the statement, with values in the ambient category.
Source: BBD 1.3.6; DAG Step 9
(blueprint: lem-a1-texact-coefficient-stage-descent). -/
def cohomology (t : TStructure C) (j : ℤ) : C ⥤ C :=
  t.truncLT (j + 1) ⋙ t.truncGE j ⋙ shiftFunctor C j

/-- The actual restriction to the heart, on both objects and arrows.
Source: BBD 1.3.17(i); DAG Step 6
(blueprint: lem-a1-texact-coefficient-stage-descent). -/
def heartRestriction (tC : TStructure C) (tD : TStructure D) (F : C ⥤ D)
    (h : ∀ X : C, tC.heart X → tD.heart (F.obj X)) :
    tC.heart.FullSubcategory ⥤ tD.heart.FullSubcategory :=
  tD.heart.lift (tC.heart.ι ⋙ F) (fun X ↦ h X.obj X.property)

/-- All the individual-functor conclusions, including uniqueness and the specified
cohomology composite. Source: BBD 1.3.3, 1.3.6, 1.3.17; DAG Steps 6--9
(blueprint: lem-a1-texact-coefficient-stage-descent). -/
structure Comparisons (tC : TStructure C) (tD : TStructure D)
    (F : C ⥤ D) [F.CommShift ℤ] where
  /-- Preservation of distinguished triangles with the specified shift. -/
  exact : F.IsTriangulated
  /-- Preservation of both halves at every integer. -/
  tExact : F.IsTExact tC tD
  /-- The heart is preserved on objects. -/
  heart : ∀ X : C, tC.heart X → tD.heart (F.obj X)
  /-- Additivity of the restriction. -/
  heartAdditive : (heartRestriction tC tD F heart).Additive
  /-- Every short exact sequence in the heart remains short exact. -/
  heartExact : ∀ S : ShortComplex tC.heart.FullSubcategory,
    S.ShortExact → (S.map (heartRestriction tC tD F heart)).ShortExact
  /-- Comparison for the upper truncation. -/
  le : ∀ m : ℤ, tC.truncLT (m + 1) ⋙ F ≅ F ⋙ tD.truncLT (m + 1)
  /-- Comparison for the lower truncation. -/
  ge : ∀ m : ℤ, tC.truncGE m ⋙ F ≅ F ⋙ tD.truncGE m
  /-- Normalization by the canonical counit. -/
  le_counit : ∀ (m : ℤ) (X : C),
    (le m).hom.app X ≫ (tD.truncLTι (m + 1)).app (F.obj X) =
      F.map ((tC.truncLTι (m + 1)).app X)
  /-- Normalization by the canonical unit. -/
  ge_unit : ∀ (m : ℤ) (X : C),
    F.map ((tC.truncGEπ m).app X) ≫ (ge m).hom.app X =
      (tD.truncGEπ m).app (F.obj X)
  /-- The upper comparison is uniquely determined by that normalization. -/
  le_unique : ∀ (m : ℤ) (a : tC.truncLT (m + 1) ⋙ F ≅ F ⋙ tD.truncLT (m + 1)),
    (∀ X : C, a.hom.app X ≫ (tD.truncLTι (m + 1)).app (F.obj X) =
      F.map ((tC.truncLTι (m + 1)).app X)) → a = le m
  /-- The lower comparison is uniquely determined by that normalization. -/
  ge_unique : ∀ (m : ℤ) (a : tC.truncGE m ⋙ F ≅ F ⋙ tD.truncGE m),
    (∀ X : C, F.map ((tC.truncGEπ m).app X) ≫ a.hom.app X =
      (tD.truncGEπ m).app (F.obj X)) → a = ge m
  /-- Cohomology comparison as a natural isomorphism. -/
  q : ∀ j : ℤ, cohomology tC j ⋙ F ≅ F ⋙ cohomology tD j
  /-- Its exact formula, including the integer shift comparison (also for negative j). -/
  q_formula : ∀ (j : ℤ) (X : C),
    (q j).hom.app X =
      (F.commShiftIso j).hom.app ((tC.truncGE j).obj ((tC.truncLT (j + 1)).obj X)) ≫
        (shiftFunctor D j).map ((ge j).hom.app ((tC.truncLT (j + 1)).obj X)) ≫
        (shiftFunctor D j).map ((tD.truncGE j).map ((le j).hom.app X))

/-- Finite-stage computation includes the canonical maps, not just objectwise
isomorphisms. Source: the pair-category hypothesis and DAG Step 10
(blueprint: lem-a1-texact-coefficient-stage-descent). -/
def TruncationsComputedAt (tC : TStructure C) (tD : TStructure D) (J : C ⥤ D) : Prop :=
  ∀ m : ℤ, ∃ (a : tC.truncLT (m + 1) ⋙ J ≅ J ⋙ tD.truncLT (m + 1))
    (b : tC.truncGE m ⋙ J ≅ J ⋙ tD.truncGE m),
    (∀ X : C, a.hom.app X ≫ (tD.truncLTι (m + 1)).app (J.obj X) =
      J.map ((tC.truncLTι (m + 1)).app X)) ∧
    (∀ X : C, J.map ((tC.truncGEπ m).app X) ≫ b.hom.app X =
      (tD.truncGEπ m).app (J.obj X))


omit [IsTriangulated C] [IsTriangulated D] in
private theorem preservesHeart (tC : TStructure C) (tD : TStructure D)
    (F : C ⥤ D) [F.IsTExact tC tD] (X : C) (hX : tC.heart X) :
    tD.heart (F.obj X) := by
  obtain ⟨hLE, hGE⟩ := (tC.mem_heart_iff X).1 hX
  exact (tD.mem_heart_iff _).2
    ⟨Functor.IsTExact.isLE_obj tC tD F X 0, Functor.IsTExact.isGE_obj tC tD F X 0⟩

private instance restrictionAdditive (tC : TStructure C) (tD : TStructure D)
    (F : C ⥤ D) [F.Additive] (h : ∀ X, tC.heart X → tD.heart (F.obj X)) :
    (heartRestriction tC tD F h).Additive where
  map_add := by
    intro X Y f g
    apply (tD.heart.ι).map_injective
    exact F.map_add

private theorem restrictionExact (tC : TStructure C) (tD : TStructure D)
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tC tD]
    (S : ShortComplex tC.heart.FullSubcategory) (hS : S.ShortExact) :
    (S.map (heartRestriction tC tD F (preservesHeart tC tD F))).ShortExact := by
  let := tC.hasHeartFullSubcategory
  let := tD.hasHeartFullSubcategory
  obtain ⟨δ, hδ⟩ := (tC.shortExact_iff_exists_distTriang S).1 hS
  apply (tD.shortExact_iff_exists_distTriang _).2
  exact ⟨F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app _, F.map_distinguished _ hδ⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private def canonicalComparisons (tC : TStructure C) (tD : TStructure D)
    (hC : tC.bounded = ⊤) (hD : tD.bounded = ⊤)
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tC tD] :
    Comparisons tC tD F where
  exact := inferInstance
  tExact := inferInstance
  heart := preservesHeart tC tD F
  heartAdditive := inferInstance
  heartExact := restrictionExact tC tD F
  le m := F.eTruncLTIso tC tD (m + 1 : ℤ)
  ge m := F.eTruncGEIso tC tD m
  le_counit m X := F.eTruncLTIsoApp_hom_eTruncLTι_app tC tD (m + 1 : ℤ) X
  ge_unit m X := F.eTruncGEπ_app_eTruncGEIsoApp_hom tC tD m X
  le_unique m := (texact_truncation_comparison.{u, v, u', v', u', v'} tC tD hC hD F m).2.1
  ge_unique m := (texact_truncation_comparison.{u, v, u', v', u', v'} tC tD hC hD F m).2.2.1
  q j := truncationCohomologyComparison tC tD F j
  q_formula j X := by
    simpa only [Functor.map_comp, TStructure.truncLE, Category.assoc,
      TStructure.truncGELE, Functor.comp_obj, cohomology] using
      (cohomology_comparison_pasting tC tD F hC hD j X).2.2.2

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [IsTriangulated C] [IsTriangulated D] in
private theorem tExactOfZero (tC : TStructure C) (tD : TStructure D)
    (F : C ⥤ D) [F.CommShift ℤ]
    (hLE : ∀ X, tC.le 0 X → tD.le 0 (F.obj X))
    (hGE : ∀ X, tC.ge 0 X → tD.ge 0 (F.obj X)) : F.IsTExact tC tD := by
  constructor
  · intro X n hX
    have : tD.IsLE (F.obj (X⟦n⟧)) 0 :=
      ⟨hLE _ (tC.le_shift n n 0 (add_zero n) X (tC.le_of_isLE X n))⟩
    have : tD.IsLE ((F.obj X)⟦n⟧) 0 :=
      tD.isLE_of_iso
        (show F.obj (X⟦n⟧) ≅ (F.obj X)⟦n⟧ from (F.commShiftIso n).app X) 0
    exact tD.isLE_of_shift (F.obj X) n n 0
  · intro X n hX
    have : tD.IsGE (F.obj (X⟦n⟧)) 0 :=
      ⟨hGE _ (tC.ge_shift n n 0 (add_zero n) X (tC.ge_of_isGE X n))⟩
    have : tD.IsGE ((F.obj X)⟦n⟧) 0 :=
      tD.isGE_of_iso
        (show F.obj (X⟦n⟧) ≅ (F.obj X)⟦n⟧ from (F.commShiftIso n).app X) 0
    exact tD.isGE_of_shift (F.obj X) n n 0

end Comparisons

section Localization

variable (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear R C] (p : R)
  [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
  [HasZeroObject (ScalarLocalization R C p)] [HasShift (ScalarLocalization R C p) ℤ]
  [∀ n : ℤ, (shiftFunctor (ScalarLocalization R C p) n).Additive]
  [Pretriangulated (ScalarLocalization R C p)] [IsTriangulated (ScalarLocalization R C p)]
  [(ScalarLocalization.localization R C p).CommShift ℤ]

/-- The stipulated triangulation and the isomorphism closures of the two integral halves.
Source: DAG hypotheses and Step 2; BBD 1.3.16
(blueprint: lem-a1-texact-coefficient-stage-descent). -/
def IsLocalizedTStructure (t₀ : TStructure C)
    (t : TStructure (ScalarLocalization R C p)) : Prop :=
  (∀ Δ : Triangle (ScalarLocalization R C p), Δ ∈ distTriang _ ↔
    ∃ Δ₀ : Triangle C, Δ₀ ∈ distTriang C ∧
      Nonempty (Δ ≅ (ScalarLocalization.localization R C p).mapTriangle.obj Δ₀)) ∧
  (∀ X : ScalarLocalization R C p, t.le 0 X ↔
    ∃ X₀ : C, t₀.le 0 X₀ ∧ Nonempty (X ≅ (ScalarLocalization.localization R C p).obj X₀)) ∧
  (∀ X : ScalarLocalization R C p, t.ge 0 X ↔
    ∃ X₀ : C, t₀.ge 0 X₀ ∧ Nonempty (X ≅ (ScalarLocalization.localization R C p).obj X₀))

variable {R C p}
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear R D]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D]
  [HasZeroObject (ScalarLocalization R D p)] [HasShift (ScalarLocalization R D p) ℤ]
  [∀ n : ℤ, (shiftFunctor (ScalarLocalization R D p) n).Additive]
  [Pretriangulated (ScalarLocalization R D p)] [IsTriangulated (ScalarLocalization R D p)]
  [(ScalarLocalization.localization R D p).CommShift ℤ]

/-- Being the additive extension on fractions with the localized integral shift comparison.
The component condition fixes the factorization to the identity on the unchanged objects.
Source: DAG Step 1, tensor base change of Hom maps
(blueprint: lem-a1-texact-coefficient-stage-descent). -/
structure FractionExtension (F₀ : C ⥤ D) [F₀.Additive] [F₀.Linear R] [F₀.CommShift ℤ]
    (F : ScalarLocalization R C p ⥤ ScalarLocalization R D p) [F.CommShift ℤ] where
  /-- Identity on the specified images of objects. -/
  obj : ∀ X : C, F.obj ⟨X⟩ = ⟨F₀.obj X⟩
  /-- The Hom map is the base change of the integral Hom map. -/
  map : ∀ (X Y : C) (f : X ⟶ Y) (a : Localization.Away p),
    HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := p) X ⟶ ⟨Y⟩))
      (a ⊗ₜ[R] F₀.map f)
  /-- The identity-on-objects localization comparison. -/
  factor : ScalarLocalization.localization R C p ⋙ F ≅
    F₀ ⋙ ScalarLocalization.localization R D p
  /-- Its components are the identity, with dependent endpoints transported by obj. -/
  factor_id : ∀ X : C,
    HEq (factor.hom.app X) (𝟙 (ScalarLocalization.mk (R := R) (p := p) (F₀.obj X)))
  /-- This states precisely that the supplied rational shift comparison is the localized one. -/
  factor_shift : NatTrans.CommShift factor.hom ℤ

omit [IsTriangulated C] [IsTriangulated D]
  [IsTriangulated (ScalarLocalization R C p)]
  [IsTriangulated (ScalarLocalization R D p)] in
private theorem localizedExact (t₀ : TStructure C)
    (t : TStructure (ScalarLocalization R C p))
    (s₀ : TStructure D) (s : TStructure (ScalarLocalization R D p))
    (hC : IsLocalizedTStructure R C p t₀ t)
    (hD : IsLocalizedTStructure R D p s₀ s)
    (F₀ : C ⥤ D) [F₀.Additive] [F₀.Linear R] [F₀.CommShift ℤ] [F₀.IsTriangulated]
    (F : ScalarLocalization R C p ⥤ ScalarLocalization R D p) [F.CommShift ℤ]
    (hF : FractionExtension F₀ F) : F.IsTriangulated := by
  let Q := ScalarLocalization.localization R C p
  let P := ScalarLocalization.localization R D p
  have : P.IsTriangulated := ⟨fun T hT ↦ (hD.1 _).2 ⟨T, hT, ⟨Iso.refl _⟩⟩⟩
  have := hF.factor_shift
  have : (Q ⋙ F).IsTriangulated :=
    (Functor.isTriangulated_iff_of_iso hF.factor).2 inferInstance
  constructor
  intro T hT
  obtain ⟨T₀, hT₀, ⟨e⟩⟩ := (hC.1 T).1 hT
  exact isomorphic_distinguished _ ((Q ⋙ F).map_distinguished T₀ hT₀) _
    (F.mapTriangle.mapIso e ≪≫ (Functor.mapTriangleCompIso Q F).symm.app T₀)

omit [IsTriangulated C] [IsTriangulated D] in
omit [IsTriangulated (ScalarLocalization R C p)]
  [IsTriangulated (ScalarLocalization R D p)] in
private theorem localizedTExact (t₀ : TStructure C)
    (t : TStructure (ScalarLocalization R C p))
    (s₀ : TStructure D) (s : TStructure (ScalarLocalization R D p))
    (hC : IsLocalizedTStructure R C p t₀ t)
    (hD : IsLocalizedTStructure R D p s₀ s)
    (F₀ : C ⥤ D) [F₀.Additive] [F₀.Linear R] [F₀.CommShift ℤ]
    (F : ScalarLocalization R C p ⥤ ScalarLocalization R D p) [F.CommShift ℤ]
    (hF : FractionExtension F₀ F)
    (hLE : ∀ X, t₀.le 0 X → s₀.le 0 (F₀.obj X))
    (hGE : ∀ X, t₀.ge 0 X → s₀.ge 0 (F₀.obj X)) : F.IsTExact t s := by
  apply tExactOfZero
  · intro X hX
    obtain ⟨X₀, hX₀, ⟨e⟩⟩ := (hC.2.1 X).1 hX
    exact (hD.2.1 _).2 ⟨F₀.obj X₀, hLE X₀ hX₀,
      ⟨F.mapIso e ≪≫ hF.factor.app X₀⟩⟩
  · intro X hX
    obtain ⟨X₀, hX₀, ⟨e⟩⟩ := (hC.2.2 X).1 hX
    exact (hD.2.2 _).2 ⟨F₀.obj X₀, hGE X₀ hX₀,
      ⟨F.mapIso e ≪≫ hF.factor.app X₀⟩⟩

end Localization

section Coherence

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D]
  {B : Type u''} [Category.{v''} B] [Preadditive B] [HasZeroObject B]
  [HasShift B ℤ] [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
  [IsTriangulated B]
  {A : Type u'''} [Category.{v'''} A] [Preadditive A] [HasZeroObject A]
  [HasShift A ℤ] [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
  [IsTriangulated A]

/-- The comparison for successive functors is the composite comparison, transported
by the supplied tower isomorphism. The third equation is its cohomology version.
Source: BBD 1.3.3; DAG Steps 8--10
(blueprint: lem-a1-texact-coefficient-stage-descent). -/
def CompositeCompatible {tC : TStructure C} {tD : TStructure D} {tB : TStructure B}
    {F : C ⥤ D} [F.CommShift ℤ] {G : D ⥤ B} [G.CommShift ℤ]
    {H : C ⥤ B} [H.CommShift ℤ]
    (cF : Comparisons tC tD F) (cG : Comparisons tD tB G)
    (cH : Comparisons tC tB H) (η : F ⋙ G ≅ H) : Prop :=
  (∀ (m : ℤ) (X : C),
    η.hom.app ((tC.truncLT (m + 1)).obj X) ≫ (cH.le m).hom.app X =
      G.map ((cF.le m).hom.app X) ≫ (cG.le m).hom.app (F.obj X) ≫
        (tB.truncLT (m + 1)).map (η.hom.app X)) ∧
  (∀ (m : ℤ) (X : C),
    η.hom.app ((tC.truncGE m).obj X) ≫ (cH.ge m).hom.app X =
      G.map ((cF.ge m).hom.app X) ≫ (cG.ge m).hom.app (F.obj X) ≫
        (tB.truncGE m).map (η.hom.app X)) ∧
  (∀ (j : ℤ) (X : C),
    η.hom.app ((cohomology tC j).obj X) ≫ (cH.q j).hom.app X =
      G.map ((cF.q j).hom.app X) ≫ (cG.q j).hom.app (F.obj X) ≫
        (cohomology tB j).map (η.hom.app X))

/-- The explicit beta square for either truncation and for cohomology. This is also
used for the stage-inclusion square, so its equation specifies finite-stage representation.
Source: DAG Steps 8--10, BBD 1.3.3
(blueprint: lem-a1-texact-coefficient-stage-descent). -/
def SquareCompatible {tC : TStructure C} {tD : TStructure D}
    {tB : TStructure B} {tA : TStructure A}
    {F : C ⥤ D} [F.CommShift ℤ] {G : B ⥤ A} [G.CommShift ℤ]
    {U : C ⥤ B} [U.CommShift ℤ] {V : D ⥤ A} [V.CommShift ℤ]
    (cF : Comparisons tC tD F) (cG : Comparisons tB tA G)
    (cU : Comparisons tC tB U) (cV : Comparisons tD tA V)
    (η : F ⋙ V ≅ U ⋙ G) : Prop :=
  (∀ (m : ℤ) (X : C),
    η.hom.app ((tC.truncLT (m + 1)).obj X) ≫
        G.map ((cU.le m).hom.app X) ≫ (cG.le m).hom.app (U.obj X) =
      V.map ((cF.le m).hom.app X) ≫ (cV.le m).hom.app (F.obj X) ≫
        (tA.truncLT (m + 1)).map (η.hom.app X)) ∧
  (∀ (m : ℤ) (X : C),
    η.hom.app ((tC.truncGE m).obj X) ≫
        G.map ((cU.ge m).hom.app X) ≫ (cG.ge m).hom.app (U.obj X) =
      V.map ((cF.ge m).hom.app X) ≫ (cV.ge m).hom.app (F.obj X) ≫
        (tA.truncGE m).map (η.hom.app X)) ∧
  (∀ (j : ℤ) (X : C),
    η.hom.app ((cohomology tC j).obj X) ≫
        G.map ((cU.q j).hom.app X) ≫ (cG.q j).hom.app (U.obj X) =
      V.map ((cF.q j).hom.app X) ≫ (cV.q j).hom.app (F.obj X) ≫
        (cohomology tA j).map (η.hom.app X))


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem canonicalSquare
    (tC : TStructure C) (tD : TStructure D) (tB : TStructure B) (tA : TStructure A)
    (hC : tC.bounded = ⊤) (hD : tD.bounded = ⊤)
    (hB : tB.bounded = ⊤) (hA : tA.bounded = ⊤)
    (F : C ⥤ D) (G : B ⥤ A) (U : C ⥤ B) (V : D ⥤ A)
    [F.CommShift ℤ] [G.CommShift ℤ] [U.CommShift ℤ] [V.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated] [U.IsTriangulated] [V.IsTriangulated]
    [F.IsTExact tC tD] [G.IsTExact tB tA] [U.IsTExact tC tB] [V.IsTExact tD tA]
    (η : F ⋙ V ≅ U ⋙ G) [NatTrans.CommShift η.hom ℤ] :
    SquareCompatible (canonicalComparisons tC tD hC hD F)
      (canonicalComparisons tB tA hB hA G) (canonicalComparisons tC tB hC hB U)
      (canonicalComparisons tD tA hD hA V) η := by
  refine ⟨?_, ?_, ?_⟩
  · intro m X
    exact (truncationCohomologyComparison_square tC tD F hC hD tB tA
      hB hA U V G η m m X).1
  · intro m X
    exact (truncationCohomologyComparison_square tC tD F hC hD tB tA
      hB hA U V G η m m X).2.1
  · intro j X
    exact (truncationCohomologyComparison_square tC tD F hC hD tB tA
      hB hA U V G η j j X).2.2

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem canonicalComposite
    (tC : TStructure C) (tD : TStructure D) (tB : TStructure B)
    (hC : tC.bounded = ⊤) (hD : tD.bounded = ⊤) (hB : tB.bounded = ⊤)
    (F : C ⥤ D) (G : D ⥤ B) (H : C ⥤ B)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated] [H.IsTriangulated]
    [F.IsTExact tC tD] [G.IsTExact tD tB] [H.IsTExact tC tB]
    (η : F ⋙ G ≅ H) [NatTrans.CommShift η.hom ℤ] :
    CompositeCompatible (canonicalComparisons tC tD hC hD F)
      (canonicalComparisons tD tB hD hB G) (canonicalComparisons tC tB hC hB H) η := by
  let := cohomologyComparison_compTExact tC tD tB F G
  have hc (m : ℤ) (X : C) :=
    (texact_truncation_comparison tC tD hC hD F m).2.2.2.2.2 B tB hB G
      ((F ⋙ G).eTruncLTIso tC tB (m + 1 : ℤ))
      ((F ⋙ G).eTruncGEIso tC tB m)
      (fun Y ↦ (F ⋙ G).eTruncLTIsoApp_hom_eTruncLTι_app tC tB (m + 1 : ℤ) Y)
      (fun Y ↦ (F ⋙ G).eTruncGEπ_app_eTruncGEIsoApp_hom tC tB m Y) X
  refine ⟨?_, ?_, ?_⟩
  · intro m X
    have hn := (texact_truncation_comparison.{u, v, u'', v'', u'', v''}
      tC tB hC hB (F ⋙ G) m).2.2.2.1
      H η.hom X
    simpa only [(hc m X).1, Category.assoc, canonicalComparisons] using hn.1
  · intro m X
    have hn := (texact_truncation_comparison.{u, v, u'', v'', u'', v''}
      tC tB hC hB (F ⋙ G) m).2.2.2.1
      H η.hom X
    simpa only [(hc m X).2, Category.assoc, canonicalComparisons] using hn.2
  · intro j X
    simpa only [truncationCohomologyComparison_comp tC tD F hC hD tB hB G,
      Category.assoc, canonicalComparisons, cohomology, TStructure.truncGELE,
      TStructure.truncLE, Functor.comp_obj, Functor.comp_map] using
      truncationCohomologyComparison_naturality tC tB (F ⋙ G) hC hB H η.hom j X

end Coherence


open StageSystem StageSystem.Morphism

section
variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)]
  {S : StageSystem C} {S' : StageSystem D}

section StageShift
variable [∀ i, HasShift (C i) ℤ] [∀ i, HasShift (D i) ℤ]
  [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ {i j : I} (h : i ≤ j), (S'.T h).CommShift ℤ]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
    NatTrans.CommShift (S.assoc h h').hom ℤ]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
    NatTrans.CommShift (S'.assoc h h').hom ℤ]
  (F : StageSystem.Morphism S S') [∀ i, (F.Φ i).CommShift ℤ]
  (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ)

private def shiftHom (n : ℤ) : Hom
    ((S.shiftMorphism ℤ n).comp F) (F.comp (S'.shiftMorphism ℤ n)) where
  τ i := ((F.Φ i).commShiftIso n).hom
  comm {i j} h K := by
    have := hβ h
    simpa [Morphism.comp, StageSystem.shiftMorphism, Functor.commShiftIso_comp_hom_app,
      Category.assoc] using (NatTrans.shift_app_comm (F.β h).hom n K)

private def shiftIso (n : ℤ) :
    (shiftFunctor S.PairCategory n) ⋙ F.functor ≅ F.functor ⋙ (shiftFunctor S'.PairCategory n) :=
  (functorCompIso (S.shiftMorphism ℤ n) F).symm ≪≫
    NatIso.ofComponents
      (F := ((S.shiftMorphism ℤ n).comp F).functor)
      (G := (F.comp (S'.shiftMorphism ℤ n)).functor)
      (fun K ↦ (S'.ι K.stage).mapIso (((F.Φ K.stage).commShiftIso n).app K.obj))
      (fun f ↦ (descNatTrans (shiftHom F hβ n)).naturality f) ≪≫
    functorCompIso F (S'.shiftMorphism ℤ n)

end StageShift

section ExactShift
variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)]
  {S : StageSystem C} {S' : StageSystem D}
  [∀ i, HasShift (C i) ℤ] [∀ i, HasShift (D i) ℤ]
  [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ {i j : I} (h : i ≤ j), (S'.T h).CommShift ℤ]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
    NatTrans.CommShift (S.assoc h h').hom ℤ]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
    NatTrans.CommShift (S'.assoc h h').hom ℤ]
  (F : StageSystem.Morphism S S') [∀ i, (F.Φ i).CommShift ℤ]
  (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem shiftIso_hom_app (n : ℤ) (K : S.PairCategory) :
    (shiftIso F hβ n).hom.app K =
      (S'.ι K.stage).map (((F.Φ K.stage).commShiftIso n).hom.app K.obj) := by
  simp only [shiftIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Morphism.functorCompIso_inv_app, Morphism.functorCompIso_hom_app,
    NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.app_hom,
    Category.comp_id]
  erw [Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible] private def descendedCommShift : F.functor.CommShift ℤ where
  commShiftIso := shiftIso F hβ
  commShiftIso_zero := by
    ext K
    simp only [shiftIso_hom_app, Functor.CommShift.isoZero_hom_app]
    change (S'.ι K.stage).map (((F.Φ K.stage).commShiftIso (0 : ℤ)).hom.app K.obj) =
      F.functor.map ((S.ι K.stage).map
        ((shiftFunctorZero (C K.stage) ℤ).hom.app K.obj)) ≫
      (S'.ι K.stage).map
        ((shiftFunctorZero (D K.stage) ℤ).inv.app ((F.Φ K.stage).obj K.obj))
    erw [Morphism.functor_map_ι]
    simpa only [Functor.CommShift.isoZero_hom_app, Functor.map_comp] using
      congrArg ((S'.ι K.stage).map)
      (congr_app (congrArg Iso.hom ((F.Φ K.stage).commShiftIso_zero ℤ)) K.obj)
  commShiftIso_add n m := by
    ext K
    simp only [Functor.CommShift.isoAdd_hom_app, shiftIso_hom_app]
    change (S'.ι K.stage).map
        (((F.Φ K.stage).commShiftIso (n + m)).hom.app K.obj) =
      F.functor.map ((S.ι K.stage).map
        ((shiftFunctorAdd (C K.stage) n m).hom.app K.obj)) ≫
      (S'.ι K.stage).map
        (((F.Φ K.stage).commShiftIso m).hom.app ((shiftFunctor (C K.stage) n).obj K.obj)) ≫
      (shiftFunctor S'.PairCategory m).map ((S'.ι K.stage).map
        (((F.Φ K.stage).commShiftIso n).hom.app K.obj)) ≫
      (S'.ι K.stage).map
        ((shiftFunctorAdd (D K.stage) n m).inv.app ((F.Φ K.stage).obj K.obj))
    erw [Morphism.functor_map_ι]
    erw [(S'.shiftMorphism ℤ m).functor_map_ι]
    simpa only [Functor.CommShift.isoAdd_hom_app, Functor.map_comp, StageSystem.shiftMorphism] using
      congrArg ((S'.ι K.stage).map)
      (congr_app (congrArg Iso.hom ((F.Φ K.stage).commShiftIso_add n m)) K.obj)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem inclusionComp_commShift (i : I) :
    letI := descendedCommShift F hβ
    NatTrans.CommShift (F.ιCompFunctorIso i).hom ℤ := by
  let _ := descendedCommShift F hβ
  constructor
  intro n
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, Category.assoc]
  change F.functor.map (𝟙 _) ≫ (shiftIso F hβ n).hom.app ((S.ι i).obj K) ≫
      (shiftFunctor S'.PairCategory n).map (𝟙 _) =
    𝟙 _ ≫ ((S'.ι i).map (((F.Φ i).commShiftIso n).hom.app K) ≫ 𝟙 _)
  simp only [shiftIso_hom_app, Functor.map_id, Category.id_comp]
  erw [Category.comp_id]

end ExactShift
end

section GenericDescent

variable {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {C : I → Type u} [∀ i, Category.{v} (C i)]
  [∀ i, Preadditive (C i)] [∀ i, HasZeroObject (C i)]
  [∀ i, HasShift (C i) ℤ] [∀ i (n : ℤ), (shiftFunctor (C i) n).Additive]
  [∀ i, Pretriangulated (C i)] [∀ i, IsTriangulated (C i)]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)]
  [∀ i, Preadditive (D i)] [∀ i, HasZeroObject (D i)]
  [∀ i, HasShift (D i) ℤ] [∀ i (n : ℤ), (shiftFunctor (D i) n).Additive]
  [∀ i, Pretriangulated (D i)] [∀ i, IsTriangulated (D i)]
  (SC : StageSystem C) (SD : StageSystem D)
  [∀ i j (h : i ≤ j), (SC.T h).CommShift ℤ]
  [∀ i j (h : i ≤ j), (SC.T h).IsTriangulated]
  [∀ i j k (h : i ≤ j) (k' : j ≤ k), NatTrans.CommShift (SC.assoc h k').hom ℤ]
  [∀ i j (h : i ≤ j), (SD.T h).CommShift ℤ]
  [∀ i j (h : i ≤ j), (SD.T h).IsTriangulated]
  [∀ i j k (h : i ≤ j) (k' : j ≤ k), NatTrans.CommShift (SD.assoc h k').hom ℤ]
  (tC : ∀ i, TStructure (C i)) (tD : ∀ i, TStructure (D i))
  (tCΩ : TStructure SC.PairCategory) (tDΩ : TStructure SD.PairCategory)
  (M : SC.Morphism SD) [∀ i, (M.Φ i).Additive] [∀ i, (M.Φ i).CommShift ℤ]
  [∀ i j (h : i ≤ j), NatTrans.CommShift (M.β h).hom ℤ]

omit [∀ i, (M.Φ i).Additive] in
private theorem stageDescent
    (hC : ∀ i, (tC i).bounded = ⊤) (hD : ∀ i, (tD i).bounded = ⊤)
    (hCΩ : tCΩ.bounded = ⊤) (hDΩ : tDΩ.bounded = ⊤)
    (hFE : ∀ i, (M.Φ i).IsTriangulated)
    (hTE : ∀ i, (M.Φ i).IsTExact (tC i) (tD i))
    (hTC : ∀ i j (h : i ≤ j), (SC.T h).IsTExact (tC i) (tC j))
    (hTD : ∀ i j (h : i ≤ j), (SD.T h).IsTExact (tD i) (tD j))
    (hCΩle : ∀ (n : ℤ) (X : SC.PairCategory), tCΩ.le n X ↔
      ∃ (E : I) (Y : C E),
        (tC E).le n Y ∧ Nonempty (X ≅ (SC.ι E).obj Y))
    (hCΩge : ∀ (n : ℤ) (X : SC.PairCategory), tCΩ.ge n X ↔
      ∃ (E : I) (Y : C E),
        (tC E).ge n Y ∧ Nonempty (X ≅ (SC.ι E).obj Y))
    (hDΩle : ∀ (n : ℤ) (X : SD.PairCategory), tDΩ.le n X ↔
      ∃ (E : I) (Y : D E),
        (tD E).le n Y ∧ Nonempty (X ≅ (SD.ι E).obj Y))
    (hDΩge : ∀ (n : ℤ) (X : SD.PairCategory), tDΩ.ge n X ↔
      ∃ (E : I) (Y : D E),
        (tD E).ge n Y ∧ Nonempty (X ≅ (SD.ι E).obj Y)) :
    ∃ cΩ : M.functor.CommShift ℤ,
      (∀ E (X : C E) (n : ℤ),
        HEq ((cΩ.commShiftIso n).hom.app ((SC.ι E).obj X))
          ((SD.ι E).map (((M.Φ E).commShiftIso n).hom.app X))) ∧
      ∃ (cE : ∀ E, Comparisons (tC E) (tD E) (M.Φ E))
        (cO : Comparisons tCΩ tDΩ M.functor)
        (cTC : ∀ E L (h : E ≤ L), Comparisons (tC E) (tC L) (SC.T h))
        (cTD : ∀ E L (h : E ≤ L), Comparisons (tD E) (tD L) (SD.T h))
        (cJC : ∀ E, Comparisons (tC E) tCΩ (SC.ι E))
        (cJD : ∀ E, Comparisons (tD E) tDΩ (SD.ι E)),
        (∀ E L (h : E ≤ L),
          SquareCompatible (cE E) (cE L) (cTC E L h) (cTD E L h) (M.β h)) ∧
        (∀ E L N (h : E ≤ L) (k : L ≤ N),
          CompositeCompatible (cTC E L h) (cTC L N k) (cTC E N (h.trans k))
            (SC.assoc h k) ∧
          CompositeCompatible (cTD E L h) (cTD L N k) (cTD E N (h.trans k))
            (SD.assoc h k)) ∧
        (∀ E, SquareCompatible (cJC E) (cJD E) (cE E) cO (M.ιCompFunctorIso E)) ∧
        (∀ E L (h : E ≤ L),
          CompositeCompatible (cTC E L h) (cJC L) (cJC E) (SC.transIso h) ∧
          CompositeCompatible (cTD E L h) (cJD L) (cJD E) (SD.transIso h)) := by
  classical
  let cΩ := descendedCommShift M (fun h ↦ inferInstance)
  let := cΩ
  have hιM : ∀ E, NatTrans.CommShift (M.ιCompFunctorIso E).hom ℤ :=
    fun E ↦ inclusionComp_commShift M (fun h ↦ inferInstance) E
  have hFO : M.functor.IsTriangulated := by
    constructor
    intro T hT
    obtain ⟨E, T₀, hT₀, ⟨e⟩⟩ := hT
    exact isomorphic_distinguished _ (((M.Φ E) ⋙ SD.ι E).map_distinguished T₀ hT₀) _
      (M.functor.mapTriangle.mapIso e ≪≫
        (Functor.mapTriangleCompIso (SC.ι E) M.functor).symm.app T₀ ≪≫
        (Functor.mapTriangleIso (M.ιCompFunctorIso E)).app T₀)
  have hJC : ∀ E, (SC.ι E).IsTExact (tC E) tCΩ := by
    intro E
    constructor
    · intro X n hX
      exact ⟨(hCΩle n _).2 ⟨E, X, (tC E).le_of_isLE X n, ⟨Iso.refl _⟩⟩⟩
    · intro X n hX
      exact ⟨(hCΩge n _).2 ⟨E, X, (tC E).ge_of_isGE X n, ⟨Iso.refl _⟩⟩⟩
  have hJD : ∀ E, (SD.ι E).IsTExact (tD E) tDΩ := by
    intro E
    constructor
    · intro X n hX
      exact ⟨(hDΩle n _).2 ⟨E, X, (tD E).le_of_isLE X n, ⟨Iso.refl _⟩⟩⟩
    · intro X n hX
      exact ⟨(hDΩge n _).2 ⟨E, X, (tD E).ge_of_isGE X n, ⟨Iso.refl _⟩⟩⟩
  have hTO : M.functor.IsTExact tCΩ tDΩ := by
    constructor
    · intro X n hX
      obtain ⟨E, Y, hY, ⟨e⟩⟩ := (hCΩle n X).1 (tCΩ.le_of_isLE X n)
      have : (tC E).IsLE Y n := ⟨hY⟩
      have := Functor.IsTExact.isLE_obj (tC E) (tD E) (M.Φ E) Y n
      exact ⟨(hDΩle n _).2 ⟨E, (M.Φ E).obj Y, (tD E).le_of_isLE _ n,
        ⟨M.functor.mapIso e ≪≫ (M.ιCompFunctorIso E).app Y⟩⟩⟩
    · intro X n hX
      obtain ⟨E, Y, hY, ⟨e⟩⟩ := (hCΩge n X).1 (tCΩ.ge_of_isGE X n)
      have : (tC E).IsGE Y n := ⟨hY⟩
      have := Functor.IsTExact.isGE_obj (tC E) (tD E) (M.Φ E) Y n
      exact ⟨(hDΩge n _).2 ⟨E, (M.Φ E).obj Y, (tD E).ge_of_isGE _ n,
        ⟨M.functor.mapIso e ≪≫ (M.ιCompFunctorIso E).app Y⟩⟩⟩
  refine ⟨cΩ, ?_, ?_⟩
  · intro E X n
    exact heq_of_eq (shiftIso_hom_app M (fun h ↦ inferInstance) n ((SC.ι E).obj X))
  · refine ⟨(fun E ↦ canonicalComparisons (tC E) (tD E) (hC E) (hD E) (M.Φ E)),
      canonicalComparisons tCΩ tDΩ hCΩ hDΩ M.functor,
      (fun E L h ↦ canonicalComparisons (tC E) (tC L) (hC E) (hC L) (SC.T h)),
      (fun E L h ↦ canonicalComparisons (tD E) (tD L) (hD E) (hD L) (SD.T h)),
      (fun E ↦ canonicalComparisons (tC E) tCΩ (hC E) hCΩ (SC.ι E)),
      (fun E ↦ canonicalComparisons (tD E) tDΩ (hD E) hDΩ (SD.ι E)),
      ?_, ?_, ?_, ?_⟩
    · intro E L h
      exact canonicalSquare (tC E) (tD E) (tC L) (tD L)
        (hC E) (hD E) (hC L) (hD L) _ _ _ _ (M.β h)
    · intro E L N h k
      exact ⟨canonicalComposite (tC E) (tC L) (tC N) (hC E) (hC L) (hC N)
        _ _ _ (SC.assoc h k),
        canonicalComposite (tD E) (tD L) (tD N) (hD E) (hD L) (hD N)
        _ _ _ (SD.assoc h k)⟩
    · intro E
      exact canonicalSquare (tC E) tCΩ (tD E) tDΩ
        (hC E) hCΩ (hD E) hDΩ _ _ _ _ (M.ιCompFunctorIso E)
    · intro E L h
      exact ⟨canonicalComposite (tC E) (tC L) tCΩ (hC E) (hC L) hCΩ
        _ _ _ (SC.transIso h),
        canonicalComposite (tD E) (tD L) tDΩ (hD E) (hD L) hDΩ
        _ _ _ (SD.transIso h)⟩

end GenericDescent

attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionAbsoluteValue Padic.coefficientExtensionUniformizer

section CoefficientFamily

variable (l : ℕ) [Fact l.Prime] (Ω : Type w) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

/-- The recorded ring of integers at the indicated finite coefficient field.
This is an abbreviation of the existing coefficient construction, not a new ring.
Source: Bhatt--Scholze 6.8.14; DAG coefficient hypotheses
(blueprint: lem-a1-texact-coefficient-stage-descent). -/
abbrev integralRing (E : Padic.FiniteCoefficientFields l Ω) :=
  Padic.coefficientExtensionIntegers l E.val

/-- The specified raw scalar category at a finite coefficient stage.
Source: Bhatt--Scholze 6.8.14(2); DAG coefficient hypotheses
(blueprint: lem-a1-texact-coefficient-stage-descent). -/
abbrev rationalStage (E : Padic.FiniteCoefficientFields l Ω) (C : Type u) :=
  ScalarLocalization (integralRing l Ω E) C (Padic.coefficientExtensionUniformizer l E.val)

variable {C₀ : Padic.FiniteCoefficientFields l Ω → Type u}
  {D₀ : Padic.FiniteCoefficientFields l Ω → Type u'}
  [∀ E, Category.{v} (C₀ E)] [∀ E, Preadditive (C₀ E)]
  [∀ E, Linear (integralRing l Ω E) (C₀ E)]
  [∀ E, HasZeroObject (C₀ E)] [∀ E, HasShift (C₀ E) ℤ]
  [∀ E (n : ℤ), (shiftFunctor (C₀ E) n).Additive]
  [∀ E, Pretriangulated (C₀ E)] [∀ E, IsTriangulated (C₀ E)]
  [∀ E, Category.{v'} (D₀ E)] [∀ E, Preadditive (D₀ E)]
  [∀ E, Linear (integralRing l Ω E) (D₀ E)]
  [∀ E, HasZeroObject (D₀ E)] [∀ E, HasShift (D₀ E) ℤ]
  [∀ E (n : ℤ), (shiftFunctor (D₀ E) n).Additive]
  [∀ E, Pretriangulated (D₀ E)] [∀ E, IsTriangulated (D₀ E)]

variable (tC₀ : ∀ E, TStructure (C₀ E)) (tD₀ : ∀ E, TStructure (D₀ E))
  [∀ E, HasZeroObject (rationalStage l Ω E (C₀ E))] [∀ E, HasShift (rationalStage l Ω E (C₀ E)) ℤ]
  [∀ E (n : ℤ), (shiftFunctor (rationalStage l Ω E (C₀ E)) n).Additive]
  [∀ E, Pretriangulated (rationalStage l Ω E (C₀ E))]
  [∀ E, IsTriangulated (rationalStage l Ω E (C₀ E))]
  [∀ E, (ScalarLocalization.localization (integralRing l Ω E) (C₀ E)
    (Padic.coefficientExtensionUniformizer l E.val)).CommShift ℤ]
  [∀ E, HasZeroObject (rationalStage l Ω E (D₀ E))] [∀ E, HasShift (rationalStage l Ω E (D₀ E)) ℤ]
  [∀ E (n : ℤ), (shiftFunctor (rationalStage l Ω E (D₀ E)) n).Additive]
  [∀ E, Pretriangulated (rationalStage l Ω E (D₀ E))]
  [∀ E, IsTriangulated (rationalStage l Ω E (D₀ E))]
  [∀ E, (ScalarLocalization.localization (integralRing l Ω E) (D₀ E)
    (Padic.coefficientExtensionUniformizer l E.val)).CommShift ℤ]

variable (tC : ∀ E, TStructure (rationalStage l Ω E (C₀ E)))
  (tD : ∀ E, TStructure (rationalStage l Ω E (D₀ E)))
  (SC : StageSystem (fun E ↦ rationalStage l Ω E (C₀ E)))
  (SD : StageSystem (fun E ↦ rationalStage l Ω E (D₀ E)))
  [∀ E L (h : E ≤ L), (SC.T h).CommShift ℤ]
  [∀ E L (h : E ≤ L), (SC.T h).IsTriangulated]
  [∀ E L M (h : E ≤ L) (k : L ≤ M), NatTrans.CommShift (SC.assoc h k).hom ℤ]
  [∀ E L (h : E ≤ L), (SD.T h).CommShift ℤ]
  [∀ E L (h : E ≤ L), (SD.T h).IsTriangulated]
  [∀ E L M (h : E ≤ L) (k : L ≤ M), NatTrans.CommShift (SD.assoc h k).hom ℤ]

variable (tCΩ : TStructure SC.PairCategory) (tDΩ : TStructure SD.PairCategory)
  (F₀ : ∀ E, C₀ E ⥤ D₀ E) [∀ E, (F₀ E).Additive]
  [∀ E, (F₀ E).Linear (integralRing l Ω E)]
  [∀ E, (F₀ E).CommShift ℤ] [∀ E, (F₀ E).IsTriangulated]
  (M : SC.Morphism SD) [∀ E, (M.Φ E).Additive] [∀ E, (M.Φ E).CommShift ℤ]
  [∀ E L (h : E ≤ L), NatTrans.CommShift (M.β h).hom ℤ]

set_option backward.isDefEq.respectTransparency true in
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- Descent through raw localization and the common-stage quotient, with canonical
truncation comparisons, exact heart restrictions, and every coefficient coherence square.

Source: the abstract lemma extracted from the coefficient argument in
Bhatt--Scholze 6.8.14(1)--(2), Remark 6.8.15; BBD 1.3.3, 1.3.6, 1.3.17
(blueprint: lem-a1-texact-coefficient-stage-descent).

Proof:
1. Use the supplied shift-compatible localization factorization. The triangle
   presentation proves exactness; the isomorphism closures of the integral halves
   prove preservation at zero, and shifts give every cutoff.
2. Descend the finite-stage shift comparisons using StageSystem.descNatTrans.
   Beta compatibility gives naturality; the stagewise zero and addition equations
   give the CommShift laws. Represent pair triangles and halves at a finite stage
   to prove exactness and t-exactness of the descended functor and inclusions.
3. Preserve the intersection of the halves, and map the distinguished triangle
   characterizing each short exact sequence in the actual heart restriction.
4. Use the canonical truncation comparison isomorphisms and their normalized
   uniqueness. Compose these with the specified shift comparison for cohomology.
5. Apply naturality and composition of these canonical comparisons to beta,
   tower associators, inclusion squares and transition identifications.
6. Uniqueness identifies the inclusion comparisons with any supplied finite-stage
   truncation computation; the inclusion and transition squares express the
   finite-stage representation and its independence of further enlargement.
-/
theorem texact_coefficient_stage_descent
    [∀ E (n : ℤ), (shiftFunctor (C₀ E) n).Linear (integralRing l Ω E)]
    [∀ E (n : ℤ), (shiftFunctor (D₀ E) n).Linear (integralRing l Ω E)]
    (hC₀ : ∀ E, (tC₀ E).bounded = ⊤) (hD₀ : ∀ E, (tD₀ E).bounded = ⊤)
    (hC : ∀ E, (tC E).bounded = ⊤) (hD : ∀ E, (tD E).bounded = ⊤)
    (hCΩ : tCΩ.bounded = ⊤) (hDΩ : tDΩ.bounded = ⊤)
    (hLC : ∀ E, IsLocalizedTStructure (integralRing l Ω E) (C₀ E)
      (Padic.coefficientExtensionUniformizer l E.val) (tC₀ E) (tC E))
    (hLD : ∀ E, IsLocalizedTStructure (integralRing l Ω E) (D₀ E)
      (Padic.coefficientExtensionUniformizer l E.val) (tD₀ E) (tD E))
    (hF₀ : ∀ E (X : C₀ E),
      ((tC₀ E).le 0 X → (tD₀ E).le 0 ((F₀ E).obj X)) ∧
      ((tC₀ E).ge 0 X → (tD₀ E).ge 0 ((F₀ E).obj X)))
    (hF : ∀ E, FractionExtension (F₀ E) (M.Φ E))
    (hTC : ∀ E L (h : E ≤ L), (SC.T h).IsTExact (tC E) (tC L))
    (hTD : ∀ E L (h : E ≤ L), (SD.T h).IsTExact (tD E) (tD L))
    (unitC : ∀ E, SC.T (le_refl E) ≅ 𝟭 _)
    (unitD : ∀ E, SD.T (le_refl E) ≅ 𝟭 _)
    (hunitC : ∀ E, NatTrans.CommShift (unitC E).hom ℤ)
    (hunitD : ∀ E, NatTrans.CommShift (unitD E).hom ℤ)
    (hunitLeftC : ∀ E L (h : E ≤ L) (X : rationalStage l Ω E (C₀ E)),
      (SC.assoc (le_refl E) h).hom.app X = (SC.T h).map ((unitC E).hom.app X))
    (hunitRightC : ∀ E L (h : E ≤ L) (X : rationalStage l Ω E (C₀ E)),
      (SC.assoc h (le_refl L)).hom.app X = (unitC L).hom.app ((SC.T h).obj X))
    (hunitLeftD : ∀ E L (h : E ≤ L) (X : rationalStage l Ω E (D₀ E)),
      (SD.assoc (le_refl E) h).hom.app X = (SD.T h).map ((unitD E).hom.app X))
    (hunitRightD : ∀ E L (h : E ≤ L) (X : rationalStage l Ω E (D₀ E)),
      (SD.assoc h (le_refl L)).hom.app X = (unitD L).hom.app ((SD.T h).obj X))
    (hbetaId : ∀ E (X : rationalStage l Ω E (C₀ E)),
      (M.β (le_refl E)).hom.app X ≫ (M.Φ E).map ((unitC E).hom.app X) =
        (unitD E).hom.app ((M.Φ E).obj X))
    (hTruncC : ∀ E, TruncationsComputedAt (tC E) tCΩ (SC.ι E))
    (hTruncD : ∀ E, TruncationsComputedAt (tD E) tDΩ (SD.ι E))
    (hCΩle : ∀ (n : ℤ) (X : SC.PairCategory), tCΩ.le n X ↔
      ∃ (E : Padic.FiniteCoefficientFields l Ω) (Y : rationalStage l Ω E (C₀ E)),
        (tC E).le n Y ∧ Nonempty (X ≅ (SC.ι E).obj Y))
    (hCΩge : ∀ (n : ℤ) (X : SC.PairCategory), tCΩ.ge n X ↔
      ∃ (E : Padic.FiniteCoefficientFields l Ω) (Y : rationalStage l Ω E (C₀ E)),
        (tC E).ge n Y ∧ Nonempty (X ≅ (SC.ι E).obj Y))
    (hDΩle : ∀ (n : ℤ) (X : SD.PairCategory), tDΩ.le n X ↔
      ∃ (E : Padic.FiniteCoefficientFields l Ω) (Y : rationalStage l Ω E (D₀ E)),
        (tD E).le n Y ∧ Nonempty (X ≅ (SD.ι E).obj Y))
    (hDΩge : ∀ (n : ℤ) (X : SD.PairCategory), tDΩ.ge n X ↔
      ∃ (E : Padic.FiniteCoefficientFields l Ω) (Y : rationalStage l Ω E (D₀ E)),
        (tD E).ge n Y ∧ Nonempty (X ≅ (SD.ι E).obj Y)) :
    ∃ cΩ : M.functor.CommShift ℤ,
      (∀ E (X : rationalStage l Ω E (C₀ E)) (n : ℤ),
        HEq ((cΩ.commShiftIso n).hom.app ((SC.ι E).obj X))
          ((SD.ι E).map (((M.Φ E).commShiftIso n).hom.app X))) ∧
      ∃ (cE : ∀ E, Comparisons (tC E) (tD E) (M.Φ E))
        (cO : Comparisons tCΩ tDΩ M.functor)
        (cTC : ∀ E L (h : E ≤ L), Comparisons (tC E) (tC L) (SC.T h))
        (cTD : ∀ E L (h : E ≤ L), Comparisons (tD E) (tD L) (SD.T h))
        (cJC : ∀ E, Comparisons (tC E) tCΩ (SC.ι E))
        (cJD : ∀ E, Comparisons (tD E) tDΩ (SD.ι E)),
        (∀ E L (h : E ≤ L),
          SquareCompatible (cE E) (cE L) (cTC E L h) (cTD E L h) (M.β h)) ∧
        (∀ E L N (h : E ≤ L) (k : L ≤ N),
          CompositeCompatible (cTC E L h) (cTC L N k) (cTC E N (h.trans k))
            (SC.assoc h k) ∧
          CompositeCompatible (cTD E L h) (cTD L N k) (cTD E N (h.trans k))
            (SD.assoc h k)) ∧
        (∀ E, SquareCompatible (cJC E) (cJD E) (cE E) cO (M.ιCompFunctorIso E)) ∧
        (∀ E L (h : E ≤ L),
          CompositeCompatible (cTC E L h) (cJC L) (cJC E) (SC.transIso h) ∧
          CompositeCompatible (cTD E L h) (cJD L) (cJD E) (SD.transIso h)) := by
  classical
  have hFE : ∀ E, (M.Φ E).IsTriangulated := fun E ↦
    localizedExact (tC₀ E) (tC E) (tD₀ E) (tD E) (hLC E) (hLD E)
      (F₀ E) (M.Φ E) (hF E)
  have hTE : ∀ E, (M.Φ E).IsTExact (tC E) (tD E) := fun E ↦
    localizedTExact (tC₀ E) (tC E) (tD₀ E) (tD E) (hLC E) (hLD E)
      (F₀ E) (M.Φ E) (hF E) (fun X ↦ (hF₀ E X).1) (fun X ↦ (hF₀ E X).2)
  exact stageDescent SC SD tC tD tCΩ tDΩ M hC hD hCΩ hDΩ hFE hTE hTC hTD
    hCΩle hCΩge hDΩle hDΩge

end CoefficientFamily

end CategoryTheory.CoefficientStageDescent
