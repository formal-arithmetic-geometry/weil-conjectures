/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.CategoryTheory.ScalarLocalization
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.FiniteStagePairCategory
public import WeilConjectures.CategoryTheory.StageSystem.Triangulated
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
import Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Colimit.Module

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

open Limits Pretriangulated Triangulated TensorProduct

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

end Coherence

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

/-- Descent through raw localization and the common-stage quotient, with canonical
truncation comparisons, exact heart restrictions, and every coefficient coherence square.

Source: the abstract lemma extracted from the coefficient argument in
Bhatt--Scholze 6.8.14(1)--(2), Remark 6.8.15; BBD 1.3.3, 1.3.6, 1.3.17
(blueprint: lem-a1-texact-coefficient-stage-descent).

Proof (the ten steps of the node):
1. Extend each integral linear Hom map by tensor base change. Pure tensors show
   identity and composition preservation; localize the specified linear shift comparison.
2. A rational distinguished triangle comes from an integral one, including its shifted
   third arrow. Exactness of F₀ proves exactness after localization. The isomorphism
   closures of the halves and shift compatibility prove preservation at every cutoff.
3. At a common field L conjugate F_L(u) by beta. Its tower equation and naturality
   show compatibility with further extension. The directed Hom-colimit universal property
   descends these maps, without assuming faithfulness of coefficient transitions.
4. The middle betas cancel in a composite. Thus the descended maps preserve composition
   and identity. This is precisely the existing M.functor and its stage-inclusion square.
5. Represent its shift comparison at a stage. Shift compatibility of beta makes it
   natural and independent of the stage. Finite-stage triangles and halves then prove
   exactness and t-exactness on the pair category. The same argument applies to inclusions.
6. The heart is the intersection of the halves. Use the short-exact/triangle criterion
   of lem-weil-heart-short-exact-triangles to obtain exactness of the actual restriction.
7. Apply lem-pod-texact-truncation-comparison to obtain the two uniquely normalized
   natural isomorphisms, with the displayed canonical counit and unit equations.
8. Its natural-transformation and composition clauses give SquareCompatible for beta
   and CompositeCompatible for the tower associators and the identity identifications.
9. Compose the two truncation comparisons and the integer shift comparison. This is
   q_formula. Shift-compatible beta squares and tower squares persist under this composition.
10. Uniqueness identifies each inclusion comparison with finite-stage computation of
   truncations and their canonical maps. The square for the inclusion identifies the
   Omega comparison with its finite-stage representative. The transIso composite square
   gives independence after any further enlargement; the same formulas apply to q.
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
  sorry

end CoefficientFamily

end CategoryTheory.CoefficientStageDescent
