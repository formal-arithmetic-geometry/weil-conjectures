/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the project license.
Authors: SHEAF group Q133
-/
module

public import Sheaf.Algebra.Homology.UniformFilteredTruncation
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Sheaf.Algebra.Homology.FilteredBoundedLocalizationComparison
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated

/-!
# Graded comparison for finite filtered bifunctors

Source: Varshavsky, Lefschetz--Verdier trace formula, §5.1.3(c)--(e),
Lemma 5.1.4(i)--(iii), pp.39--41
(blueprint: lem-trf-filtered-bifunctor-graded-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w v u e f x y
universe wA vA uA eA fA xA yA wB vB uB eB fB xB yB wC vC uC eC fC xC yC

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Functor CategoryTheory.Pretriangulated.Opposite

open scoped CategoryTheory.Prod

namespace CategoryTheory.FilteredBifunctor

/-- An ordinary and filtered full triangulated domain, with the restrictions of the
canonical forgetful and graded functors. The image is closed under high and low
filtration truncations, hence under taking pure graded pieces. `pureComparison`
is fixed by its image in the unbounded category; it is not an arbitrary isomorphism.
Source: Varshavsky 5.1.1(e), 5.1.2 and Lemma 5.1.4, domain restrictions
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
class Domain (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [UniformFiltered.Model A] (E : Type e) [Category.{f} E]
    (D : Type x) [Category.{y} D] where
  [ordinary_preadditive : Preadditive E]
  [ordinary_zero : HasZeroObject E]
  [ordinary_shift : HasShift E ℤ]
  [ordinary_shift_additive : ∀ n : ℤ, (shiftFunctor E n).Additive]
  [ordinary_pretriangulated : Pretriangulated E]
  [ordinary_triangulated : IsTriangulated E]
  [filtered_preadditive : Preadditive D]
  [filtered_zero : HasZeroObject D]
  [filtered_shift : HasShift D ℤ]
  [filtered_shift_additive : ∀ n : ℤ, (shiftFunctor D n).Additive]
  [filtered_pretriangulated : Pretriangulated D]
  [filtered_triangulated : IsTriangulated D]
  ordinaryIncl : E ⥤ DerivedCategory A
  filteredIncl : D ⥤ UniformFiltered.Derived A
  [ordinary_full : ordinaryIncl.Full]
  [ordinary_faithful : ordinaryIncl.Faithful]
  [filtered_full : filteredIncl.Full]
  [filtered_faithful : filteredIncl.Faithful]
  [ordinaryIncl_shift : ordinaryIncl.CommShift ℤ]
  [filteredIncl_shift : filteredIncl.CommShift ℤ]
  [ordinaryIncl_exact : ordinaryIncl.IsTriangulated]
  [filteredIncl_exact : filteredIncl.IsTriangulated]
  omega : D ⥤ E
  gr : ℤ → D ⥤ E
  [omega_shift : omega.CommShift ℤ]
  [gr_shift : ∀ p : ℤ, (gr p).CommShift ℤ]
  [omega_exact : omega.IsTriangulated]
  [gr_exact : ∀ p : ℤ, (gr p).IsTriangulated]
  omegaImage : omega ⋙ ordinaryIncl ≅ filteredIncl ⋙ UniformFiltered.Model.omega
  grImage : ∀ p : ℤ, gr p ⋙ ordinaryIncl ≅ filteredIncl ⋙ UniformFiltered.Model.gr p
  high_closed : ∀ (r : ℤ) (M : D),
    filteredIncl.essImage ((UniformFiltered.Model.high r).obj (filteredIncl.obj M))
  low_closed : ∀ (r : ℤ) (M : D),
    filteredIncl.essImage ((UniformFiltered.Model.low r).obj (filteredIncl.obj M))
  pureComparison : ∀ (p : ℤ) (M : D),
    (∀ q : ℤ, q ≠ p → IsZero ((gr q).obj M)) → ((gr p).obj M ≅ omega.obj M)
  pureNormalization : ∀ (p : ℤ) (M : D)
    (h : ∀ q : ℤ, q ≠ p → IsZero ((gr q).obj M))
    (h' : ∀ q : ℤ, q ≠ p →
      IsZero ((UniformFiltered.Model.gr q).obj (filteredIncl.obj M))),
    ordinaryIncl.map (pureComparison p M h).hom ≫ omegaImage.hom.app M =
      (grImage p).hom.app M ≫
        (UniformFiltered.Model.pureComparison p (filteredIncl.obj M) h').hom

attribute [instance_reducible] Domain.ordinary_preadditive Domain.ordinary_shift
  Domain.ordinary_pretriangulated Domain.filtered_preadditive Domain.filtered_shift
  Domain.filtered_pretriangulated Domain.ordinaryIncl_shift Domain.filteredIncl_shift
  Domain.omega_shift Domain.gr_shift
attribute [instance] Domain.ordinary_preadditive Domain.ordinary_zero Domain.ordinary_shift
  Domain.ordinary_shift_additive Domain.ordinary_pretriangulated Domain.ordinary_triangulated
  Domain.filtered_preadditive Domain.filtered_zero Domain.filtered_shift
  Domain.filtered_shift_additive Domain.filtered_pretriangulated Domain.filtered_triangulated
  Domain.ordinary_full Domain.ordinary_faithful Domain.filtered_full Domain.filtered_faithful
  Domain.ordinaryIncl_shift Domain.filteredIncl_shift Domain.ordinaryIncl_exact
  Domain.filteredIncl_exact Domain.omega_shift Domain.gr_shift Domain.omega_exact Domain.gr_exact

/-- The unrestricted domain uses identity embeddings and the actual unbounded model.
Source: Varshavsky 5.1.2 (blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
@[instance_reducible]
def unrestrictedDomain (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [UniformFiltered.Model A] :
    Domain A (DerivedCategory A) (UniformFiltered.Derived A) where
  ordinaryIncl := 𝟭 _
  filteredIncl := 𝟭 _
  omega := UniformFiltered.Model.omega
  gr := UniformFiltered.Model.gr
  omegaImage := Iso.refl _
  grImage _ := Iso.refl _
  high_closed _ _ := ⟨_, ⟨Iso.refl _⟩⟩
  low_closed _ _ := ⟨_, ⟨Iso.refl _⟩⟩
  pureComparison := UniformFiltered.Model.pureComparison
  pureNormalization _ _ _ _ := by simp

/-- A low cutoff and its pure top grade in a full filtered domain. The two maps
are the actual quotient and inclusion after the fully faithful embedding.
Source: Varshavsky Lemma 5.1.4(i), first paragraph and (5.1)
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
structure LowCut {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [UniformFiltered.Model A]
    {E : Type e} [Category.{f} E] {D : Type x} [Category.{y} D]
    (P : Domain A E D) (p : ℤ) (M : D) where
  cut : D
  pure : D
  cutImage : P.filteredIncl.obj cut ≅
    (UniformFiltered.Model.low (p + 1)).obj (P.filteredIncl.obj M)
  pureImage : P.filteredIncl.obj pure ≅
    (UniformFiltered.Model.high p).obj (P.filteredIncl.obj cut)
  quotient : M ⟶ cut
  inclusion : pure ⟶ cut
  quotient_normalization : P.filteredIncl.map quotient ≫ cutImage.hom =
    (UniformFiltered.Model.quotient (p + 1)).app (P.filteredIncl.obj M)
  inclusion_normalization : P.filteredIncl.map inclusion = pureImage.hom ≫
    (UniformFiltered.Model.inclusion p).app (P.filteredIncl.obj cut)
  pure_support : ∀ q : ℤ, q ≠ p → IsZero ((P.gr q).obj pure)
  [quotient_grade_iso : IsIso ((P.gr p).map quotient)]
  [inclusion_grade_iso : IsIso ((P.gr p).map inclusion)]

attribute [instance] LowCut.quotient_grade_iso LowCut.inclusion_grade_iso

/-- The canonical underlying pure-cut object identified with the original grade.
Source: Varshavsky Lemma 5.1.4(i), first paragraph
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
def LowCut.pureToGrade {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [UniformFiltered.Model A]
    {E : Type e} [Category.{f} E] {D : Type x} [Category.{y} D]
    {P : Domain A E D} {p : ℤ} {M : D} (T : LowCut P p M) :
    P.omega.obj T.pure ≅ (P.gr p).obj M :=
  (P.pureComparison p T.pure T.pure_support).symm ≪≫
    asIso ((P.gr p).map T.inclusion) ≪≫ (asIso ((P.gr p).map T.quotient)).symm

/-- The high cutoff used in the contravariant variable, followed by its pure
bottom grade. Its maps are the actual inclusion and quotient in the ambient category.
Source: Varshavsky 5.1.3(c), Lemma 5.1.4(i)
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
structure HighCut {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [UniformFiltered.Model A]
    {E : Type e} [Category.{f} E] {D : Type x} [Category.{y} D]
    (P : Domain A E D) (p : ℤ) (M : D) where
  cut : D
  pure : D
  cutImage : P.filteredIncl.obj cut ≅
    (UniformFiltered.Model.high p).obj (P.filteredIncl.obj M)
  pureImage : P.filteredIncl.obj pure ≅
    (UniformFiltered.Model.low (p + 1)).obj (P.filteredIncl.obj cut)
  inclusion : cut ⟶ M
  quotient : cut ⟶ pure
  inclusion_normalization : P.filteredIncl.map inclusion = cutImage.hom ≫
    (UniformFiltered.Model.inclusion p).app (P.filteredIncl.obj M)
  quotient_normalization : P.filteredIncl.map quotient ≫ pureImage.hom =
    (UniformFiltered.Model.quotient (p + 1)).app (P.filteredIncl.obj cut)
  pure_support : ∀ q : ℤ, q ≠ p → IsZero ((P.gr q).obj pure)
  [inclusion_grade_iso : IsIso ((P.gr p).map inclusion)]
  [quotient_grade_iso : IsIso ((P.gr p).map quotient)]

attribute [instance] HighCut.inclusion_grade_iso HighCut.quotient_grade_iso

/-- The canonical grade identification for the high-cut pure object.
Source: Varshavsky 5.1.3(c), Lemma 5.1.4(i)
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
def HighCut.pureToGrade {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [UniformFiltered.Model A]
    {E : Type e} [Category.{f} E] {D : Type x} [Category.{y} D]
    {P : Domain A E D} {p : ℤ} {M : D} (T : HighCut P p M) :
    P.omega.obj T.pure ≅ (P.gr p).obj M :=
  (P.pureComparison p T.pure T.pure_support).symm ≪≫
    (asIso ((P.gr p).map T.quotient)).symm ≪≫ asIso ((P.gr p).map T.inclusion)

/-- Finite support for one filtered input, measured by the actual graded functors.
Source: Varshavsky 5.1.1(a), 5.1.2 (blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
def SupportedOn {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [UniformFiltered.Model A] {E : Type e} [Category.{f} E]
    {D : Type x} [Category.{y} D] (P : Domain A E D) (s : Finset ℤ) (M : D) : Prop :=
  ∀ p : ℤ, p ∉ s → IsZero ((P.gr p).obj M)

/-- The finite diagonal in two finite supports, including the empty diagonal.
Source: Varshavsky Lemma 5.1.4(i)
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
abbrev Diagonal (i : ℤ) (s t : Finset ℤ) :=
  ↥((s ×ˢ t).filter (fun q ↦ q.1 + q.2 = i))

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [UniformFiltered.Model A] {EA : Type eA} [Category.{fA} EA]
  {DA : Type xA} [Category.{yA} DA] [PA : Domain A EA DA]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [UniformFiltered.Model B] {EB : Type eB} [Category.{fB} EB]
  {DB : Type xB} [Category.{yB} DB] [PB : Domain B EB DB]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  [UniformFiltered.Model C] {EC : Type eC} [Category.{fC} EC]
  {DC : Type xC} [Category.{yC} DC] [PC : Domain C EC DC]

/-- Finite biproducts of functors follow from the pointwise finite products and addition.
Source: Varshavsky Lemma 5.1.4(i)
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
instance finiteBiproductsOfFunctors (J : Type x) [Category.{y} J] :
    HasFiniteBiproducts (J ⥤ EC) := HasFiniteBiproducts.of_hasFiniteProducts

/-- An exact covariant bifiltered lift, with its natural forgetful comparison.
The bounds hold for all finite intervals, using derived vanishing of the grades.
Source: Varshavsky 5.1.3(c),(d)
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
structure CovariantLift where
  ordinary : EA × EB ⥤ EC
  filtered : DA × DB ⥤ DC
  [ordinary_left_shift : ∀ M : EA, ((curry.obj ordinary).obj M).CommShift ℤ]
  [ordinary_right_shift : ∀ N : EB, ((curry.obj ordinary).flip.obj N).CommShift ℤ]
  [filtered_left_shift : ∀ M : DA, ((curry.obj filtered).obj M).CommShift ℤ]
  [filtered_right_shift : ∀ N : DB, ((curry.obj filtered).flip.obj N).CommShift ℤ]
  ordinary_left_exact : ∀ M : EA, ((curry.obj ordinary).obj M).IsTriangulated
  ordinary_right_exact : ∀ N : EB, ((curry.obj ordinary).flip.obj N).IsTriangulated
  filtered_left_exact : ∀ M : DA, ((curry.obj filtered).obj M).IsTriangulated
  filtered_right_exact : ∀ N : DB, ((curry.obj filtered).flip.obj N).IsTriangulated
  phi : filtered ⋙ PC.omega ≅ (PA.omega).prod PB.omega ⋙ ordinary
  interval : ∀ (a b c d : ℤ) (M : DA) (N : DB),
    (∀ p : ℤ, p < a ∨ b < p → IsZero ((PA.gr p).obj M)) →
    (∀ p : ℤ, p < c ∨ d < p → IsZero ((PB.gr p).obj N)) →
    ∀ p : ℤ, p < a + c ∨ b + d < p →
      IsZero ((PC.gr p).obj (filtered.obj (M, N)))

/-- The full domain of pairs with the indicated finite signed grade supports.
The first set indexes `gr^j`; it is reflected only in the contravariant case.
Source: Varshavsky Lemma 5.1.4(i)
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
def covariantSupport (s t : Finset ℤ) : ObjectProperty (DA × DB) := fun M ↦
  (∀ p : ℤ, p ∉ s → IsZero ((PA.gr p).obj M.1)) ∧ SupportedOn PB t M.2

/-- A single graded summand on the full supported-pair domain.
Source: Varshavsky Lemma 5.1.4(i)
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
def covariantSummand (F : CovariantLift (PA := PA) (PB := PB) (PC := PC))
    (s t : Finset ℤ) (j k : ℤ) :
    (covariantSupport (PA := PA) (PB := PB) s t).FullSubcategory ⥤ EC :=
  ObjectProperty.ι _ ⋙ ((PA.gr j)).prod (PB.gr k) ⋙ F.ordinary

/-- The finite diagonal biproduct of the actual graded bifunctor values.
Source: Varshavsky Lemma 5.1.4(i)
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
def covariantSum (F : CovariantLift (PA := PA) (PB := PB) (PC := PC))
    (i : ℤ) (s t : Finset ℤ) :
    (covariantSupport (PA := PA) (PB := PB) s t).FullSubcategory ⥤ EC :=
  biproduct (fun q : Diagonal i s t ↦ covariantSummand F s t q.val.1 q.val.2)

/-- A supplied filtered transformation lifts the ordinary one exactly when its
natural forgetful square commutes. No arbitrary transformation is given a lift.
Source: Varshavsky 5.1.3(e)
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
def covariantLiftsTransformation
    (F G : CovariantLift (PA := PA) (PB := PB) (PC := PC))
    (H : F.ordinary ⟶ G.ordinary) (HF : F.filtered ⟶ G.filtered) : Prop :=
  whiskerRight HF PC.omega ≫ G.phi.hom =
    F.phi.hom ≫ whiskerLeft ((PA.omega).prod PB.omega) H

/-- The covariant graded comparison, its normalization by the specified phi,
and its compatibility with supplied transformations, including iso detection.
Natural isomorphisms on each full supported domain express naturality in both inputs.
Their components are independent of the finite supports used to display the sum.
The fully faithful domain embeddings and truncation closure include bounded,
one-sided and full triangulated-domain variants in this same assertion.

Source: Varshavsky 5.1.3(c)--(e), Lemma 5.1.4(i)--(iii), pp.39--41.
Proof:
1. For j+k=i apply the exact grade functor to the two truncation triangles of
   lem-trf-filtered-unbounded-truncation. Use low(j+1) and low(k+1) as cutoff inputs.
   The interval inequality kills each discarded term. The zero-cone criterion
   identifies the cutoff value with the value on the pure input pair.
2. On the pure output grade i equals forgetting. Apply phi there, and the
   canonical pure identifications of the two inputs, to identify each cutoff
   value with G(gr^j,gr^k). These are natural identifications.
3. The two low quotient maps
    give the comparison to the sum of cutoff values. Only
   finitely many input grades occur. Work with common finite supports on each
   finite diagram; adding zero summands changes no component. Cutoff maps
   commute with shifts and cone triangles. Finite sums of distinguished triangles
   are distinguished (lem-weil-finite-sums-distinguished-triangles).
4. On pure pairs the comparison is phi and all other summands vanish. Induct first
   on the second filtration width for a pure first input and then on the first
   width, splitting off the top grade by the truncation triangle. Use
   lem-sf-triangle-morphism-iso to conclude invertibility. Reverse the image
   triangle in the contravariant variable. This constructs theta with the stated
   pure normalization and support independence.
5. For a supplied transformation, naturality with the cutoff maps gives the
   square before inversion. Naturality with the pure-to-cut maps and the given
   phi square give its component formula after inversion. Summing proves the
   displayed natural-transformation identity.
6. If H is invertible, that identity makes every graded HF invertible. Its cone
   has all grades zero; a uniformly finite representative maps to zero by a
   graded quasi-isomorphism. It is zero in the localization. The zero-cone
   criterion implies HF is invertible, with natural component inverses.
7. Full domain embeddings preserve these maps and inverses. Truncation closure
   retains every cut and pure input; exactness retains cone triangles. Bounded
   and one-sided full embeddings follow from
   lem-trf-filtered-bounded-localization-comparison. The induction is in finite
   filtration width and imposes no cochain boundedness.
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
theorem filteredBifunctorGradedComparison_covariant :
    (∀ M : DA, ∃ s : Finset ℤ,
      ∀ p : ℤ, p ∉ s → IsZero ((PA.gr p).obj M)) ∧
    (∀ N : DB, ∃ t : Finset ℤ, SupportedOn PB t N) ∧
    ∃ theta : ∀ (F : CovariantLift (PA := PA) (PB := PB) (PC := PC))
      (i : ℤ) (s t : Finset ℤ),
      ObjectProperty.ι (covariantSupport (PA := PA) (PB := PB) s t) ⋙
        F.filtered ⋙ PC.gr i ≅ covariantSum F i s t,
    (∀ (F : CovariantLift (PA := PA) (PB := PB) (PC := PC))
      (i : ℤ) (s t : Finset ℤ)
      (X : (covariantSupport (PA := PA) (PB := PB) s t).FullSubcategory)
      (q : Diagonal i s t)
      (TM : LowCut PA q.val.1 X.obj.1)
      (TN : LowCut PB q.val.2 X.obj.2)
      (e : (PC.gr i).obj (F.filtered.obj (TM.pure, TN.pure)) ≅
        (PC.gr i).obj (F.filtered.obj (TM.cut, TN.cut)))
      (_he : e.hom = (PC.gr i).map
        (F.filtered.map (TM.inclusion ×ₘ TN.inclusion)))
      (hOut : ∀ p : ℤ, p ≠ i → IsZero ((PC.gr p).obj
        (F.filtered.obj (TM.pure, TN.pure)))),
      (theta F i s t).hom.app X ≫
          (biproduct.π (fun r : Diagonal i s t ↦
            covariantSummand F s t r.val.1 r.val.2) q).app X =
        (PC.gr i).map (F.filtered.map
          (TM.quotient ×ₘ TN.quotient)) ≫ e.inv ≫
          (PC.pureComparison i
            (F.filtered.obj (TM.pure, TN.pure)) hOut).hom ≫
          F.phi.hom.app (TM.pure, TN.pure) ≫
          F.ordinary.map (TM.pureToGrade.hom ×ₘ TN.pureToGrade.hom)) ∧
    (∀ (F : CovariantLift (PA := PA) (PB := PB) (PC := PC))
      (i : ℤ) (s t : Finset ℤ)
      (X : (covariantSupport (PA := PA) (PB := PB) s t).FullSubcategory)
      (q : Diagonal i s t)
      (hM : ∀ p : ℤ, p ≠ q.val.1 → IsZero ((PA.gr p).obj X.obj.1))
      (hN : ∀ p : ℤ, p ≠ q.val.2 → IsZero ((PB.gr p).obj X.obj.2))
      (hOut : ∀ p : ℤ, p ≠ i → IsZero ((PC.gr p).obj (F.filtered.obj X.obj))),
      (theta F i s t).hom.app X ≫
          (biproduct.π (fun q : Diagonal i s t ↦
            covariantSummand F s t q.val.1 q.val.2) q).app X =
        (PC.pureComparison i (F.filtered.obj X.obj) hOut).hom ≫ F.phi.hom.app X.obj ≫
          F.ordinary.map
            ((PA.pureComparison q.val.1 X.obj.1 hM).inv ×ₘ
              (PB.pureComparison q.val.2 X.obj.2 hN).inv)) ∧
    (∀ (F : CovariantLift (PA := PA) (PB := PB) (PC := PC))
      (i : ℤ) (s t s' t' : Finset ℤ)
      (X : (covariantSupport (PA := PA) (PB := PB) s t).FullSubcategory)
      (X' : (covariantSupport (PA := PA) (PB := PB) s' t').FullSubcategory)
      (hX : X.obj = X'.obj) (q : Diagonal i s t) (q' : Diagonal i s' t')
      (hq : q.val = q'.val),
      (theta F i s t).hom.app X ≫
          (biproduct.π (fun r : Diagonal i s t ↦
            covariantSummand F s t r.val.1 r.val.2) q).app X ≫
          eqToHom (congrArg₂ (fun (r : ℤ × ℤ) (Y : DA × DB) ↦
            F.ordinary.obj ((PA.gr r.1).obj Y.1, (PB.gr r.2).obj Y.2)) hq hX) =
        eqToHom (congrArg (fun Z ↦ (PC.gr i).obj (F.filtered.obj Z)) hX) ≫
          (theta F i s' t').hom.app X' ≫
          (biproduct.π (fun r : Diagonal i s' t' ↦
            covariantSummand F s' t' r.val.1 r.val.2) q').app X') ∧
    (∀ (F G : CovariantLift (PA := PA) (PB := PB) (PC := PC))
      (H : F.ordinary ⟶ G.ordinary) (HF : F.filtered ⟶ G.filtered),
      covariantLiftsTransformation F G H HF →
      (∀ (i : ℤ) (s t : Finset ℤ),
        whiskerLeft (ObjectProperty.ι (covariantSupport (PA := PA) (PB := PB) s t))
            (whiskerRight HF (PC.gr i)) ≫ (theta G i s t).hom =
          (theta F i s t).hom ≫ biproduct.map
            (fun q : Diagonal i s t ↦ whiskerLeft
              (ObjectProperty.ι (covariantSupport (PA := PA) (PB := PB) s t) ⋙
                ((PA.gr q.val.1)).prod (PB.gr q.val.2)) H)) ∧
      (IsIso H → IsIso HF)) := by
  sorry

/-- An exact contravariant-first bifiltered lift, with its natural forgetful comparison.
The bounds hold for all finite intervals, using derived vanishing of the grades.
Source: Varshavsky 5.1.3(c),(d)
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
structure ContravariantLift where
  ordinary : EAᵒᵖ × EB ⥤ EC
  filtered : DAᵒᵖ × DB ⥤ DC
  [ordinary_left_shift : ∀ M : EAᵒᵖ, ((curry.obj ordinary).obj M).CommShift ℤ]
  [ordinary_right_shift : ∀ N : EB, ((curry.obj ordinary).flip.obj N).CommShift ℤ]
  [filtered_left_shift : ∀ M : DAᵒᵖ, ((curry.obj filtered).obj M).CommShift ℤ]
  [filtered_right_shift : ∀ N : DB, ((curry.obj filtered).flip.obj N).CommShift ℤ]
  ordinary_left_exact : ∀ M : EAᵒᵖ, ((curry.obj ordinary).obj M).IsTriangulated
  ordinary_right_exact : ∀ N : EB, ((curry.obj ordinary).flip.obj N).IsTriangulated
  filtered_left_exact : ∀ M : DAᵒᵖ, ((curry.obj filtered).obj M).IsTriangulated
  filtered_right_exact : ∀ N : DB, ((curry.obj filtered).flip.obj N).IsTriangulated
  phi : filtered ⋙ PC.omega ≅ (PA.omega.op).prod PB.omega ⋙ ordinary
  interval : ∀ (a b c d : ℤ) (M : DAᵒᵖ) (N : DB),
    (∀ p : ℤ, p < a ∨ b < p → IsZero ((PA.gr p).obj M.unop)) →
    (∀ p : ℤ, p < c ∨ d < p → IsZero ((PB.gr p).obj N)) →
    ∀ p : ℤ, p < -b + c ∨ -a + d < p →
      IsZero ((PC.gr p).obj (filtered.obj (M, N)))

/-- The full domain of pairs with the indicated finite signed grade supports.
The first set indexes `gr^(-j)`; it is reflected only in the contravariant case.
Source: Varshavsky Lemma 5.1.4(i)
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
def contravariantSupport (s t : Finset ℤ) : ObjectProperty (DAᵒᵖ × DB) := fun M ↦
  (∀ p : ℤ, p ∉ s → IsZero ((PA.gr (-p)).obj M.1.unop)) ∧ SupportedOn PB t M.2

/-- A single graded summand on the full supported-pair domain.
Source: Varshavsky Lemma 5.1.4(i)
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
def contravariantSummand (F : ContravariantLift (PA := PA) (PB := PB) (PC := PC))
    (s t : Finset ℤ) (j k : ℤ) :
    (contravariantSupport (PA := PA) (PB := PB) s t).FullSubcategory ⥤ EC :=
  ObjectProperty.ι _ ⋙ ((PA.gr (-j)).op).prod (PB.gr k) ⋙ F.ordinary

/-- The finite diagonal biproduct of the actual graded bifunctor values.
Source: Varshavsky Lemma 5.1.4(i)
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
def contravariantSum (F : ContravariantLift (PA := PA) (PB := PB) (PC := PC))
    (i : ℤ) (s t : Finset ℤ) :
    (contravariantSupport (PA := PA) (PB := PB) s t).FullSubcategory ⥤ EC :=
  biproduct (fun q : Diagonal i s t ↦ contravariantSummand F s t q.val.1 q.val.2)

/-- A supplied filtered transformation lifts the ordinary one exactly when its
natural forgetful square commutes. No arbitrary transformation is given a lift.
Source: Varshavsky 5.1.3(e)
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
def contravariantLiftsTransformation
    (F G : ContravariantLift (PA := PA) (PB := PB) (PC := PC))
    (H : F.ordinary ⟶ G.ordinary) (HF : F.filtered ⟶ G.filtered) : Prop :=
  whiskerRight HF PC.omega ≫ G.phi.hom =
    F.phi.hom ≫ whiskerLeft ((PA.omega.op).prod PB.omega) H

/-- The contravariant-first graded comparison, its normalization by the specified phi,
and its compatibility with supplied transformations, including iso detection.
Natural isomorphisms on each full supported domain express naturality in both inputs.
Their components are independent of the finite supports used to display the sum.
The fully faithful domain embeddings and truncation closure include bounded,
one-sided and full triangulated-domain variants in this same assertion.

Source: Varshavsky 5.1.3(c)--(e), Lemma 5.1.4(i)--(iii), pp.39--41.
Proof:
1. For j+k=i apply the exact grade functor to the two truncation triangles of
   lem-trf-filtered-unbounded-truncation. Use high(-j) and low(k+1) as cutoff inputs.
   The interval inequality kills each discarded term. The zero-cone criterion
   identifies the cutoff value with the value on the pure input pair.
2. On the pure output grade i equals forgetting. Apply phi there, and the
   canonical pure identifications of the two inputs, to identify each cutoff
   value with G(gr^(-j),gr^k). These are natural identifications.
3. The first-variable high inclusion, reversed by contravariance,
   and the second-variable low quotient give the comparison to the sum of cutoff values. Only
   finitely many input grades occur. Work with common finite supports on each
   finite diagram; adding zero summands changes no component. Cutoff maps
   commute with shifts and cone triangles. Finite sums of distinguished triangles
   are distinguished (lem-weil-finite-sums-distinguished-triangles).
4. On pure pairs the comparison is phi and all other summands vanish. Induct first
   on the second filtration width for a pure first input and then on the first
   width, splitting off the top grade by the truncation triangle. Use
   lem-sf-triangle-morphism-iso to conclude invertibility. Reverse the image
   triangle in the contravariant variable. This constructs theta with the stated
   pure normalization and support independence.
5. For a supplied transformation, naturality with the cutoff maps gives the
   square before inversion. Naturality with the pure-to-cut maps and the given
   phi square give its component formula after inversion. Summing proves the
   displayed natural-transformation identity.
6. If H is invertible, that identity makes every graded HF invertible. Its cone
   has all grades zero; a uniformly finite representative maps to zero by a
   graded quasi-isomorphism. It is zero in the localization. The zero-cone
   criterion implies HF is invertible, with natural component inverses.
7. Full domain embeddings preserve these maps and inverses. Truncation closure
   retains every cut and pure input; exactness retains cone triangles. Bounded
   and one-sided full embeddings follow from
   lem-trf-filtered-bounded-localization-comparison. The induction is in finite
   filtration width and imposes no cochain boundedness.
(blueprint: lem-trf-filtered-bifunctor-graded-comparison). -/
theorem filteredBifunctorGradedComparison_contravariant_first :
    (∀ M : DAᵒᵖ, ∃ s : Finset ℤ,
      ∀ p : ℤ, p ∉ s → IsZero ((PA.gr (-p)).obj M.unop)) ∧
    (∀ N : DB, ∃ t : Finset ℤ, SupportedOn PB t N) ∧
    ∃ theta : ∀ (F : ContravariantLift (PA := PA) (PB := PB) (PC := PC))
      (i : ℤ) (s t : Finset ℤ),
      ObjectProperty.ι (contravariantSupport (PA := PA) (PB := PB) s t) ⋙
        F.filtered ⋙ PC.gr i ≅ contravariantSum F i s t,
    (∀ (F : ContravariantLift (PA := PA) (PB := PB) (PC := PC))
      (i : ℤ) (s t : Finset ℤ)
      (X : (contravariantSupport (PA := PA) (PB := PB) s t).FullSubcategory)
      (q : Diagonal i s t)
      (TM : HighCut PA (-q.val.1) X.obj.1.unop)
      (TN : LowCut PB q.val.2 X.obj.2)
      (e : (PC.gr i).obj (F.filtered.obj (Opposite.op TM.pure, TN.pure)) ≅
        (PC.gr i).obj (F.filtered.obj (Opposite.op TM.cut, TN.cut)))
      (_he : e.hom = (PC.gr i).map
        (F.filtered.map (TM.quotient.op ×ₘ TN.inclusion)))
      (hOut : ∀ p : ℤ, p ≠ i → IsZero ((PC.gr p).obj
        (F.filtered.obj (Opposite.op TM.pure, TN.pure)))),
      (theta F i s t).hom.app X ≫
          (biproduct.π (fun r : Diagonal i s t ↦
            contravariantSummand F s t r.val.1 r.val.2) q).app X =
        (PC.gr i).map (F.filtered.map
          (TM.inclusion.op ×ₘ TN.quotient)) ≫ e.inv ≫
          (PC.pureComparison i
            (F.filtered.obj (Opposite.op TM.pure, TN.pure)) hOut).hom ≫
          F.phi.hom.app (Opposite.op TM.pure, TN.pure) ≫
          F.ordinary.map (TM.pureToGrade.inv.op ×ₘ TN.pureToGrade.hom)) ∧
    (∀ (F : ContravariantLift (PA := PA) (PB := PB) (PC := PC))
      (i : ℤ) (s t : Finset ℤ)
      (X : (contravariantSupport (PA := PA) (PB := PB) s t).FullSubcategory)
      (q : Diagonal i s t)
      (hM : ∀ p : ℤ, p ≠ (-q.val.1) → IsZero ((PA.gr p).obj X.obj.1.unop))
      (hN : ∀ p : ℤ, p ≠ q.val.2 → IsZero ((PB.gr p).obj X.obj.2))
      (hOut : ∀ p : ℤ, p ≠ i → IsZero ((PC.gr p).obj (F.filtered.obj X.obj))),
      (theta F i s t).hom.app X ≫
          (biproduct.π (fun q : Diagonal i s t ↦
            contravariantSummand F s t q.val.1 q.val.2) q).app X =
        (PC.pureComparison i (F.filtered.obj X.obj) hOut).hom ≫ F.phi.hom.app X.obj ≫
          F.ordinary.map
            ((PA.pureComparison (-q.val.1) X.obj.1.unop hM).hom.op ×ₘ
              (PB.pureComparison q.val.2 X.obj.2 hN).inv)) ∧
    (∀ (F : ContravariantLift (PA := PA) (PB := PB) (PC := PC))
      (i : ℤ) (s t s' t' : Finset ℤ)
      (X : (contravariantSupport (PA := PA) (PB := PB) s t).FullSubcategory)
      (X' : (contravariantSupport (PA := PA) (PB := PB) s' t').FullSubcategory)
      (hX : X.obj = X'.obj) (q : Diagonal i s t) (q' : Diagonal i s' t')
      (hq : q.val = q'.val),
      (theta F i s t).hom.app X ≫
          (biproduct.π (fun r : Diagonal i s t ↦
            contravariantSummand F s t r.val.1 r.val.2) q).app X ≫
          eqToHom (congrArg₂ (fun (r : ℤ × ℤ) (Y : DAᵒᵖ × DB) ↦
            F.ordinary.obj (Opposite.op ((PA.gr (-r.1)).obj Y.1.unop),
              (PB.gr r.2).obj Y.2)) hq hX) =
        eqToHom (congrArg (fun Z ↦ (PC.gr i).obj (F.filtered.obj Z)) hX) ≫
          (theta F i s' t').hom.app X' ≫
          (biproduct.π (fun r : Diagonal i s' t' ↦
            contravariantSummand F s' t' r.val.1 r.val.2) q').app X') ∧
    (∀ (F G : ContravariantLift (PA := PA) (PB := PB) (PC := PC))
      (H : F.ordinary ⟶ G.ordinary) (HF : F.filtered ⟶ G.filtered),
      contravariantLiftsTransformation F G H HF →
      (∀ (i : ℤ) (s t : Finset ℤ),
        whiskerLeft (ObjectProperty.ι (contravariantSupport (PA := PA) (PB := PB) s t))
            (whiskerRight HF (PC.gr i)) ≫ (theta G i s t).hom =
          (theta F i s t).hom ≫ biproduct.map
            (fun q : Diagonal i s t ↦ whiskerLeft
              (ObjectProperty.ι (contravariantSupport (PA := PA) (PB := PB) s t) ⋙
                ((PA.gr (-q.val.1)).op).prod (PB.gr q.val.2)) H)) ∧
      (IsIso H → IsIso HF)) := by
  sorry

end CategoryTheory.FilteredBifunctor
