/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-!
# The vertical augmentation of the two-sided categorical bar complex

Source: Stacks Project, Cohomology on Sites, Tag 08Q9, last paragraph; Simplicial,
Tags 019M, 019S and 019Y; Homology, Tag 0132. The arbitrary-coefficient two-sided-bar
variant is spelled out in the DAG (blueprint: lem-trf-two-sided-bar-contractible-augmentation).

`Presentation` specifies the direct sums by their coproduct universal properties and
fixes every differential and augmentation on generators. The result asserts existence
of this presentation and applies to every such presentation; it never chooses an
unspecified complex or map from a postponed existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite Simplicial MonoidalCategory

namespace CategoryTheory.TwoSidedBar

variable {D : Type u} [SmallCategory D] {R : Type u} [CommRing R]

/-- Reindex a string by a simplex operator, composing across omitted vertices.
Source: Stacks 08Q9, explicit two-sided-bar variant
(blueprint: lem-trf-two-sided-bar-contractible-augmentation). -/
def stringReindex {m n : ℕ} (c : ComposableArrows D n) (α : ⦋m⦌ ⟶ ⦋n⦌) :
    ComposableArrows D m :=
  (SimplexCategory.toCat.map α).toFunctor ⋙ c

/-- The first-vertex coefficient map for a simplex operator.
Source: Stacks 08Q9, explicit two-sided-bar variant
(blueprint: lem-trf-two-sided-bar-contractible-augmentation). -/
def coefficient (F : D ⥤ ModuleCat.{u} R) {m n : ℕ}
    (c : ComposableArrows D n) (α : ⦋m⦌ ⟶ ⦋n⦌) :
    F.obj c.left ⟶ F.obj (stringReindex c α).left :=
  F.map (c.map (homOfLE (Fin.zero_le _)))

/-- The arrow from the last retained vertex to the original last vertex.
Source: Stacks 08Q9, explicit two-sided-bar variant
(blueprint: lem-trf-two-sided-bar-contractible-augmentation). -/
def lastMap {m n : ℕ} (c : ComposableArrows D n) (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (stringReindex c α).right ⟶ c.right :=
  c.map (homOfLE (Fin.le_last _))

/-- The representable evaluation `Hom(T,Q)` using the recorded simplicial-set notion.
Source: Stacks 08Q9 (blueprint: lem-trf-two-sided-bar-contractible-augmentation). -/
abbrev evaluation (Q : SimplicialObject D) (T : D) : SSet.{u} :=
  Q ⋙ coyoneda.obj (op T)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A presentation of exactly the displayed two-sided bar double complex, its category
bar target, and the two vertical summation maps. The coproduct conditions fix the terms,
and the formulas fix all differentials and maps. There are no homotopy or quasi-isomorphism
assumptions in this structure.
Source: Stacks 08Q9, explicit arbitrary-coefficient two-sided-bar variant; Homology 0132
(blueprint: lem-trf-two-sided-bar-contractible-augmentation). -/
structure Presentation (F : D ⥤ ModuleCat.{u} R) (Q : SimplicialObject D) where
  A : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℤ) (.up ℤ)
  B : CochainComplex (ModuleCat.{u} R) ℤ
  a : ∀ (p q : ℕ) (c : ComposableArrows D p) (_f : c.right ⟶ Q.obj (op ⦋q⦌)),
    F.obj c.left ⟶ (A.X (-↑p)).X (-↑q)
  b : ∀ (p : ℕ) (c : ComposableArrows D p), F.obj c.left ⟶ B.X (-↑p)
  aCoproduct : ∀ p q : ℕ,
    IsColimit (Cofan.mk ((A.X (-↑p)).X (-↑q))
      (fun s : Σ c : ComposableArrows D p, c.right ⟶ Q.obj (op ⦋q⦌) ↦ a p q s.1 s.2))
  bCoproduct : ∀ p : ℕ,
    IsColimit (Cofan.mk (B.X (-↑p)) (fun c : ComposableArrows D p ↦ b p c))
  aPositive : ∀ i j : ℤ, 0 < i ∨ 0 < j → IsZero ((A.X i).X j)
  bPositive : ∀ i : ℤ, 0 < i → IsZero (B.X i)
  verticalOperator : ∀ (p m n : ℕ) (_α : ⦋m⦌ ⟶ ⦋n⦌),
    (A.X (-↑p)).X (-↑n) ⟶ (A.X (-↑p)).X (-↑m)
  verticalOperatorFormula : ∀ (p m n : ℕ) (α : ⦋m⦌ ⟶ ⦋n⦌)
    (c : ComposableArrows D p) (f : c.right ⟶ Q.obj (op ⦋n⦌)),
    a p n c f ≫ verticalOperator p m n α = a p m c (f ≫ Q.map α.op)
  horizontal : ∀ (p q : ℕ) (c : ComposableArrows D (p + 1))
    (f : c.right ⟶ Q.obj (op ⦋q⦌)),
    a (p + 1) q c f ≫ (A.d (-↑(p + 1)) (-↑p)).f (-↑q) =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
        (coefficient F c (SimplexCategory.δ j) ≫
          a p q (stringReindex c (SimplexCategory.δ j))
            (lastMap c (SimplexCategory.δ j) ≫ f))
  vertical : ∀ (p q : ℕ) (c : ComposableArrows D p)
    (f : c.right ⟶ Q.obj (op ⦋q + 1⦌)),
    a p (q + 1) c f ≫ (A.X (-↑p)).d (-↑(q + 1)) (-↑q) =
      ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val • a p q c (f ≫ Q.δ j)
  barDifferential : ∀ (p : ℕ) (c : ComposableArrows D (p + 1)),
    b (p + 1) c ≫ B.d (-↑(p + 1)) (-↑p) =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
        (coefficient F c (SimplexCategory.δ j) ≫ b p (stringReindex c (SimplexCategory.δ j)))
  column : ∀ p : ℕ, A.X (-↑p) ⟶ (CochainComplex.singleFunctor _ 0).obj (B.X (-↑p))
  columnFormula : ∀ (p : ℕ) (c : ComposableArrows D p)
    (f : c.right ⟶ Q.obj (op ⦋0⦌)),
    a p 0 c f ≫ (column p).f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (B.X (-↑p))).hom = b p c
  [hasTotal : A.HasTotal (.up ℤ)]
  augmentation : A.total (.up ℤ) ⟶ B
  augmentationFormula : ∀ (p : ℕ) (c : ComposableArrows D p)
    (f : c.right ⟶ Q.obj (op ⦋0⦌)),
    a p 0 c f ≫ A.ιTotalOrZero (.up ℤ) (-↑p) 0 (-↑p) ≫
      augmentation.f (-↑p) = b p c
  augmentationOffEdge : ∀ (i j n : ℤ), j ≠ 0 →
    A.ιTotalOrZero (.up ℤ) i j n ≫ augmentation.f n = 0

attribute [instance] Presentation.hasTotal

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A coefficient summation augmentation, together with its explicitly normalized
free-chain tensor description. This specifies the maps, without assuming equivalence
or flatness. Source: Stacks 08Q9, arbitrary-coefficient variant
(blueprint: lem-trf-two-sided-bar-contractible-augmentation). -/
structure CoefficientAugmentation (X : SSet.{u}) (M : ModuleCat.{u} R) where
  augmentation : X.chainComplex M ⟶ (ChainComplex.single₀ _).obj M
  sumFormula : ∀ (x : X.obj (op ⦋0⦌)),
    X.ιChainComplex x ≫ augmentation.f 0 = 𝟙 M
  freeAugmentation : X.chainComplex (ModuleCat.of R R) ⟶
    (ChainComplex.single₀ _).obj (ModuleCat.of R R)
  freeSumFormula : ∀ (x : X.obj (op ⦋0⦌)),
    X.ιChainComplex x ≫ freeAugmentation.f 0 = 𝟙 (ModuleCat.of R R)
  tensorIso :
    ((((tensoringRight (ModuleCat.{u} R)).obj M).mapHomologicalComplex (.down ℕ)).obj
      (X.chainComplex (ModuleCat.of R R))) ≅ X.chainComplex M
  tensorFormula : ∀ (n : ℕ) (x : X.obj (op ⦋n⦌)) (m : M),
    (tensorIso.hom.f n)
      ((X.ιChainComplex (R := ModuleCat.of R R) x (1 : R)) ⊗ₜ[R] m) =
        X.ιChainComplex (R := M) x m
  tensorAugmentation : ∀ (z : (X.chainComplex (ModuleCat.of R R)).X 0) (m : M),
    augmentation.f 0 ((tensorIso.hom.f 0) (z ⊗ₜ[R] m)) =
      (freeAugmentation.f 0 z) • m

/-- Tensor an actual chain homotopy, preserving its equations without a flatness
hypothesis. This is Mathlib's additive-functor operation, specialized to modules.
Source: Stacks 08Q9, arbitrary-coefficient variant, proof step 4
(blueprint: lem-trf-two-sided-bar-contractible-augmentation). -/
def tensorHomotopy (M : ModuleCat.{u} R) {K L : ChainComplex (ModuleCat.{u} R) ℕ}
    {f g : K ⟶ L} (h : Homotopy f g) :
    Homotopy
      ((((tensoringRight (ModuleCat.{u} R)).obj M).mapHomologicalComplex (.down ℕ)).map f)
      ((((tensoringRight (ModuleCat.{u} R)).obj M).mapHomologicalComplex (.down ℕ)).map g) :=
  ((tensoringRight (ModuleCat.{u} R)).obj M).mapHomotopy h

/-- Tensor a chosen chain homotopy equivalence, including each of its two homotopy
identities. It applies to the singleton contraction and to the equivalence obtained
from any chosen finite simplicial homotopy zigzags.
Source: Stacks 08Q9, arbitrary-coefficient variant, proof step 4
(blueprint: lem-trf-two-sided-bar-contractible-augmentation). -/
def tensorEquivalence (M : ModuleCat.{u} R) {K L : ChainComplex (ModuleCat.{u} R) ℕ}
    (e : HomotopyEquiv K L) :
    HomotopyEquiv
      ((((tensoringRight (ModuleCat.{u} R)).obj M).mapHomologicalComplex (.down ℕ)).obj K)
      ((((tensoringRight (ModuleCat.{u} R)).obj M).mapHomologicalComplex (.down ℕ)).obj L) :=
  ((tensoringRight (ModuleCat.{u} R)).obj M).mapHomotopyEquiv e

/-- The full vertical augmentation statement, including the arbitrary coefficient
contractions, singleton parity homotopy, direct-sum column equivalences, and the
specific total augmentation in the derived category.
Source: Stacks 08Q9, last paragraph, Simplicial 019M/019S/019Y and Homology 0132
(blueprint: lem-trf-two-sided-bar-contractible-augmentation).

Proof: (1) Identify each summand of free chains tensored with M by
`[x] tensor m ↦ inclusion_x m`; its inverse sums the finitely supported coefficients.
Both maps commute with faces and identify the summation augmentations.
(2) Choose the simplicial inverse to the singleton map. Apply
lem-weil-pbc-simplicial-homotopy-free-chain-homotopy to every cylinder homotopy
in its finite zigzags, reversing by negation and concatenating by addition.
This gives `1-C(v)C(u)=dH+Hd` and `C(u)C(v)=1`.
(3) The singleton differential is identity in positive even degrees and zero in
odd degrees. Its identity degree-zero section and homotopy identity in odd degrees,
zero in even degrees, satisfy `1-jt=dk+kd`, also at degree zero.
Combining with (2) gives inverse `C(v)j` and homotopy `H+C(v)kC(u)`.
(4) Tensor every map and identity with M. Additivity and functoriality preserve
the homotopy equations; no tensor exactness or flatness is used. For each p,
take direct sums over the strings; finite support makes the inverse and homotopy
well-defined, and the augmentation is exactly `Presentation.column`.
(5) Category composition and functoriality give the horizontal bar identities;
the operators of Q give the vertical identities, commuting with the horizontal ones.
Forgetting f commutes with horizontal faces. At q=1 its two vertical faces agree,
so their alternating sum is zero. These facts construct the stated presentation.
The total sign is `(-1)^(-p)=(-1)^p`; only p+q=n contributes to degree -n.
(6) Apply lem-pc-bounded-above-double-complex-total-comparison with bounds zero
to the column augmentations. The target is B placed in vertical degree zero.
Its total identifies with B, and the total map is the specified augmentation.
Localization at quasi-isomorphisms makes this particular map an isomorphism.
-/
theorem contractible_vertical_augmentation
    (F : D ⥤ ModuleCat.{u} R) (Q : SimplicialObject D)
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (hQ : ∀ T : D,
      ∃ (f : evaluation Q T ⟶ (SimplicialObject.const (Type u)).obj PUnit)
        (g : (SimplicialObject.const (Type u)).obj PUnit ⟶ evaluation Q T),
        Relation.EqvGen (fun a b ↦ Nonempty (SSet.Homotopy a b)) (f ≫ g) (𝟙 _) ∧
        Relation.EqvGen (fun a b ↦ Nonempty (SSet.Homotopy a b)) (g ≫ f) (𝟙 _)) :
    Nonempty (Presentation F Q) ∧
    (∀ P : Presentation F Q,
      (∀ p : ℕ, ∃ e : HomotopyEquiv (P.A.X (-↑p))
          ((CochainComplex.singleFunctor _ 0).obj (P.B.X (-↑p))),
        e.hom = P.column p) ∧
      QuasiIso P.augmentation ∧ IsIso (DerivedCategory.Q.map P.augmentation)) ∧
    (∀ (p : ℕ) (c : ComposableArrows D p) (M : ModuleCat.{u} R),
      ∃ a : CoefficientAugmentation (evaluation Q c.right) M,
        (∃ e : HomotopyEquiv ((evaluation Q c.right).chainComplex M)
            ((ChainComplex.single₀ _).obj M), e.hom = a.augmentation) ∧
        (∃ e : HomotopyEquiv
            ((evaluation Q c.right).chainComplex (ModuleCat.of R R))
            ((ChainComplex.single₀ _).obj (ModuleCat.of R R)),
          e.hom = a.freeAugmentation)) ∧
    (∀ M : ModuleCat.{u} R,
      ∃ (t : ChainComplex.alternatingConst.obj M ⟶ (ChainComplex.single₀ _).obj M)
        (j : (ChainComplex.single₀ _).obj M ⟶ ChainComplex.alternatingConst.obj M)
        (k : Homotopy (𝟙 (ChainComplex.alternatingConst.obj M)) (t ≫ j)),
        t.f 0 = 𝟙 M ∧ j.f 0 = 𝟙 M ∧ j ≫ t = 𝟙 _ ∧
        (∀ n : ℕ, k.hom n (n + 1) = if Odd n then 𝟙 M else 0)) ∧
    (∀ n : ℤ, Set.Finite {ij : ℤ × ℤ | ij.1 ≤ 0 ∧ ij.2 ≤ 0 ∧ ij.1 + ij.2 = n}) := by
  sorry

end CategoryTheory.TwoSidedBar
