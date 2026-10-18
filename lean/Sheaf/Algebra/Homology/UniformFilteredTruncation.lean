/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Sheaf.Algebra.Homology.UniformFiniteFilteredLocalization
public import Sheaf.Algebra.Homology.FilteredDerivedHomCalculus
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Unbounded uniformly finite filtered truncation calculus

Source: Varshavsky, Lefschetz--Verdier trace formula, §§5.1.1--5.1.2, pp. 39--40
(blueprint: lem-trf-filtered-unbounded-truncation).

The model is the existing localization of uniformly finite filtered cochain complexes,
with its cone triangulation. The functors and structure maps are fixed on representatives.
No model or functor is chosen from the existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.UniformFiltered

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The existing unbounded uniformly finite filtered complex category.
Source: Varshavsky 5.1.1(a) (blueprint: lem-trf-filtered-unbounded-truncation). -/
abbrev Complexes (C : Type u) [Category.{v} C] [Abelian C] :=
  UniformFilteredComplexes C none (fun _ ↦ True)

/-- The existing localization at graded quasi-isomorphisms, without cochain bounds.
Source: Varshavsky 5.1.2(a) (blueprint: lem-trf-filtered-unbounded-truncation). -/
abbrev Derived (C : Type u) [Category.{v} C] [Abelian C] :=
  UniformFilteredDerived C none (fun _ ↦ True)

/-- The localization functor, with the same objects and canonical filtered maps.
Source: Varshavsky 5.1.2(a) (blueprint: lem-trf-filtered-unbounded-truncation). -/
abbrev Q : Complexes C ⥤ Derived C := (uniformFilteredQuasiIso none (fun _ ↦ True)).Q

/-- View a uniform filtered complex as a finite filtered object in the abelian
category of complexes. This uses the existing graded-map functor.
Source: Varshavsky 5.1.1(a),(d) (blueprint: lem-trf-filtered-unbounded-truncation). -/
def asFiltered : Complexes C ⥤ FiniteFilteredObjects (CochainComplex C ℤ) none false where
  obj K := ⟨K.obj, K.property.1, K.property.2.1, fun _ h ↦ Bool.noConfusion h⟩
  map f := ⟨f.hom⟩

/-- Forgetting (`none`) or taking the canonical graded complex (`some p`).
Source: Varshavsky 5.1.1(d) (blueprint: lem-trf-filtered-unbounded-truncation). -/
def evaluation (p : Option ℤ) : Complexes C ⥤ CochainComplex C ℤ :=
  asFiltered ⋙ filteredEvaluation (CochainComplex C ℤ) none false p

/-- Filtration subcomplex and quotient retain uniform finiteness.
Source: Varshavsky 5.1.1(b),(c).
Proof: intersect each step with F^r for the subcomplex and take its image in the
quotient for the quotient complex. At a common lower bound the step is the whole
object, and at a common upper bound it is zero. There is no cochain-degree bound.
(blueprint: lem-trf-filtered-unbounded-truncation). -/
theorem truncation_bounds (K : Complexes C) (r : ℤ) :
    uniformFilteredProperty none (fun _ ↦ True)
      (CochainComplex.FiniteFiltered.highObject K.obj r) ∧
    uniformFilteredProperty none (fun _ ↦ True)
      (CochainComplex.FiniteFiltered.lowObject K.obj r) := by
  sorry

/-- The filtration subcomplex with its induced filtration.
Source: Varshavsky 5.1.1(c) (blueprint: lem-trf-filtered-unbounded-truncation). -/
def highRepresentative (K : Complexes C) (r : ℤ) : Complexes C :=
  ⟨CochainComplex.FiniteFiltered.highObject K.obj r, (truncation_bounds K r).1⟩

/-- The quotient with its image filtration.
Source: Varshavsky 5.1.1(c) (blueprint: lem-trf-filtered-unbounded-truncation). -/
def lowRepresentative (K : Complexes C) (r : ℤ) : Complexes C :=
  ⟨CochainComplex.FiniteFiltered.lowObject K.obj r, (truncation_bounds K r).2⟩

/-- The actual subcomplex inclusion, using the existing canonical factorization.
Source: Varshavsky 5.1.2(c) (blueprint: lem-trf-filtered-unbounded-truncation). -/
def highInclusion (K : Complexes C) (r : ℤ) : highRepresentative K r ⟶ K :=
  ⟨⟨(K.obj.filtration.step r).arrow,
    (CochainComplex.FiniteFiltered.truncation_maps K.obj r).1⟩⟩

/-- The actual quotient projection, using the existing canonical factorization.
Source: Varshavsky 5.1.2(c) (blueprint: lem-trf-filtered-unbounded-truncation). -/
def lowProjection (K : Complexes C) (r : ℤ) : K ⟶ lowRepresentative K r :=
  ⟨⟨cokernel.π (K.obj.filtration.step r).arrow,
    (CochainComplex.FiniteFiltered.truncation_maps K.obj r).2⟩⟩

section Cone

variable [HasShift (Derived C) ℤ]

/-- A shifted representative has the shifted filtration on every cochain term.
Source: Varshavsky 5.1.1(e) (blueprint: lem-trf-filtered-unbounded-truncation). -/
structure ShiftRepresentative (K : Complexes C) where
  complex : Complexes C
  underlying : complex.obj.obj ≅ K.obj.obj⟦(1 : ℤ)⟧
  filtration : ∀ p n : ℤ,
    imageSubobject ((complex.obj.filtration.F p).arrow.f n ≫ underlying.hom.f n) =
      imageSubobject (((shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).map
        (K.obj.filtration.F p).arrow).f n)

/-- Cone triangles are precisely the images of actual filtered mapping cones.
The filtration and the sign of the connecting arrow are both specified.
Source: Varshavsky 5.1.2(a),(c) (blueprint: lem-trf-filtered-unbounded-truncation). -/
def IsConeTriangle (S : ∀ K : Complexes C, ShiftRepresentative K)
    (s : ∀ K : Complexes C, Q.obj (S K).complex ≅ (Q.obj K)⟦(1 : ℤ)⟧)
    (T : Triangle (Derived C)) : Prop :=
  ∃ (K L M : Complexes C) (f : K ⟶ L) (g : L ⟶ M) (h : M ⟶ (S K).complex)
    (e : M.obj.obj ≅ CochainComplex.mappingCone f.hom.hom),
    (∀ p n : ℤ,
      imageSubobject ((M.obj.filtration.F p).arrow.f n ≫ e.hom.f n) =
        imageSubobject ((K.obj.filtration.F p).arrow.f (n + 1) ≫
          (CochainComplex.mappingCone.inl f.hom.hom).v (n + 1) n (by omega)) ⊔
        imageSubobject ((L.obj.filtration.F p).arrow.f n ≫
          (CochainComplex.mappingCone.inr f.hom.hom).f n)) ∧
    g.hom.hom ≫ e.hom = CochainComplex.mappingCone.inr f.hom.hom ∧
    h.hom.hom ≫ (S K).underlying.hom =
      e.hom ≫ (CochainComplex.mappingCone.triangle f.hom.hom).mor₃ ∧
    Nonempty (T ≅ Triangle.mk (Q.map f) (Q.map g) (Q.map h ≫ (s K).hom))

end Cone

variable [HasDerivedCategory.{w} C]

/-- The canonical unbounded filtered derived calculus, specified on the actual
localization and on its representatives. All structure is data, never a choice
from an unproved existence assertion. The Hom bijections and their canonical maps
specify the adjunctions and hence the truncation functors uniquely.
Source: Varshavsky §§5.1.1--5.1.2 (blueprint: lem-trf-filtered-unbounded-truncation). -/
class Model (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] where
  [preadditive : Preadditive (Derived C)]
  [zero : HasZeroObject (Derived C)]
  [shift : HasShift (Derived C) ℤ]
  [shift_additive : ∀ n : ℤ, (shiftFunctor (Derived C) n).Additive]
  [pretriangulated : Pretriangulated (Derived C)]
  [triangulated : IsTriangulated (Derived C)]
  shiftComplex : ∀ K : Complexes C, ShiftRepresentative K
  shiftComparison : ∀ K : Complexes C,
    Q.obj (shiftComplex K).complex ≅ (Q.obj K)⟦(1 : ℤ)⟧
  coneTriangles : ∀ T : Triangle (Derived C),
    T ∈ distTriang (Derived C) ↔ IsConeTriangle shiftComplex shiftComparison T
  omega : Derived C ⥤ DerivedCategory C
  gr : ℤ → Derived C ⥤ DerivedCategory C
  [omega_shift : omega.CommShift ℤ]
  [gr_shift : ∀ p : ℤ, (gr p).CommShift ℤ]
  [omega_exact : omega.IsTriangulated]
  [gr_exact : ∀ p : ℤ, (gr p).IsTriangulated]
  omegaComparison : Q ⋙ omega ≅ evaluation none ⋙ DerivedCategory.Q
  grComparison : ∀ p : ℤ, Q ⋙ gr p ≅ evaluation (some p) ⋙ DerivedCategory.Q
  high : ℤ → Derived C ⥤ Derived C
  low : ℤ → Derived C ⥤ Derived C
  [high_shift : ∀ p : ℤ, (high p).CommShift ℤ]
  [low_shift : ∀ p : ℤ, (low p).CommShift ℤ]
  [high_exact : ∀ p : ℤ, (high p).IsTriangulated]
  [low_exact : ∀ p : ℤ, (low p).IsTriangulated]
  inclusion : ∀ p : ℤ, high p ⟶ 𝟭 _
  quotient : ∀ p : ℤ, 𝟭 _ ⟶ low p
  connecting : ∀ p : ℤ, low p ⟶ high p ⋙ shiftFunctor _ (1 : ℤ)
  distinguished : ∀ (p : ℤ) (M : Derived C),
    Triangle.mk ((inclusion p).app M) ((quotient p).app M) ((connecting p).app M) ∈
      distTriang (Derived C)
  high_support : ∀ (r p : ℤ) (M : Derived C), r > p → IsZero ((gr p).obj ((high r).obj M))
  low_support : ∀ (r p : ℤ) (M : Derived C), r ≤ p → IsZero ((gr p).obj ((low r).obj M))
  high_grade : ∀ (r p : ℤ), r ≤ p → (high r ⋙ gr p ≅ gr p)
  low_grade : ∀ (r p : ℤ), p < r → (low r ⋙ gr p ≅ gr p)
  high_grade_normalization : ∀ (r p : ℤ) (h : r ≤ p),
    (high_grade r p h).hom = Functor.whiskerRight (inclusion r) (gr p)
  low_grade_normalization : ∀ (r p : ℤ) (h : p < r),
    (low_grade r p h).inv = Functor.whiskerRight (quotient r) (gr p)
  unique_triangle : ∀ (p : ℤ) (M L R : Derived C)
    (i : L ⟶ M) (q : M ⟶ R) (d : R ⟶ L⟦(1 : ℤ)⟧),
    Triangle.mk i q d ∈ distTriang (Derived C) →
    (∀ a : ℤ, a < p → IsZero ((gr a).obj L)) →
    (∀ a : ℤ, p ≤ a → IsZero ((gr a).obj R)) →
    ∃! e : Triangle.mk ((inclusion p).app M) ((quotient p).app M)
        ((connecting p).app M) ≅ Triangle.mk i q d, e.hom.hom₂ = 𝟙 M
  high_hom_bijective : ∀ (r : ℤ) (L M : Derived C),
    (∀ p : ℤ, p < r → IsZero ((gr p).obj L)) →
    Function.Bijective (fun f : L ⟶ (high r).obj M ↦ f ≫ (inclusion r).app M)
  low_hom_bijective : ∀ (r : ℤ) (M R : Derived C),
    (∀ p : ℤ, r ≤ p → IsZero ((gr p).obj R)) →
    Function.Bijective (fun f : (low r).obj M ⟶ R ↦ (quotient r).app M ≫ f)
  highComparison : ∀ (r : ℤ) (K : Complexes C),
    (high r).obj (Q.obj K) ≅ Q.obj (highRepresentative K r)
  lowComparison : ∀ (r : ℤ) (K : Complexes C),
    (low r).obj (Q.obj K) ≅ Q.obj (lowRepresentative K r)
  highNormalization : ∀ (r : ℤ) (K : Complexes C),
    (highComparison r K).hom ≫ Q.map (highInclusion K r) = (inclusion r).app (Q.obj K)
  lowNormalization : ∀ (r : ℤ) (K : Complexes C),
    (quotient r).app (Q.obj K) ≫ (lowComparison r K).hom = Q.map (lowProjection K r)
  grade_truncation : ∀ p : ℤ, low (p + 1) ⋙ high p ⋙ omega ≅ gr p
  pureComparison : ∀ (p : ℤ) (M : Derived C),
    (∀ q : ℤ, q ≠ p → IsZero ((gr q).obj M)) → ((gr p).obj M ≅ omega.obj M)
  pureNaturality : ∀ (p : ℤ) {M N : Derived C}
    (hM : ∀ q : ℤ, q ≠ p → IsZero ((gr q).obj M))
    (hN : ∀ q : ℤ, q ≠ p → IsZero ((gr q).obj N)) (f : M ⟶ N),
    (gr p).map f ≫ (pureComparison p N hN).hom =
      (pureComparison p M hM).hom ≫ omega.map f
  pureNormalization : ∀ (p : ℤ) (K : Complexes C),
    K.obj.filtration.F p = ⊤ → K.obj.filtration.F (p + 1) = ⊥ →
    ∀ hK : ∀ q : ℤ, q ≠ p → IsZero ((gr q).obj (Q.obj K)),
      DerivedCategory.Q.map (K.obj.filtration.F p).arrow =
        DerivedCategory.Q.map (cokernel.π (Subobject.ofLE _ _
          (K.obj.filtration.F_succ_le p))) ≫ (grComparison p).inv.app K ≫
        (pureComparison p (Q.obj K) hK).hom ≫ omegaComparison.hom.app K
  pure_equivalence : ∀ p : ℤ,
    (ObjectProperty.ι (fun M : Derived C ↦
      ∀ q : ℤ, q ≠ p → IsZero ((gr q).obj M)) ⋙ omega).IsEquivalence
  pure_identity : ∀ p : ℤ,
    ObjectProperty.ι (fun M : Derived C ↦
      ∀ q : ℤ, q ≠ p → IsZero ((gr q).obj M)) ⋙ low (p + 1) ⋙ high p ≅
      ObjectProperty.ι (fun M : Derived C ↦
        ∀ q : ℤ, q ≠ p → IsZero ((gr q).obj M))

attribute [instance_reducible] Model.preadditive Model.shift Model.pretriangulated
  Model.omega_shift Model.gr_shift Model.high_shift Model.low_shift
attribute [instance] Model.preadditive Model.zero Model.shift Model.shift_additive
  Model.pretriangulated Model.triangulated Model.omega_shift Model.gr_shift
  Model.omega_exact Model.gr_exact Model.high_shift Model.low_shift Model.high_exact Model.low_exact

/-- The unbounded, uniformly finite localization has the canonical truncation calculus.
Source: Varshavsky §§5.1.1--5.1.2, pp.39--40.
Proof: filtered cochain shifts and cones with their direct-sum filtrations form the
filtered homotopy triangulation. Grading takes them to ordinary cone triangles;
graded-acyclic objects are a triangulated subcategory. Localizing this Verdier class
agrees with the chain-map localization by the filtered cylinder, and gives precisely
the cone-normalized triangulation. Forgetting inverts graded quasi-isomorphisms by
finite filtration induction. Grading inverts them by definition; both descend by
localization and retain exactness. Subcomplex and quotient truncations retain finite
filtration and preserve graded quasi-isomorphisms: on each grade they are either the
identity or zero. Their chain-level inclusions and projections descend. Filtered roofs
with disjoint grade supports give the two Hom bijections; the inverse constructions
are natural because inclusion and quotient commute with all filtered maps. Their
adjunctions make the cone triangle universal and unique with the identity on the
middle object. The single-grade subquotient is canonically the graded complex.
Putting an ordinary complex in a single filtration grade is inverse to forgetting
on the pure subcategory; the step inclusion and quotient normalize this equivalence.
(blueprint: lem-trf-filtered-unbounded-truncation). -/
theorem unbounded_truncation (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] : Nonempty (Model C) := by
  sorry

end CategoryTheory.UniformFiltered
