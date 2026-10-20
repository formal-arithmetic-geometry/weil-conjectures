/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.CategoryTheory.FiniteFiltrationInduction
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Presentations of the finite filtered bounded below derived category

Source: Varshavsky, Lefschetz--Verdier trace formula, Sections 5.1.1--5.1.3,
pp. 39--40 (blueprint: def-trf-finite-filtered-derived-presentation).

A presentation specifies a localization and its canonical structure maps. Factorization
conditions specify the forgetful and graded functors on objects AND morphisms. The cone
condition specifies the triangulation, including the cone filtration and the connecting map.
No category or functor is selected from a bare existence assertion.
-/

@[expose] public section

set_option autoImplicit false

universe w v u v' u'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.FiniteFilteredDerived

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- Uniformly finite filtered complexes whose underlying complex is bounded below.
Source: Varshavsky 5.1.1(a),(e)
(blueprint: def-trf-finite-filtered-derived-presentation). -/
abbrev Complexes := ObjectProperty.FullSubcategory
  (fun K : FilteredObject (CochainComplex C ℤ) ↦
    K.filtration.IsFinite ∧ CochainComplex.plus C K.obj)

/-- The actual graded quasi-isomorphisms, using the recorded filtration quotient maps.
Source: Varshavsky 5.1.2(a)
(blueprint: def-trf-finite-filtered-derived-presentation). -/
def gradedQuasiIso : MorphismProperty (Complexes C) :=
  fun {_ _} f ↦ ∀ p : ℤ, QuasiIso (FilteredObject.gradedMapSteps f.hom p)

/-- The concrete localization: formal strings of chain maps and inverses of graded
quasi-isomorphisms, modulo the category and inverse relations.
Source: Varshavsky 5.1.2(a)
(blueprint: def-trf-finite-filtered-derived-presentation). -/
abbrev Localization := (gradedQuasiIso C).Localization

/-- The canonical functor into the concrete finite-filtered localization.
Source: Varshavsky 5.1.2(a)
(blueprint: def-trf-finite-filtered-derived-presentation). -/
noncomputable def quotient : Complexes C ⥤ Localization C := (gradedQuasiIso C).Q

variable {C} {D : Type u'} [Category.{v'} D] [HasShift D ℤ]

/-- A representative of a shifted filtered complex, with the filtration transported
by the actual shift of complexes. The equation is degreewise, hence independent of
choices of representatives for subobjects.
Source: Varshavsky 5.1.1(a),(e)
(blueprint: def-trf-finite-filtered-derived-presentation). -/
structure ShiftRepresentative (K : Complexes C) where
  complex : Complexes C
  underlying : complex.obj.obj ≅ K.obj.obj⟦(1 : ℤ)⟧
  filtration : ∀ p n : ℤ,
    imageSubobject ((complex.obj.filtration.F p).arrow.f n ≫ underlying.hom.f n) =
      imageSubobject (((shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).map
        (K.obj.filtration.F p).arrow).f n)

/-- The cone triangle representatives have precisely the direct-sum cone filtration,
with the usual cochain cone maps. This predicate fixes the induced triangulation.
Source: Varshavsky 5.1.2(a),(c), filtered cone construction
(blueprint: def-trf-finite-filtered-derived-presentation). -/
def IsConeTriangle (Q : Complexes C ⥤ D)
    (S : ∀ K : Complexes C, ShiftRepresentative K)
    (s : ∀ K : Complexes C, Q.obj (S K).complex ≅ (Q.obj K)⟦(1 : ℤ)⟧)
    (T : Triangle D) : Prop :=
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

variable [HasDerivedCategory.{w} C]
variable [Preadditive D] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]

/-- A choice of presentation of `DF⁺(C)`, with its canonical forgetful/graded functors.
The localization property rules out an arbitrary category; the factorization equations
rule out arbitrary comparison functors; the cone predicate fixes the triangulation.
All sizes are explicit and independent. Source: Varshavsky 5.1.1--5.1.2
(blueprint: def-trf-finite-filtered-derived-presentation). -/
structure Presentation where
  Q : Complexes C ⥤ D
  localization : Q.IsLocalization (gradedQuasiIso C)
  shiftComplex : ∀ K : Complexes C, ShiftRepresentative K
  shiftComparison : ∀ K : Complexes C, Q.obj (shiftComplex K).complex ≅ (Q.obj K)⟦(1 : ℤ)⟧
  coneTriangles : ∀ T : Triangle D,
    T ∈ distTriang D ↔ IsConeTriangle Q shiftComplex shiftComparison T
  omega : D ⥤ DerivedCategory.Plus C
  gr : ℤ → D ⥤ DerivedCategory.Plus C
  [omegaShift : omega.CommShift ℤ]
  [grShift : ∀ p : ℤ, (gr p).CommShift ℤ]
  omegaExact : omega.IsTriangulated
  grExact : ∀ p : ℤ, (gr p).IsTriangulated
  omegaComplex : ∀ K : Complexes C,
    DerivedCategory.Plus.ι.obj (omega.obj (Q.obj K)) ≅ DerivedCategory.Q.obj K.obj.obj
  grComplex : ∀ (p : ℤ) (K : Complexes C),
    DerivedCategory.Plus.ι.obj ((gr p).obj (Q.obj K)) ≅
      DerivedCategory.Q.obj (K.obj.filtration.gradedPiece p)
  omegaNaturality : ∀ {K L : Complexes C} (f : K ⟶ L),
    DerivedCategory.Plus.ι.map (omega.map (Q.map f)) ≫ (omegaComplex L).hom =
      (omegaComplex K).hom ≫ DerivedCategory.Q.map f.hom.hom
  grNaturality : ∀ (p : ℤ) {K L : Complexes C} (f : K ⟶ L),
    DerivedCategory.Plus.ι.map ((gr p).map (Q.map f)) ≫ (grComplex p L).hom =
      (grComplex p K).hom ≫ DerivedCategory.Q.map (FilteredObject.gradedMapSteps f.hom p)
  pureComparison : ∀ (p : ℤ) (M : D),
    (∀ q : ℤ, q ≠ p → IsZero ((gr q).obj M)) → ((gr p).obj M ≅ omega.obj M)
  pureNaturality : ∀ (p : ℤ) {M N : D}
    (hM : ∀ q : ℤ, q ≠ p → IsZero ((gr q).obj M))
    (hN : ∀ q : ℤ, q ≠ p → IsZero ((gr q).obj N)) (f : M ⟶ N),
    (gr p).map f ≫ (pureComparison p N hN).hom =
      (pureComparison p M hM).hom ≫ omega.map f
  pureNormalization : ∀ (p : ℤ) (K : Complexes C),
    K.obj.filtration.F p = ⊤ → K.obj.filtration.F (p + 1) = ⊥ →
    ∀ hK : ∀ q : ℤ, q ≠ p → IsZero ((gr q).obj (Q.obj K)),
      DerivedCategory.Q.map (K.obj.filtration.F p).arrow =
        DerivedCategory.Q.map (cokernel.π (Subobject.ofLE _ _
          (K.obj.filtration.F_succ_le p))) ≫ (grComplex p K).inv ≫
        DerivedCategory.Plus.ι.map (pureComparison p (Q.obj K) hK).hom ≫
        (omegaComplex K).hom

attribute [instance] Presentation.localization Presentation.omegaShift Presentation.grShift
attribute [instance] Presentation.omegaExact Presentation.grExact

/-- Vanishing outside a finite filtration interval is derived vanishing, so acyclic
rather than literally zero graded complexes are included.
Source: Varshavsky 5.1.2(a),(b)
(blueprint: def-trf-finite-filtered-derived-presentation). -/
def Supported (P : Presentation (C := C) (D := D)) (a b : ℤ) (M : D) : Prop :=
  ∀ p : ℤ, p < a ∨ b < p → IsZero ((P.gr p).obj M)

end CategoryTheory.FiniteFilteredDerived
