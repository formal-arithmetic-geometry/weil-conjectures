/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Sheaf.CategoryTheory.SmallDgCategory

/-!
# Triangulation from the dg axioms A, B and C

Source: Stacks Project, `dga.tex`, section-review, Tags 09QJ, 09P6, 09QU and 09QY
(blueprint: def-coef-dg-abc-data).

## Main definitions

* `IntegralDGCategory.ABC.Shifts`: dg translations and the shifted-Hom identifications.
* `IntegralDGCategory.ABC.Admissible`: the five graded splitting identities.
* `IntegralDGCategory.ABC.Cone`: an admissible cone with the specified boundary.
* `IntegralDGCategory.ABC.TriangulatedRealization`: the normalized H⁰ category and its
  triangulation, including both descriptions of the distinguished triangles.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.IntegralDGCategory.ABC

/-- The degree-zero cycles in the actual Hom complex. Source: Stacks, section-review
(blueprint: def-coef-dg-abc-data). -/
abbrev Closed (A : IntegralDGCategory.{u, v}) (x y : A.Obj) :=
  ((A.hom x y).d 0 1).hom.ker

/-- Axiom (B), with chain maps on Hom complexes and strict dg functor laws.
The two composition equations specify the usual shifted-Hom compatibility, including
its Koszul sign. Source: Stacks, section-review, axiom (B)
(blueprint: def-coef-dg-abc-data). -/
structure Shifts (A : IntegralDGCategory.{u, v}) where
  obj : ℤ → A.Obj → A.Obj
  map (n : ℤ) (x y : A.Obj) : A.hom x y ⟶ A.hom (obj n x) (obj n y)
  map_unit (n : ℤ) (x : A.Obj) : (map n x x).f 0 (A.unit x) = A.unit (obj n x)
  map_comp (n : ℤ) (x y z : A.Obj) (p q : ℤ)
      (g : (A.hom y z).X p) (f : (A.hom x y).X q) :
    (map n x z).f (p + q) (A.comp p q g f) =
      A.comp p q ((map n y z).f p g) ((map n x y).f q f)
  obj_zero (x : A.Obj) : obj 0 x = x
  map_zero (x y : A.Obj) (p : ℤ) (f : (A.hom x y).X p) :
    HEq ((map 0 x y).f p f) f
  obj_add (n m : ℤ) (x : A.Obj) : obj (n + m) x = obj n (obj m x)
  map_add (n m : ℤ) (x y : A.Obj) (p : ℤ) (f : (A.hom x y).X p) :
    HEq ((map (n + m) x y).f p f)
      ((map n (obj m x) (obj m y)).f p ((map m x y).f p f))
  homShift (n : ℤ) (x y : A.Obj) : A.hom x (obj n y) ≅ (A.hom x y)⟦n⟧
  homShift_precomp (n : ℤ) (x y z : A.Obj) (p q : ℤ)
      (g : (A.hom y (obj n z)).X p) (f : (A.hom x y).X q) :
    HEq ((homShift n x z).hom.f (p + q) (A.comp p q g f))
      (A.comp (p + n) q ((homShift n y z).hom.f p g) f)
  homShift_postcomp (n : ℤ) (x y z : A.Obj) (p q : ℤ)
      (g : (A.hom y z).X p) (f : (A.hom x (obj n y)).X q) :
    HEq ((homShift n x z).hom.f (p + q)
      (A.comp p q ((map n y z).f p g) f))
      ((n * p).negOnePow • A.comp p (q + n) g ((homShift n x y).hom.f q f))

/-- An admissible sequence, with its graded splitting; inclusions and quotient maps
are cycles, whereas `π` and `s` need not be. Source: Stacks, section-review and Tag 09P6
(blueprint: def-coef-dg-abc-data). -/
structure Admissible (A : IntegralDGCategory.{u, v}) (x y z : A.Obj) where
  a : Closed A x y
  b : Closed A y z
  π : (A.hom y x).X 0
  s : (A.hom z y).X 0
  π_a : A.comp 0 0 π a.val = A.unit x
  b_s : A.comp 0 0 b.val s = A.unit z
  a_π_s_b : A.comp 0 0 a.val π + A.comp 0 0 s b.val = A.unit y
  b_a : A.comp 0 0 b.val a.val = 0
  π_s : A.comp 0 0 π s = 0

/-- A dg biproduct has four closed structure maps and the five biproduct equations.
Source: Stacks, section-review, axiom (A)
(blueprint: def-coef-dg-abc-data). -/
structure Biproduct (A : IntegralDGCategory.{u, v}) (x z : A.Obj) where
  obj : A.Obj
  inl : Closed A x obj
  inr : Closed A z obj
  fst : Closed A obj x
  snd : Closed A obj z
  fst_inl : A.comp 0 0 fst.val inl.val = A.unit x
  snd_inr : A.comp 0 0 snd.val inr.val = A.unit z
  fst_inr : A.comp 0 0 fst.val inr.val = 0
  snd_inl : A.comp 0 0 snd.val inl.val = 0
  total : A.comp 0 0 inl.val fst.val + A.comp 0 0 inr.val snd.val = A.unit obj

/-- Axiom (A): a zero dg object and a dg sum for every pair, with no boundedness
restriction. Source: Stacks, section-review
(blueprint: def-coef-dg-abc-data). -/
def AxiomA (A : IntegralDGCategory.{u, v}) : Prop :=
  (∃ o : A.Obj, ∀ (x : A.Obj) (n : ℤ),
    Subsingleton ((A.hom x o).X n) ∧ Subsingleton ((A.hom o x).X n)) ∧
    ∀ x z : A.Obj, Nonempty (Biproduct A x z)

/-- The actual degree-one boundary `π d(s)`, before applying the Hom-shift isomorphism.
Source: Stacks, Tag 09P6
(blueprint: def-coef-dg-abc-data). -/
def boundary {A : IntegralDGCategory.{u, v}} {x y z : A.Obj}
    (E : Admissible A x y z) : (A.hom z x).X 1 :=
  A.comp 0 1 E.π ((A.hom z y).d 0 1 E.s)

/-- A cone as in axiom (C), including the exact boundary equality with `f[1]`.
Source: Stacks, Tag 09QJ
(blueprint: def-coef-dg-abc-data). -/
structure Cone {A : IntegralDGCategory.{u, v}} (S : Shifts A) {x y : A.Obj}
    (f : Closed A x y) where
  obj : A.Obj
  sequence : Admissible A y obj (S.obj 1 x)
  boundary_eq : HEq ((S.homShift 1 (S.obj 1 x) y).hom.f 0 ((S.map 1 x y).f 0 f.val))
    (boundary sequence)

/-- A triangulated realization on the literal object set of `A`. The class map is
surjective and identifies exactly differences of boundaries, so this is precisely H⁰,
with its induced composition, addition and translations. The two final equivalences
fix all distinguished triangles, including the negative projection in cone triangles.
The structure is the theorem's conclusion, not an assumed replacement of H⁰.
Source: Stacks, Tags 09P6, 09QU, 09QY
(blueprint: def-coef-dg-abc-data). -/
structure TriangulatedRealization (A : IntegralDGCategory.{u, v}) (S : Shifts A) where
  [category : Category.{v} A.Obj]
  [preadditive : Preadditive A.Obj]
  [zero : HasZeroObject A.Obj]
  [shift : HasShift A.Obj ℤ]
  [shiftAdditive : ∀ n : ℤ, (shiftFunctor A.Obj n).Additive]
  [pretriangulated : Pretriangulated A.Obj]
  [triangulated : IsTriangulated A.Obj]
  classMap (x y : A.Obj) : Closed A x y →+ (x ⟶ y)
  class_surjective (x y : A.Obj) : Function.Surjective (classMap x y)
  class_eq (x y : A.Obj) (f g : Closed A x y) :
    classMap x y f = classMap x y g ↔
      ∃ h : (A.hom x y).X (-1), (A.hom x y).d (-1) 0 h = f.val - g.val
  class_identity (x : A.Obj) : classMap x x ⟨A.unit x, A.d_unit x⟩ = 𝟙 x
  class_comp (x y z : A.Obj) (f : Closed A x y) (g : Closed A y z)
      (h : Closed A x z) (hh : h.val = A.comp 0 0 g.val f.val) :
    classMap x z h = classMap x y f ≫ classMap y z g
  shift_obj (n : ℤ) (x : A.Obj) : (shiftFunctor A.Obj n).obj x = S.obj n x
  shift_map (n : ℤ) (x y : A.Obj) (f : Closed A x y)
      (g : Closed A (S.obj n x) (S.obj n y)) (hg : g.val = (S.map n x y).f 0 f.val) :
    HEq ((shiftFunctor A.Obj n).map (classMap x y f))
      (classMap (S.obj n x) (S.obj n y) g)
  admissible_iff (T : Triangle A.Obj) : T ∈ distTriang A.Obj ↔
    ∃ (x y z : A.Obj) (E : Admissible A x y z) (δ : Closed A z (S.obj 1 x)),
      HEq ((S.homShift 1 z x).hom.f 0 δ.val) (boundary E) ∧
      ∃ d : z ⟶ (shiftFunctor A.Obj (1 : ℤ)).obj x,
        HEq d (classMap z (S.obj 1 x) δ) ∧
        Nonempty (T ≅ Triangle.mk (classMap x y E.a) (classMap y z E.b) d)
  cone_iff (T : Triangle A.Obj) : T ∈ distTriang A.Obj ↔
    ∃ (x y : A.Obj) (f : Closed A x y) (K : Cone S f)
      (d : K.obj ⟶ (shiftFunctor A.Obj (1 : ℤ)).obj x),
      HEq d (-classMap K.obj (S.obj 1 x) K.sequence.b) ∧
      Nonempty (T ≅ Triangle.mk (classMap x y f) (classMap y K.obj K.sequence.a) d)

end CategoryTheory.IntegralDGCategory.ABC
