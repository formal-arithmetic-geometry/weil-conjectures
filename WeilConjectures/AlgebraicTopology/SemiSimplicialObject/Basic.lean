/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Semi-simplicial objects

A semi-simplicial object `U` in a category `C` consists of objects `U.obj n` for `n : ℕ` and face
maps `U.δ n i : U.obj (n + 1) ⟶ U.obj n` for `i : Fin (n + 2)`, satisfying the simplicial
identities `δ_{j + 1} ≫ δ_i = δ_i ≫ δ_j` for `i ≤ j`. Unlike a simplicial object it has no
degeneracy maps. (Mathlib has the semi-simplex category but no semi-simplicial objects yet; we use
this concrete presentation since it makes inductive constructions straightforward.)

We define:

- `CategoryTheory.SemiSimplicialObject`: semi-simplicial objects, and their morphisms;
- `CategoryTheory.SemiSimplicialObject.Compatible`: a family `x : Fin (n + 2) → (W ⟶ U.obj n)`
  satisfying the simplicial identities, i.e. the boundary of a would-be `(n + 1)`-simplex of `U`
  with values in `W` (a morphism from `W` to the `(n + 1)`-st matching object of `U`);
- `CategoryTheory.SemiSimplicialObject.cochainComplex`: for a presheaf `F` with values in a
  preadditive category, the cochain complex `n ↦ F(U.obj n)` with the alternating sum of the face
  maps as differential;
- `CategoryTheory.SemiSimplicialObject.matching`: in a category with finite limits, the matching
  object `M_{n + 1}(U)` corepresenting compatible families, and the matching map
  `U.obj (n + 1) ⟶ M_{n + 1}(U)`.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits Opposite

namespace CategoryTheory

/-- A semi-simplicial object in `C`: objects `obj n` and face maps
`δ n i : obj (n + 1) ⟶ obj n`, `i : Fin (n + 2)`, satisfying the simplicial identities. -/
structure SemiSimplicialObject (C : Type u) [Category.{v} C] where
  /-- The object of `n`-simplices. -/
  obj : ℕ → C
  /-- The `i`-th face map from `(n + 1)`-simplices to `n`-simplices. -/
  δ (n : ℕ) (i : Fin (n + 2)) : obj (n + 1) ⟶ obj n
  /-- The simplicial identity `δ_{j + 1} ≫ δ_i = δ_i ≫ δ_j` for `i ≤ j`. -/
  δ_comp_δ (n : ℕ) {i j : Fin (n + 2)} (h : i ≤ j) :
    δ (n + 1) j.succ ≫ δ n i = δ (n + 1) i.castSucc ≫ δ n j

namespace SemiSimplicialObject

variable {C : Type u} [Category.{v} C]

attribute [reassoc] δ_comp_δ

/-- A morphism of semi-simplicial objects: maps in every degree commuting with the faces. -/
@[ext]
structure Hom (U V : SemiSimplicialObject C) where
  /-- The component in degree `n`. -/
  app (n : ℕ) : U.obj n ⟶ V.obj n
  /-- Compatibility with the face maps. -/
  app_δ (n : ℕ) (i : Fin (n + 2)) : app (n + 1) ≫ V.δ n i = U.δ n i ≫ app n := by
    aesop_cat

attribute [reassoc (attr := simp)] Hom.app_δ

instance : Category (SemiSimplicialObject C) where
  Hom := Hom
  id U := { app _ := 𝟙 _ }
  comp f g := { app n := f.app n ≫ g.app n }

@[ext]
lemma hom_ext {U V : SemiSimplicialObject C} {f g : U ⟶ V} (h : ∀ n, f.app n = g.app n) :
    f = g :=
  Hom.ext (funext h)

@[simp]
lemma id_app (U : SemiSimplicialObject C) (n : ℕ) : Hom.app (𝟙 U) n = 𝟙 _ := rfl

@[simp, reassoc]
lemma comp_app {U V W : SemiSimplicialObject C} (f : U ⟶ V) (g : V ⟶ W) (n : ℕ) :
    (f ≫ g).app n = f.app n ≫ g.app n := rfl

section Map

/-- The image of a semi-simplicial object under a functor. -/
@[simps]
def map {D : Type u'} [Category.{v'} D] (G : C ⥤ D) (U : SemiSimplicialObject C) :
    SemiSimplicialObject D where
  obj n := G.obj (U.obj n)
  δ n i := G.map (U.δ n i)
  δ_comp_δ n _ _ h := by simp only [← G.map_comp, U.δ_comp_δ n h]

end Map

section Compatible

variable (U : SemiSimplicialObject C)

/-- A family `x : Fin (n + 2) → (W ⟶ U.obj n)` is *compatible* if it satisfies the simplicial
identities `x_{j + 1} ≫ δ_i = x_i ≫ δ_j` for `i ≤ j` (no condition for `n = 0`). These are the
possible families of faces of an `(n + 1)`-simplex of `U` with values in `W`. -/
def Compatible : ∀ {n : ℕ} {W : C}, (Fin (n + 2) → (W ⟶ U.obj n)) → Prop
  | 0, _, _ => True
  | m + 1, _, x => ∀ (i j : Fin (m + 2)), i ≤ j → x j.succ ≫ U.δ m i = x i.castSucc ≫ U.δ m j

lemma compatible_zero {W : C} (x : Fin 2 → (W ⟶ U.obj 0)) : U.Compatible x := trivial

lemma compatible_succ_iff {m : ℕ} {W : C} (x : Fin (m + 3) → (W ⟶ U.obj (m + 1))) :
    U.Compatible x ↔
      ∀ (i j : Fin (m + 2)), i ≤ j → x j.succ ≫ U.δ m i = x i.castSucc ≫ U.δ m j :=
  Iff.rfl

/-- The faces of an `(n + 1)`-simplex form a compatible family. -/
lemma compatible_δ {n : ℕ} {W : C} (y : W ⟶ U.obj (n + 1)) :
    U.Compatible (fun i ↦ y ≫ U.δ n i) := by
  cases n with
  | zero => trivial
  | succ m =>
    intro i j hij
    simp only [Category.assoc, U.δ_comp_δ m hij]

/-- Compatible families are stable under precomposition. -/
lemma Compatible.comp {n : ℕ} {W W' : C} {x : Fin (n + 2) → (W ⟶ U.obj n)} (hx : U.Compatible x)
    (g : W' ⟶ W) : U.Compatible (fun i ↦ g ≫ x i) := by
  cases n with
  | zero => trivial
  | succ m =>
    intro i j hij
    simp only [Category.assoc, hx i j hij]

/-- Compatible families are stable under postcomposition with a morphism of semi-simplicial
objects. -/
lemma Compatible.map {V : SemiSimplicialObject C} (f : U ⟶ V) {n : ℕ} {W : C}
    {x : Fin (n + 2) → (W ⟶ U.obj n)} (hx : U.Compatible x) :
    V.Compatible (fun i ↦ x i ≫ f.app n) := by
  cases n with
  | zero => trivial
  | succ m =>
    intro i j hij
    simp only [Category.assoc, Hom.app_δ, reassoc_of% (hx i j hij)]

end Compatible

section CochainComplex

variable {A : Type u'} [Category.{v'} A] [Preadditive A]

/-- The differential `Σᵢ (-1)ⁱ F(δᵢ) : F(U.obj n) ⟶ F(U.obj (n + 1))` of the cochain complex
of a presheaf on a semi-simplicial object. -/
noncomputable def cochainDifferential (U : SemiSimplicialObject C) (F : Cᵒᵖ ⥤ A) (n : ℕ) :
    F.obj (op (U.obj n)) ⟶ F.obj (op (U.obj (n + 1))) :=
  ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • F.map (U.δ n i).op

lemma cochainDifferential_comp (U : SemiSimplicialObject C) (F : Cᵒᵖ ⥤ A) (n : ℕ) :
    U.cochainDifferential F n ≫ U.cochainDifferential F (n + 1) = 0 := by
  sorry

/-- The cochain complex `C^•(U, F)` of a presheaf `F` on a semi-simplicial object `U`: in degree
`n` it is `F(U.obj n)`, and the differential is the alternating sum of the face maps. -/
noncomputable def cochainComplex (U : SemiSimplicialObject C) (F : Cᵒᵖ ⥤ A) :
    CochainComplex A ℕ :=
  CochainComplex.of (fun n ↦ F.obj (op (U.obj n))) (U.cochainDifferential F)
    (U.cochainDifferential_comp F)

@[simp]
lemma cochainComplex_X (U : SemiSimplicialObject C) (F : Cᵒᵖ ⥤ A) (n : ℕ) :
    (U.cochainComplex F).X n = F.obj (op (U.obj n)) := rfl

@[simp]
lemma cochainComplex_d (U : SemiSimplicialObject C) (F : Cᵒᵖ ⥤ A) (n : ℕ) :
    (U.cochainComplex F).d n (n + 1) = U.cochainDifferential F n := by
  simp [cochainComplex]

/-- A morphism of presheaves induces a morphism of cochain complexes. -/
noncomputable def cochainComplexMap (U : SemiSimplicialObject C) {F G : Cᵒᵖ ⥤ A} (φ : F ⟶ G) :
    U.cochainComplex F ⟶ U.cochainComplex G :=
  CochainComplex.ofHom (fun n ↦ φ.app (op (U.obj n))) (by sorry)

@[simp]
lemma cochainComplexMap_f (U : SemiSimplicialObject C) {F G : Cᵒᵖ ⥤ A} (φ : F ⟶ G) (n : ℕ) :
    (U.cochainComplexMap φ).f n = φ.app (op (U.obj n)) := by
  simp [cochainComplexMap]

/-- A morphism of semi-simplicial objects `f : U ⟶ V` induces the restriction map of cochain
complexes `C^•(V, F) ⟶ C^•(U, F)`. -/
noncomputable def cochainComplexPullback {U V : SemiSimplicialObject C} (f : U ⟶ V)
    (F : Cᵒᵖ ⥤ A) : V.cochainComplex F ⟶ U.cochainComplex F :=
  CochainComplex.ofHom (fun n ↦ F.map (f.app n).op) (by sorry)

@[simp]
lemma cochainComplexPullback_f {U V : SemiSimplicialObject C} (f : U ⟶ V) (F : Cᵒᵖ ⥤ A)
    (n : ℕ) : (cochainComplexPullback f F).f n = F.map (f.app n).op := by
  simp [cochainComplexPullback]

end CochainComplex

section Matching

variable [HasFiniteLimits C] (U : SemiSimplicialObject C)

/-- The index type of the simplicial identities `δ_{j + 1} ≫ δ_i = δ_i ≫ δ_j`, `i ≤ j`, between
`(m + 2)`-simplices and `m`-simplices. -/
abbrev MatchingIndex (m : ℕ) : Type := {p : Fin (m + 2) × Fin (m + 2) // p.1 ≤ p.2}

/-- The two maps `∏ᵢ U_{m + 1} ⟶ ∏_{i ≤ j} U_m` whose equalizer is `M_{m + 2}(U)`. -/
noncomputable def matchingLeft (m : ℕ) :
    ∏ᶜ (fun _ : Fin (m + 3) ↦ U.obj (m + 1)) ⟶ ∏ᶜ (fun _ : MatchingIndex m ↦ U.obj m) :=
  Pi.lift fun p ↦ Pi.π _ p.1.2.succ ≫ U.δ m p.1.1

/-- The two maps `∏ᵢ U_{m + 1} ⟶ ∏_{i ≤ j} U_m` whose equalizer is `M_{m + 2}(U)`. -/
noncomputable def matchingRight (m : ℕ) :
    ∏ᶜ (fun _ : Fin (m + 3) ↦ U.obj (m + 1)) ⟶ ∏ᶜ (fun _ : MatchingIndex m ↦ U.obj m) :=
  Pi.lift fun p ↦ Pi.π _ p.1.1.castSucc ≫ U.δ m p.1.2

/-- The `(n + 1)`-st matching object `M_{n + 1}(U)` of a semi-simplicial object `U` in a category
with finite limits: it corepresents the compatible families `Fin (n + 2) → (W ⟶ U.obj n)`
(`CategoryTheory.SemiSimplicialObject.matchingLift`). For `n = 0` it is the product
`U.obj 0 ⨯ U.obj 0`; for `n = m + 1` it is the equalizer of the two maps
`∏ᵢ U_{m + 1} ⟶ ∏_{i ≤ j} U_m` given by the two sides of the simplicial identities. -/
noncomputable def matching : ℕ → C
  | 0 => ∏ᶜ (fun _ : Fin 2 ↦ U.obj 0)
  | m + 1 => equalizer (U.matchingLeft m) (U.matchingRight m)

/-- The `i`-th projection `M_{n + 1}(U) ⟶ U.obj n`. -/
noncomputable def matchingπ : ∀ (n : ℕ) (_ : Fin (n + 2)), U.matching n ⟶ U.obj n
  | 0, i => Pi.π _ i
  | m + 1, i => equalizer.ι (U.matchingLeft m) (U.matchingRight m) ≫ Pi.π _ i

lemma compatible_matchingπ (n : ℕ) : U.Compatible (U.matchingπ n) := by
  sorry

/-- The morphism to the matching object given by a compatible family. -/
noncomputable def matchingLift : ∀ {n : ℕ} {W : C} (x : Fin (n + 2) → (W ⟶ U.obj n))
    (_ : U.Compatible x), W ⟶ U.matching n
  | 0, _, x, _ => Pi.lift x
  | m + 1, _, x, hx => equalizer.lift (Pi.lift x) (by sorry)

@[reassoc (attr := simp)]
lemma matchingLift_π {n : ℕ} {W : C} (x : Fin (n + 2) → (W ⟶ U.obj n)) (hx : U.Compatible x)
    (i : Fin (n + 2)) : U.matchingLift x hx ≫ U.matchingπ n i = x i := by
  sorry

lemma matching_hom_ext {n : ℕ} {W : C} {f g : W ⟶ U.matching n}
    (h : ∀ i, f ≫ U.matchingπ n i = g ≫ U.matchingπ n i) : f = g := by
  sorry

/-- The matching map `U.obj (n + 1) ⟶ M_{n + 1}(U)`, whose components are the face maps. -/
noncomputable def toMatching (n : ℕ) : U.obj (n + 1) ⟶ U.matching n :=
  U.matchingLift (U.δ n) (by simpa using U.compatible_δ (𝟙 _))

@[reassoc (attr := simp)]
lemma toMatching_π (n : ℕ) (i : Fin (n + 2)) : U.toMatching n ≫ U.matchingπ n i = U.δ n i := by
  simp [toMatching]

end Matching

end SemiSimplicialObject

end CategoryTheory
