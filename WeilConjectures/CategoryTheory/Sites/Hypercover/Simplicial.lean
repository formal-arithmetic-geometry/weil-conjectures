/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.AlgebraicTopology.SimplicialObject.Split
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Sites.Grothendieck

/-!
# Simplicial hypercovers

Let `(C, J)` be a site. An augmented simplicial object `U → X` of `C` is a *hypercover* of `X`
if every map `U_n → M_n(U)` to the `n`-th matching object is a covering. Here
`M_0(U) = X`, `M_1(U) = U_0 ×_X U_0`, and in general `M_{n+1}(U)` parametrises the families
`(x_0, …, x_{n+1})` of `n`-simplices which satisfy the simplicial identities
`d_i x_j = d_{j-1} x_i` of the faces of an `(n+1)`-simplex. We do not assume that the
matching objects exist in `C`: we work with their functors of points, the *matching families*
`CategoryTheory.SimplicialObject.Augmented.IsMatchingFamily`, and the covering condition says
that a matching family over `W` lifts to an `(n+1)`-simplex locally on `W`, i.e. that the
morphism from the presheaf represented by `U_{n+1}` to the matching presheaf is locally
surjective. When the matching object is representable, this says exactly that
`U_{n+1} → M_{n+1}(U)` generates a covering sieve.

For a presheaf `F` on `C` with values in a preadditive category, the complex `C^•(U, F)` has
`C^n(U, F) = F(U_n)`, with differential the alternating sum of the restrictions along the
faces `d_i : U_{n+1} → U_n`. A morphism of simplicial objects induces a morphism of complexes,
and simplicially homotopic morphisms induce homotopic morphisms of complexes.

## Main definitions

- `CategoryTheory.SimplicialObject.Augmented.IsMatchingFamily`: the `W`-points of the matching
  objects.
- `CategoryTheory.SimplicialObject.Augmented.IsHypercover`: hypercovers.
- `CategoryTheory.SimplicialObject.Augmented.IsHypercoverThrough`: the truncation through
  degree `r` of a hypercover.
- `CategoryTheory.SimplicialObject.cechComplex`: the complex `C^•(U, F)`.
- `CategoryTheory.SimplicialObject.cechComplexMap`: the morphism of complexes induced by a
  morphism of simplicial objects.

## Main statements

- `CategoryTheory.SimplicialObject.Homotopy.cechComplexHomotopy`: simplicially homotopic
  morphisms induce homotopic morphisms of complexes.
-/

@[expose] public section

universe v' u' v u

open CategoryTheory Limits Opposite Simplicial AlgebraicTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace SimplicialObject

namespace Augmented

variable (U : SimplicialObject.Augmented C)

/-- A family `x_0, …, x_{n+1} : W ⟶ U_n` of `n`-simplices of an augmented simplicial object
`U → X` is a *matching family* if it satisfies the identities of the family of faces of an
`(n + 1)`-simplex: for `n = 0` the two points have the same image in `X`, and for `n + 1` the
simplicial identities `d_i x_{j + 1} = d_j x_i` hold for `i ≤ j`. These are the `W`-points of the
matching object `M_{n+1}(U)`, the finite limit of all compatible proper faces of an
`(n + 1)`-simplex. -/
def IsMatchingFamily : (n : ℕ) → {W : C} → (Fin (n + 2) → (W ⟶ U.left _⦋n⦌)) → Prop
  | 0, _, x => x 0 ≫ U.hom.app (op ⦋0⦌) = x 1 ≫ U.hom.app (op ⦋0⦌)
  | n + 1, _, x => ∀ i j : Fin (n + 2), i ≤ j →
      x j.succ ≫ U.left.δ i = x i.castSucc ≫ U.left.δ j

lemma isMatchingFamily_zero_iff {W : C} (x : Fin 2 → (W ⟶ U.left _⦋0⦌)) :
    U.IsMatchingFamily 0 x ↔ x 0 ≫ U.hom.app (op ⦋0⦌) = x 1 ≫ U.hom.app (op ⦋0⦌) :=
  Iff.rfl

lemma isMatchingFamily_succ_iff {n : ℕ} {W : C} (x : Fin (n + 3) → (W ⟶ U.left _⦋n + 1⦌)) :
    U.IsMatchingFamily (n + 1) x ↔ ∀ i j : Fin (n + 2), i ≤ j →
      x j.succ ≫ U.left.δ i = x i.castSucc ≫ U.left.δ j :=
  Iff.rfl

/-- The faces of an `(n + 1)`-simplex form a matching family. -/
lemma isMatchingFamily_δ {n : ℕ} {W : C} (y : W ⟶ U.left _⦋n + 1⦌) :
    U.IsMatchingFamily n (fun i ↦ y ≫ U.left.δ i) := by
  cases n with
  | zero =>
    change (y ≫ U.left.δ 0) ≫ _ = (y ≫ U.left.δ 1) ≫ _
    have h₀ := U.hom.naturality (SimplexCategory.δ (0 : Fin 2)).op
    have h₁ := U.hom.naturality (SimplexCategory.δ (1 : Fin 2)).op
    dsimp at h₀ h₁
    simp only [Category.assoc, SimplicialObject.δ_def, h₀, h₁]
  | succ n =>
    intro i j hij
    simp only [Category.assoc]
    rw [U.left.δ_comp_δ hij]

/-- Matching families are stable under precomposition. -/
lemma IsMatchingFamily.comp {n : ℕ} {W W' : C} {x : Fin (n + 2) → (W ⟶ U.left _⦋n⦌)}
    (hx : U.IsMatchingFamily n x) (g : W' ⟶ W) :
    U.IsMatchingFamily n (fun i ↦ g ≫ x i) := by
  cases n with
  | zero =>
    have hx' : x 0 ≫ U.hom.app (op ⦋0⦌) = x 1 ≫ U.hom.app (op ⦋0⦌) := hx
    change (g ≫ x 0) ≫ _ = (g ≫ x 1) ≫ _
    rw [Category.assoc, Category.assoc, hx']
  | succ n =>
    intro i j hij
    simp only [Category.assoc, hx i j hij]

/-- The sieve of the morphisms `g : W' ⟶ W` along which the point `f : W ⟶ X` lifts to a
`0`-simplex of `U`. -/
@[simps]
def liftSieveZero {W : C} (f : W ⟶ U.right) : Sieve W where
  arrows W' g := ∃ y : W' ⟶ U.left _⦋0⦌, y ≫ U.hom.app (op ⦋0⦌) = g ≫ f
  downward_closed := by
    rintro W' W'' g ⟨y, hy⟩ h
    exact ⟨h ≫ y, by rw [Category.assoc, hy, Category.assoc]⟩

/-- The sieve of the morphisms `g : W' ⟶ W` along which the family `x` of `n`-simplices lifts to
an `(n + 1)`-simplex with faces `g ≫ x i`. -/
@[simps]
def liftSieve {n : ℕ} {W : C} (x : Fin (n + 2) → (W ⟶ U.left _⦋n⦌)) : Sieve W where
  arrows W' g := ∃ y : W' ⟶ U.left _⦋n + 1⦌, ∀ i, y ≫ U.left.δ i = g ≫ x i
  downward_closed := by
    rintro W' W'' g ⟨y, hy⟩ h
    exact ⟨h ≫ y, fun i ↦ by rw [Category.assoc, hy, Category.assoc]⟩

variable (J : GrothendieckTopology C)

/-- An augmented simplicial object `U → X` is a *hypercover* of `X` if every morphism
`U_n → M_n(U)` to the matching object is a covering: every point of `X` lifts locally to a
`0`-simplex, and every matching family of `n`-simplices lifts locally to an `(n + 1)`-simplex.
(blueprint: `def-weil-pbc-finite-split-hypercover`) -/
structure IsHypercover : Prop where
  liftSieveZero_mem ⦃W : C⦄ (f : W ⟶ U.right) : U.liftSieveZero f ∈ J W
  liftSieve_mem ⦃n : ℕ⦄ ⦃W : C⦄ (x : Fin (n + 2) → (W ⟶ U.left _⦋n⦌))
    (hx : U.IsMatchingFamily n x) : U.liftSieve x ∈ J W

/-- The truncation through degree `r` of a hypercover: the morphisms `U_n → M_n(U)` are
coverings for `n ≤ r`. This condition only involves the simplices of degree at most `r`.
(blueprint: `def-weil-pbc-finite-split-hypercover`) -/
structure IsHypercoverThrough (r : ℕ) : Prop where
  liftSieveZero_mem ⦃W : C⦄ (f : W ⟶ U.right) : U.liftSieveZero f ∈ J W
  liftSieve_mem ⦃n : ℕ⦄ (hn : n + 1 ≤ r) ⦃W : C⦄ (x : Fin (n + 2) → (W ⟶ U.left _⦋n⦌))
    (hx : U.IsMatchingFamily n x) : U.liftSieve x ∈ J W

variable {U J}

lemma IsHypercover.isHypercoverThrough (hU : U.IsHypercover J) (r : ℕ) :
    U.IsHypercoverThrough J r where
  liftSieveZero_mem := hU.liftSieveZero_mem
  liftSieve_mem n _ := @hU.liftSieve_mem n

lemma isHypercover_iff_forall_isHypercoverThrough :
    U.IsHypercover J ↔ ∀ r, U.IsHypercoverThrough J r :=
  ⟨fun hU r ↦ hU.isHypercoverThrough r, fun h ↦
    { liftSieveZero_mem := (h 0).liftSieveZero_mem
      liftSieve_mem := fun n _ x hx ↦ (h (n + 1)).liftSieve_mem le_rfl x hx }⟩

end Augmented

section CechComplex

variable {A : Type u'} [Category.{v'} A] [Preadditive A]

/-- The complex `C^•(U, F)` of a simplicial object `U` of `C` with coefficients in a presheaf
`F` on `C`: `C^n(U, F) = F(U_n)`, with differential `∑_i (-1)^i d_i^*`. It is obtained from the
alternating face map complex of the simplicial object `F(U_•)` of `Aᵒᵖ`.
(blueprint: `def-weil-pbc-finite-split-hypercover`) -/
noncomputable def cechComplex (U : SimplicialObject C) (F : Cᵒᵖ ⥤ A) : CochainComplex A ℕ :=
  ((alternatingFaceMapComplex Aᵒᵖ).obj (U ⋙ F.rightOp)).unop

/-- The morphism of complexes `C^•(U, F) → C^•(V, F)` induced by a morphism `f : V ⟶ U` of
simplicial objects. -/
noncomputable def cechComplexMap {U V : SimplicialObject C} (f : V ⟶ U) (F : Cᵒᵖ ⥤ A) :
    cechComplex U F ⟶ cechComplex V F :=
  (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
    ((alternatingFaceMapComplex Aᵒᵖ).map (((whiskering C Aᵒᵖ).obj F.rightOp).map f)).op

/-- Simplicially homotopic morphisms `f g : V ⟶ U` induce homotopic morphisms
`C^•(U, F) → C^•(V, F)`. -/
noncomputable def Homotopy.cechComplexHomotopy {U V : SimplicialObject C} {f g : V ⟶ U}
    (H : SimplicialObject.Homotopy f g) (F : Cᵒᵖ ⥤ A) :
    _root_.Homotopy (cechComplexMap f F) (cechComplexMap g F) :=
  ((H.whiskerRight F.rightOp).toChainHomotopy).unop

variable (U : SimplicialObject C) (F : Cᵒᵖ ⥤ A)

lemma cechComplex_X (n : ℕ) : (cechComplex U F).X n = F.obj (op (U _⦋n⦌)) := rfl

lemma cechComplex_d_eq (n : ℕ) :
    (cechComplex U F).d n (n + 1) = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F.map (U.δ i).op := by
  simp only [cechComplex, HomologicalComplex.unop_d, alternatingFaceMapComplex_obj_d,
    AlternatingFaceMapComplex.objD, unop_sum, unop_zsmul]
  rfl

lemma cechComplexMap_f {V : SimplicialObject C} (f : V ⟶ U) (n : ℕ) :
    (cechComplexMap f F).f n = F.map (f.app (op ⦋n⦌)).op := rfl

/-- The morphism of complexes `C^•(U, F) → C^•(U, G)` induced by a morphism of presheaves. -/
noncomputable def cechComplexMapRight {F G : Cᵒᵖ ⥤ A} (φ : F ⟶ G) :
    cechComplex U F ⟶ cechComplex U G :=
  (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
    ((alternatingFaceMapComplex Aᵒᵖ).map (Functor.whiskerLeft U (NatTrans.rightOp φ))).op

lemma cechComplexMapRight_f {F G : Cᵒᵖ ⥤ A} (φ : F ⟶ G) (n : ℕ) :
    (cechComplexMapRight U φ).f n = φ.app (op (U _⦋n⦌)) := rfl

end CechComplex

end SimplicialObject

end CategoryTheory
