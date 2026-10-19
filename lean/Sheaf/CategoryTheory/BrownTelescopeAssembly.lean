/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.CompactObject
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Category.Preorder
import Sheaf.CategoryTheory.CompactHomHocolim
import all Sheaf.CategoryTheory.BrownStageSequence
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.DirectSum.Module

/-! Assembly of compatible Yoneda transformations on a sequential telescope.

Source: Stacks Project, Derived Categories, Tag 0A8F, telescope paragraph of
Lemma `lemma-brown`, and Tag 094A (blueprint: lem-pc-brown-telescope-assembly).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated.Opposite
open CategoryTheory.Pretriangulated

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] [HasCoproducts.{v} C]

omit [HasZeroObject C] [Pretriangulated C] [IsTriangulated C] in
private theorem compact_shift (K : C) (hK : IsCompactObject K) (n : ℤ) :
    IsCompactObject (K⟦n⟧) := by
  classical
  intro J A
  let e := shiftEquiv C n
  have : e.functor.Additive := inferInstanceAs (shiftFunctor C n).Additive
  have : e.inverse.Additive := inferInstanceAs (shiftFunctor C (-n)).Additive
  let adj := e.toAdjunction
  let D := DirectSum.congrAddEquiv (fun j ↦ adj.homAddEquiv K (A j))
  let s := sigmaComparison e.inverse A
  let post : (K ⟶ e.inverse.obj (∐ A)) ≃+ (K ⟶ ∐ fun j ↦ e.inverse.obj (A j)) :=
    { toEquiv := Iso.homCongr (Iso.refl K) (asIso s).symm
      map_add' := by
        intro f g
        simp [Iso.homCongr, Preadditive.add_comp] }
  let Q := (adj.homAddEquiv K (∐ A)).trans post
  let φ := DirectSum.toAddMonoid (fun j ↦ Preadditive.rightComp (e.functor.obj K) (Sigma.ι A j))
  let ψ := DirectSum.toAddMonoid
    (fun j ↦ Preadditive.rightComp K (Sigma.ι (fun j ↦ e.inverse.obj (A j)) j))
  have hcomm : Q.toAddMonoidHom.comp φ = ψ.comp D.toAddMonoidHom := by
    apply DirectSum.addHom_ext
    intro j f
    change Q (φ (DirectSum.of _ j f)) = ψ (D (DirectSum.of _ j f))
    have hφof : φ (DirectSum.of _ j f) = f ≫ Sigma.ι A j :=
      DirectSum.toAddMonoid_of
        (fun j ↦ Preadditive.rightComp (e.functor.obj K) (Sigma.ι A j)) j f
    have hDof : D (DirectSum.of _ j f) =
        DirectSum.of _ j (adj.homAddEquiv K (A j) f) :=
      DirectSum.map_of (fun j ↦ (adj.homAddEquiv K (A j)).toAddMonoidHom) j f
    rw [hφof, hDof]
    rw [show ψ (DirectSum.of _ j (adj.homAddEquiv K (A j) f)) =
        adj.homAddEquiv K (A j) f ≫ Sigma.ι (fun j ↦ e.inverse.obj (A j)) j from
      DirectSum.toAddMonoid_of
        (fun j ↦ Preadditive.rightComp K (Sigma.ι (fun j ↦ e.inverse.obj (A j)) j)) j _]
    dsimp [Q, post, Iso.homCongr]
    rw [Category.id_comp]
    change adj.homEquiv K (∐ A) (f ≫ Sigma.ι A j) ≫ inv s =
      adj.homEquiv K (A j) f ≫ Sigma.ι (fun j ↦ e.inverse.obj (A j)) j
    rw [adj.homEquiv_naturality_right, Category.assoc]
    rw [map_ι_comp_inv_sigmaComparison]
  have hψ := hK J (fun j ↦ e.inverse.obj (A j))
  have hφ : Function.Bijective (fun x ↦ Q (φ x)) := by
    have hh : (fun x ↦ Q (φ x)) = (fun x ↦ ψ (D x)) :=
      funext (fun x ↦ DFunLike.congr_fun hcomm x)
    rw [hh]
    exact hψ.comp D.bijective
  constructor
  · intro x y hxy
    exact hφ.1 (congrArg Q hxy)
  · intro f
    obtain ⟨x, hx⟩ := hφ.2 (Q f)
    exact ⟨x, Q.injective hx⟩

/-- Compatible transformations extend to a telescope, through whose stages every map
from a shift of a compact object factors. This asserts no bijectivity for the transformation.

Source: Stacks Project, Derived Categories, Tag 0A8F, telescope paragraph of Lemma
`lemma-brown`, and Tag 094A (blueprint: lem-pc-brown-telescope-assembly).

Proof: form the coproduct A of the sequence, indexed by ULift ℕ, and its endomorphism
one minus transition shift. Complete this endomorphism to a distinguished triangle
A → A → G → A[1]. The composites of the second triangle morphism with coproduct
inclusions give the stage maps ι. The zero consecutive composition, restricted to
each summand, gives their successor compatibility. Additive Yoneda identifies β j
with an element of H(X j). Product preservation assembles these into an element of
H(A). Successor compatibility means this element lies in the kernel of H of one
minus transition shift, as checked on every product projection. Cohomological
exactness lifts it to H(G). Additive Yoneda makes the lift α, and restriction along
each summand proves the asserted equality of transformations. For a compact K, its
shift K[n] is compact: the inverse shift equivalence preserves coproducts, and its
additive Hom equivalences identify the direct-sum comparison with that of K. Apply
compact_hom_hocolim to K[n] and the displayed triangle. Surjectivity of its comparison,
together with joint surjectivity of the inclusions into a colimit of types, factors
every map from K[n] through some X j. There is no condition on kernels or initial
surjectivity of β here. -/
theorem brownTelescopeAssembly (X : ℕ ⥤ C)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ (J : Type v), PreservesLimitsOfShape (Discrete J) H)
    (β : ∀ j : ℕ, preadditiveYoneda.obj (X.obj j) ⟶ H)
    (hβ : ∀ j : ℕ,
      preadditiveYoneda.map (X.map (homOfLE (Nat.le_succ j))) ≫ β (j + 1) = β j) :
    ∃ (G : C) (ι : ∀ j : ℕ, X.obj j ⟶ G) (α : preadditiveYoneda.obj G ⟶ H),
      (∀ j : ℕ, X.map (homOfLE (Nat.le_succ j)) ≫ ι (j + 1) = ι j) ∧
      (∀ j : ℕ, preadditiveYoneda.map (ι j) ≫ α = β j) ∧
      (∀ (K : C), IsCompactObject K → ∀ (n : ℤ) (f : K⟦n⟧ ⟶ G),
        ∃ (j : ℕ) (g : K⟦n⟧ ⟶ X.obj j), g ≫ ι j = f) := by
  let A : ULift.{v} ℕ → C := fun j ↦ X.obj j.down
  let d : (∐ A) ⟶ (∐ A) := Sigma.desc (fun j : ULift.{v} ℕ ↦
    X.map (homOfLE (Nat.le_succ j.down)) ≫ Sigma.ι A ⟨j.down + 1⟩)
  let u := 𝟙 (∐ A) - d
  obtain ⟨G, q, r, htri⟩ := distinguished_cocone_triangle u
  let ι : ∀ j : ℕ, X.obj j ⟶ G := fun j ↦ Sigma.ι A ⟨j⟩ ≫ q
  have hι : ∀ j : ℕ, X.map (homOfLE (Nat.le_succ j)) ≫ ι (j + 1) = ι j := by
    intro j
    have hu := comp_distTriang_mor_zero₁₂ (Triangle.mk u q r) htri
    change u ≫ q = 0 at hu
    apply (sub_eq_zero.mp ?_).symm
    simpa [u, d, ι, Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc] using
      congrArg (fun f : (∐ A) ⟶ G ↦ Sigma.ι A ⟨j⟩ ≫ f) hu
  let a : ∀ j : ℕ, H.obj (Opposite.op (X.obj j)) :=
    fun j ↦ (β j).app (Opposite.op (X.obj j)) (𝟙 (X.obj j))
  have ha : ∀ j : ℕ, H.map (X.map (homOfLE (Nat.le_succ j))).op (a (j + 1)) = a j := by
    intro j
    rw [stage_elementTransformation_value H (X.obj (j + 1)) (β (j + 1))]
    have h := congrArg (fun γ : preadditiveYoneda.obj (X.obj j) ⟶ H ↦
      γ.app (Opposite.op (X.obj j)) (𝟙 (X.obj j))) (hβ j)
    change (β (j + 1)).app (Opposite.op (X.obj j))
      (𝟙 (X.obj j) ≫ X.map (homOfLE (Nat.le_succ j))) = a j at h
    simpa only [Category.id_comp] using h
  obtain ⟨x, hx⟩ := stage_coproduct_element H hH A (fun j ↦ a j.down)
  have hu : H.map u.op x = 0 := by
    apply stage_coproduct_element_zero H hH A
    intro j
    rw [← AddCommGrpCat.comp_apply, ← H.map_comp, ← op_comp]
    simp only [u, Preadditive.comp_sub, Category.comp_id, d, Sigma.ι_desc,
      op_sub, Functor.map_sub, op_comp, H.map_comp]
    change H.map (Sigma.ι A j).op x -
      H.map (X.map (homOfLE (Nat.le_succ j.down))).op
        (H.map (Sigma.ι A ⟨j.down + 1⟩).op x) = 0
    rw [hx, hx, ha, sub_self]
  have hex := H.map_distinguished_op_exact (Triangle.mk u q r) htri
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).1 hex x hu
  change H.map q.op y = x at hy
  let α := elementTransformation H G y
  have hα : ∀ j : ℕ, preadditiveYoneda.map (ι j) ≫ α = β j := by
    intro j
    ext K f
    change H.map (f ≫ ι j).op y = (β j).app K f
    simp only [ι, op_comp, Functor.map_comp, AddCommGrpCat.comp_apply, hy]
    rw [hx]
    exact stage_elementTransformation_value H (X.obj j) (β j) K.unop f
  refine ⟨G, ι, α, hι, hα, ?_⟩
  intro K hK n f
  obtain ⟨φ, hφ, hbij⟩ := compact_hom_hocolim (K⟦n⟧) (compact_shift K hK n) X G q r htri
  obtain ⟨z, hz⟩ := hbij.2 f
  obtain ⟨j, g, hg⟩ := Types.jointly_surjective' z
  refine ⟨j, g, ?_⟩
  rw [← hz, ← hg, hφ]

end CategoryTheory
