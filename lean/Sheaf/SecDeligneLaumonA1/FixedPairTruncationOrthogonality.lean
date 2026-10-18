/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Authors: SHEAF contributors
-/
module

public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Truncation adjunctions and orthogonality for fixed pairs

Source: BBD, *Faisceaux pervers*, Propositions 1.3.3–1.3.4, printed pp. 29–30
(blueprint: lem-a1-fixed-pair-truncation-orthogonality).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

open Triangulated

/-- The canonical truncations of a t-structure lift to pairs fixed by a
triangulated autoequivalence, and their adjunctions give the right-orthogonality
criterion for the nonnegative part.  Source: BBD, *Faisceaux pervers*,
Propositions 1.3.3–1.3.4, printed pp. 29–30, with the fixed-pair consequence of
uniqueness and naturality made explicit.

Proof (to be formalised in stage 3), following the node's steps:

1. (uses def-weil-t-structure, def-weil-endofunctor-fixed-pair-category,
   lem-weil-heart-short-exact-triangles) Fix `n`.  Since `Φ = E.functor` is exact it
   commutes with the shift, so it preserves `T^{≤n}` and `T^{≥n+1}` for every `n`.
   Applying `Φ` to the truncation triangle `τ^{≤n}X → X → τ^{≥n+1}X →` gives a
   distinguished triangle with outer terms in `T^{≤n}` and `T^{≥n+1}`; uniqueness of
   truncation triangles (lem-weil-heart-short-exact-triangles, clause 1) gives unique
   isomorphisms `c_X : Φ τ^{≤n} X ≅ τ^{≤n} Φ X`, `d_X : Φ τ^{≥n+1} X ≅ τ^{≥n+1} Φ X`
   with `ι_{ΦX} c_X = Φ(ι_X)` and `d_X Φ(π_X) = π_{ΦX}`.  Both are natural by the
   right (resp. left) truncation adjunction.  For a fixed pair `(X, θ)` put
   `θ^{≤n} = τ^{≤n}(θ) ∘ c_X` and `θ^{≥n+1} = τ^{≥n+1}(θ) ∘ d_X`; then
   `ι_X θ^{≤n} = θ Φ(ι_X)`, so `ι_X` (dually `π_X`) is a morphism of fixed pairs, and
   naturality of `c`, `d` shows that `τ^{≤n} f`, `τ^{≥n+1} f` are morphisms of fixed
   pairs when `f` is.  Identities and composites are those of `C`, so these are
   functors on fixed pairs lifting `τ^{≤n}`, `τ^{≥n+1}` (every `τ^{≥m}` is a `τ^{≥n+1}`).
2. (uses def-weil-endofunctor-fixed-pair-category, lem-weil-heart-short-exact-triangles)
   Let `(M, θ_M)` be a fixed pair with `M ∈ T^{≤n}`.  The bijection `h ↦ ι_X h`,
   `Hom(M, τ^{≤n}X) → Hom(M, X)`, sends equivariant maps to equivariant maps; if
   `g = ι_X h` is equivariant, then `h θ_M` and `θ^{≤n} Φ(h)` agree after composing
   with `ι_X`, and since `Φ M ∈ T^{≤n}` injectivity of the adjunction bijection for
   the source `Φ M` makes them equal, so `h` is equivariant.  Dually for
   `M ∈ T^{≥n+1}` and `h ↦ h π_X`, using `Φ(π_X) = d_X⁻¹ π_{ΦX}` and injectivity of
   the left adjunction bijection for `Φ X`, transported along `d_X`.
3. (uses def-weil-t-structure, def-weil-endofunctor-fixed-pair-category,
   lem-weil-heart-short-exact-triangles) If `X ∈ T^{≥0}` and `M ∈ T^{≤-1}`, write
   `M = A[1]` with `A ∈ T^{≤0}`; then `Hom(M, X) ≅ Hom(A, X[-1]) = 0` by axiom 2 of
   def-weil-t-structure, so every equivariant `M → X` has zero underlying map.
   Conversely, if every such map vanishes, step 1 with `n = -1` makes
   `(τ^{≤-1}X, θ^{≤-1})` a test pair and `ι_X` equivariant, so `ι_X = 0`; by the
   bijection of step 2, `id = 0` on `τ^{≤-1}X`, so `τ^{≤-1}X = 0`.  In the truncation
   triangle `τ^{≤-1}X → X → τ^{≥0}X →` the map `π_X` is then an isomorphism, and
   `X ∈ T^{≥0}` by strict fullness.  This is BBD 1.3.4 ((a) ⇔ (b)) with Hom taken in
   the fixed-pair category.
(blueprint: lem-a1-fixed-pair-truncation-orthogonality)
-/
theorem fixedPairTruncationOrthogonality
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (t : Triangulated.TStructure C) (E : C ≌ C)
    [E.functor.CommShift ℤ] [E.functor.IsTriangulated]
    [E.inverse.CommShift ℤ] [E.inverse.IsTriangulated]
    (hle : ∀ (n : ℤ) (X : C), t.le n X → t.le n (E.functor.obj X))
    (hge : ∀ (n : ℤ) (X : C), t.ge n X → t.ge n (E.functor.obj X))
    (hleInv : ∀ (n : ℤ) (X : C), t.le n X → t.le n (E.inverse.obj X))
    (hgeInv : ∀ (n : ℤ) (X : C), t.ge n X → t.ge n (E.inverse.obj X)) :
    (∀ (n : ℤ),
      ∃ (leTrunc geTrunc :
          ObjectProperty.FullSubcategory (fun A : Endofunctor.Algebra E.functor => IsIso A.str) ⥤
            ObjectProperty.FullSubcategory (fun A : Endofunctor.Algebra E.functor => IsIso A.str)),
        ∃ (ι : leTrunc ⟶ 𝟭 _)
          (π : 𝟭 _ ⟶ geTrunc),
          (∀ (X : ObjectProperty.FullSubcategory
              (fun A : Endofunctor.Algebra E.functor => IsIso A.str)),
              (leTrunc.obj X).obj.a = (t.truncLE n).obj X.obj.a ∧
              (geTrunc.obj X).obj.a = (t.truncGE n).obj X.obj.a ∧
              HEq (ι.app X).hom.f ((t.truncLEι n).app X.obj.a) ∧
              HEq (π.app X).hom.f ((t.truncGEπ n).app X.obj.a)) ∧
          (∀ (M X : ObjectProperty.FullSubcategory
              (fun A : Endofunctor.Algebra E.functor => IsIso A.str)),
            t.le n M.obj.a →
              Function.Bijective (fun h : M ⟶ leTrunc.obj X => h ≫ ι.app X)) ∧
          (∀ (X M : ObjectProperty.FullSubcategory
              (fun A : Endofunctor.Algebra E.functor => IsIso A.str)),
            t.ge n M.obj.a →
              Function.Bijective (fun h : geTrunc.obj X ⟶ M => π.app X ≫ h))) ∧
    (∀ (X : ObjectProperty.FullSubcategory (fun A : Endofunctor.Algebra E.functor => IsIso A.str)),
      t.ge 0 X.obj.a ↔
        ∀ (M : ObjectProperty.FullSubcategory
            (fun A : Endofunctor.Algebra E.functor => IsIso A.str)),
          t.le (-1 : ℤ) M.obj.a → ∀ f : M ⟶ X, f.hom.f = 0) := by
  sorry

end CategoryTheory

