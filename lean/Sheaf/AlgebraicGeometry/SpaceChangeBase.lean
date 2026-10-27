/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Viewing algebraic spaces over a smaller base scheme

Source: Stacks Project, Spaces, Tags 03I4, 03I5 and 04SG; Properties of Spaces,
Tag 04KK, first paragraph of the proof
(blueprint: lem-sfb-space-change-base-to-integers).

The extension is characterized on sections, restrictions, and morphisms. The equivalence
of small étale sites retains scheme charts, their covering families and regular functions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Viewing a space over `S` as a space over `S'` with its map to `S`.
Source: Stacks, Spaces, Tags 03I4, 03I5 and 04SG; Properties of Spaces, Tag 04KK
(blueprint: lem-sfb-space-change-base-to-integers).

Proof:
1. Identify schemes over `S` with the slice of schemes over `S'` at `S`. Apply
   lem-weil-pbc-localized-sheaves-over-representable. The extension presheaf is already
   a sheaf: first glue the maps to `S` using def-trf-scheme-algebraic-space, then glue
   sections of `X`. This gives the displayed sigma formula, projection, restrictions
   and morphism formulas, with no sheafification changing its sections.
2. For schemes, forgetting the base sends `(phi,a)` to `a`, with inverse giving `a`
   its forced structure map. Matching pairs in the sigma formula have the same `phi`,
   so fibre products are preserved, using
   lem-weil-pbc-site-sheaf-sets-limits-sectionwise.
3. Check algebraicity by scheme tests (def-trf-algebraic-space). Two maps from schemes
   acquire maps to `S`, and their fibre product over the extension is the same scheme
   fibre product over `X`. For an arbitrary diagonal test use
   `T ×_(T ×_(S') T) (A ×_X B)`, allowing different `S`-structures on the two copies
   of `T`. A given atlas has the same scheme base changes, hence stays étale surjective.
4. Conversely, a space over `S'` mapping to `S` has the fibre sheaf of step 1. Its
   equality loci are those of the original space, and any atlas inherits its unique
   map to `S`. Thus the sheaf equivalence restricts to precisely the space categories.
5. A scheme chart over the extension acquires its unique map to `S`. The scheme tests
   for étaleness are identical in both directions. Chart arrows are exactly the same
   scheme maps; jointly surjective étale coverings therefore agree. The structure
   sheaf is regular functions on these same schemes with the same pullbacks.
6. For any `h : X → Y`, the fibre product of an étale chart `V → Y` with `X` need
   not be a scheme. Step 2 still identifies the sheaf fibre products and both
   projections, naturally in `V`. Its projection to `X` has the same étale scheme
   tests `T ×_Y V` before and after extension. If the fibre product is a scheme,
   step 5 identifies it as that same chart. This proves compatibility of base change
   on objects, arrows and regular functions. No finiteness or separation was used. -/
theorem exists_spaceChangeBase {S S' : Scheme.{u}} (g : S ⟶ S') :
    ∃ (J : AlgebraicSpace S ⥤ Over (schemeSpace (Over.mk g)))
      (e : ∀ (X : AlgebraicSpace S) (T : Over S'),
        (J.obj X).left.obj.obj.obj (op T) ≃
          Σ a : T ⟶ Over.mk g, X.obj.obj.obj (op (Over.mk a.left))),
      (∀ (X : AlgebraicSpace S) (T : Over S')
        (z : (J.obj X).left.obj.obj.obj (op T)),
        (J.obj X).hom.hom.hom.app (op T) z = (e X T z).1) ∧
      (∀ (X : AlgebraicSpace S) (T U : Over S') (b : U ⟶ T)
        (a : T ⟶ Over.mk g) (s : X.obj.obj.obj (op (Over.mk a.left))),
        e X U ((J.obj X).left.obj.obj.map b.op ((e X T).symm ⟨a, s⟩)) =
          ⟨b ≫ a, X.obj.obj.map (Over.homMk b.left rfl :
            Over.mk (b ≫ a).left ⟶ Over.mk a.left).op s⟩) ∧
      (∀ (X Y : AlgebraicSpace S) (f : X ⟶ Y) (T : Over S')
        (a : T ⟶ Over.mk g) (s : X.obj.obj.obj (op (Over.mk a.left))),
        e Y T ((J.map f).left.hom.hom.app (op T) ((e X T).symm ⟨a, s⟩)) =
          ⟨a, f.hom.hom.app (op (Over.mk a.left)) s⟩) ∧
      J.IsEquivalence ∧
      (∀ (X : AlgebraicSpace S) (U : Over S) (a : yoneda.obj U ⟶ X.obj.obj),
        IsEtale a → IsSurjective a →
        ∃ b : yoneda.obj ((Over.map g).obj U) ⟶ (J.obj X).left.obj.obj,
          e X ((Over.map g).obj U) (b.app (op ((Over.map g).obj U)) (𝟙 _)) =
            ⟨Over.homMk U.hom rfl,
              X.obj.obj.map (Over.homMk (𝟙 U.left) (by simp) :
                Over.mk U.hom ⟶ U).op (a.app (op U) (𝟙 U))⟩ ∧
          IsEtale b ∧ IsSurjective b) ∧
      (∀ (P A B C : AlgebraicSpace S) (p : P ⟶ A) (q : P ⟶ B)
        (f : A ⟶ C) (h : B ⟶ C),
        IsPullback p.hom q.hom f.hom h.hom →
        IsPullback (J.map p).left.hom (J.map q).left.hom
          (J.map f).left.hom (J.map h).left.hom) ∧
      (∀ X : AlgebraicSpace S,
        ∃ (E : X.EtaleSite ≌ (J.obj X).left.EtaleSite)
          (a : E.functor ⋙ ObjectProperty.ι _ ⋙
              CostructuredArrow.proj yoneda (J.obj X).left.obj.obj ≅
            ObjectProperty.ι _ ⋙ CostructuredArrow.proj yoneda X.obj.obj ⋙ Over.map g),
          (∀ T : X.EtaleSite,
            e X ((Over.map g).obj T.obj.left)
                ((E.functor.obj T).obj.hom.app (op ((Over.map g).obj T.obj.left))
                  (a.inv.app T)) =
              ⟨Over.homMk T.obj.left.hom rfl,
                X.obj.obj.map (Over.homMk (𝟙 T.obj.left.left) (by simp) :
                  Over.mk T.obj.left.hom ⟶ T.obj.left).op
                  (T.obj.hom.app (op T.obj.left) (𝟙 T.obj.left))⟩) ∧
          (∀ (T : X.EtaleSite) (R : Presieve T),
            R ∈ X.etalePrecoverage T ↔
              R.map E.functor ∈ (J.obj X).left.etalePrecoverage (E.functor.obj T)) ∧
          ∃ r : X.structurePresheaf ≅ E.functor.op ⋙ (J.obj X).left.structurePresheaf,
            ∀ T : X.EtaleSite,
              r.hom.app (op T) = (forget₂ CommRingCat RingCat).map
                (Scheme.Γ.map (a.hom.app T).left.op)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
