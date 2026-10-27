/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Étale stacks on schemes over a localized base

Source: Stacks Project, Tags 04WT and 04WV
(blueprint: lem-sfb-etale-stack-localization).

The represented stack is `BasedCategory.ofFunctor (Over.map g)`. Construction A
replaces the projection `F.p` by `F.p ⋙ Over.map g`; Construction B replaces the
projection of `G` by `q.toFunctor`. Both retain the total category. The equivalences
on morphism categories retain the underlying functors and natural transformations
in both directions. Consequently they preserve identities, vertical composition,
and horizontal composition, which are computed on those same underlying data.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open CategoryTheory

namespace CategoryTheory

/-- Étale stacks over `S` are exactly étale stacks over `S'` with a map to the
represented `S`. The two constructions keep the total category, its functors, and
its natural isomorphisms. The full subcategory on the right imposes strict
commutation with the projections to `S`. Its based natural transformations are
already compatible with these projections: `Over.map g` is faithful. Between
fibred groupoids every based natural transformation is invertible, so these hom
categories encode exactly the required 2-morphisms.

Source: Stacks Project, Tag 04WT, Constructions A and B, and Tag 04WV
(blueprint: lem-sfb-etale-stack-localization).

Proof:
1. The slice `(Sch/S')/S` is `Sch/S`, with the same jointly surjective étale
   covering families. The fibre of `Over.map g` over `T` consists of the maps
   `T → S` over `S'`, with discrete arrows. Apply
   lem-weil-pbc-small-etale-representable-presheaf-sheaf on the small étale site
   of `T` to `T ×[S'] S` (def-pc-fibre-product). Maps to `S` glue uniquely;
   this proves object descent and the isomorphism sheaf condition for `h_S`.
   Yoneda identifies the slice with the discrete moduli of `yoneda.obj (Over.mk g)`,
   giving the represented-by-scheme assertion.
2. A lift for `F.p` over the arrow `(V, a u) → (T, a)` is a lift for the
   composite projection over `u`. Given arrows into a common object, their
   unique-factorization condition in the large base forces the required equation
   of maps to `S`, hence is exactly the condition in the slice. Thus the
   composite is fibred in groupoids, using def-sfb-stable-pointed-moduli-groupoids.
3. Local isomorphisms in the composite imply that the two maps to `S` agree
   locally, hence globally by step 1. They now lie in one isomorphism sheaf
   for `F`; its unique gluing is their unique gluing over `S'` as well.
4. For an object descent datum in the composite, its structure maps to `S`
   agree on overlaps. Glue those maps by step 1, then apply effective descent
   for `F` over the resulting `S`-scheme. The same object and local
   identifications give effectivity over `S'`.
5. Conversely a lift for `G.p` of a slice arrow is automatically a lift for
   `q.toFunctor`: its image in the slice has the prescribed underlying arrow
   and endpoints. The same observation proves unique factorization, because
   a slice arrow is determined by its underlying arrow and endpoints.
6. Isomorphisms in the fixed slice fibre are exactly the isomorphisms over the
   underlying scheme. Descend objects using `G`, then use step 1 to identify
   the descended map to `S` with the prescribed one. This proves the stack
   axioms for `q.toFunctor` and establishes both implications in the displayed
   stack equivalences, without any algebraicity or separation hypothesis.
7. On 1-morphisms retain the total functor: being over `S` says exactly that
   it commutes with the maps to `h_S`. On 2-morphisms retain the natural
   isomorphism: faithfulness of the slice functor identifies compatibility over
   `S` and over `S'`. This gives the displayed equivalences with the stated
   normalizations in both directions. Identities and both compositions are
   unchanged. The two object constructions are inverse since `q.w` says
   `q.toFunctor ⋙ Over.map g = G.p`, and the other composite has projection
   `F.p` literally. Hence these are the mutually inverse 2-category equivalences
   of Tag 04WV.
-/
theorem etaleStack_localization {S S' : AlgebraicGeometry.Scheme.{u}} (g : S ⟶ S') :
    IsModuliStack (BasedCategory.ofFunctor (Over.map g)) ∧
    IsRepresentedByScheme (BasedCategory.ofFunctor (Over.map g)) (Over.mk g) ∧
    (∀ F : BasedCategory.{v₁, w₁} (Over S),
      IsModuliStack F ↔ IsModuliStack (BasedCategory.ofFunctor (F.p ⋙ Over.map g))) ∧
    (∀ (G : BasedCategory.{v₁, w₁} (Over S'))
      (q : BasedFunctor G (BasedCategory.ofFunctor (Over.map g))),
      IsModuliStack G ↔ IsModuliStack (BasedCategory.ofFunctor q.toFunctor)) ∧
    (∀ (F : BasedCategory.{v₁, w₁} (Over S))
      (F' : BasedCategory.{v₂, w₂} (Over S)),
      IsModuliStack F → IsModuliStack F' →
      ∃ E : BasedFunctor F F' ≌
          ObjectProperty.FullSubcategory (fun h : BasedFunctor
            (BasedCategory.ofFunctor (F.p ⋙ Over.map g))
            (BasedCategory.ofFunctor (F'.p ⋙ Over.map g)) ↦
              h.toFunctor ⋙ F'.p = F.p),
        (∀ f : BasedFunctor F F', (E.functor.obj f).obj.toFunctor = f.toFunctor) ∧
        (∀ f, (E.inverse.obj f).toFunctor = f.obj.toFunctor) ∧
        (∀ (f h : BasedFunctor F F') (α : f ⟶ h),
          HEq ((E.functor.map α).hom).toNatTrans α.toNatTrans) ∧
        (∀ (f h) (α : f ⟶ h),
          HEq (E.inverse.map α).toNatTrans α.hom.toNatTrans)) := by
  sorry

end CategoryTheory
