/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import WeilConjectures.CategoryTheory.ExistsDirectedReindexing
import Sheaf.RingTheory.IndEtaleStability

/-! # Finite intersection limits of affine ind-étale coverings

Source: Stacks Project, Tag 099U (`lemma-affine-vanishing`), first-limit paragraph
and displayed intersection identity
(blueprint: lem-weil-pbc-finite-intersection-limit-compatibility).

The stage diagrams are over the fixed scheme `U`, not étale over `X`.
Empty products in `Over U` handle deletion from a one-factor intersection.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.AffineProEt

/-- The simultaneous stage family, with the product index ordered coordinatewise.
Source: Stacks Project, Tag 099U, first-limit product of directed sets
(blueprint: lem-weil-pbc-finite-intersection-limit-compatibility). -/
def firstLimitCoordinate {U : Scheme.{u}} {m : ℕ} {J : Fin m → Type u}
    [∀ a, Preorder (J a)] (D : ∀ a, (J a)ᵒᵖ ⥤ Over U) (a : Fin m) :
    (∀ b, J b)ᵒᵖ ⥤ Over U :=
  (CategoryTheory.Pi.eval J a).op ⋙ D a

/-- The canonical diagram of ordered intersections, including the empty intersection.
Repeated labels select separate product factors at the same stage index.
Source: Stacks Project, Tag 099U, displayed first-limit intersection identity
(blueprint: lem-weil-pbc-finite-intersection-limit-compatibility). -/
noncomputable def firstLimitIntersectionDiagram {U : Scheme.{u}} {m : ℕ}
    {J : Fin m → Type u} [∀ a, Preorder (J a)]
    (D : ∀ a, (J a)ᵒᵖ ⥤ Over U) (k : ℕ) (α : Fin k → Fin m) :
    (∀ a, J a)ᵒᵖ ⥤ Over U :=
  Functor.pi' (fun r ↦ firstLimitCoordinate D (α r)) ⋙ Limits.Pi.functor (Fin k)

/-- Delete the specified factor from a finite ordered fibre product over `U`.
For a one-factor product the target is the empty product, canonically `U`.
Source: Stacks Project, Tag 099U, functoriality of the intersection identity
(blueprint: lem-weil-pbc-finite-intersection-limit-compatibility). -/
noncomputable def firstLimitDelete {U : Scheme.{u}} {m k : ℕ}
    (V : Fin m → Over U) (α : Fin (k + 1) → Fin m) (r : Fin (k + 1)) :
    (∏ᶜ fun s ↦ V (α s)) ⟶ ∏ᶜ fun s ↦ V (α (r.succAbove s)) :=
  Limits.Pi.map' r.succAbove (fun _ ↦ 𝟙 _)

/-- A nonempty finite basis covering of `U` admits independent small directed affine
étale finite-presentation approximations. Every simultaneous stage still covers `U`.
The original and stage intersections are affine ind-étale over `X`, and their canonical
cones are scheme limits, compatible with deletion of every factor and with transitions.
Source: Stacks Project, Tag 099U (`lemma-affine-vanishing`), first-limit paragraph
and displayed intersection identity
(blueprint: lem-weil-pbc-finite-intersection-limit-compatibility).

Proof:
1. The algebra-map clause of ind-étale stability makes each `V_a -> U` ind-étale.
   Use its filtered étale finite-presentation presentation and directed reindexing
   (lem-weil-pbc-ind-etale-stability, def-weil-pbc-ind-etale-algebra,
   lem-weil-pbc-filtered-category-directed-cofinal, def-weil-size-convention).
2. The finite product of the nonempty directed index sets is nonempty and directed.
   Lift a point of `U` into some `V_a`, then project it to the selected stage.
   Thus each simultaneous stage family is jointly surjective and étale
   (def-weil-pbc-ind-etale-basis, def-weil-pbc-proetale-covering,
   def-weil-pbc-etale-site). No individual cone leg must be surjective.
3. Compose the ind-étale stage maps with `U -> X`. Basis stability under fibre
   products puts every intersection in the basis, including repeated factors.
   Maps between affine schemes, including all transitions and cone legs, are affine
   (lem-weil-pbc-ind-etale-stability, lem-weil-pbc-ind-etale-basis,
   lem-weil-pbc-morphism-affine-schemes-affine).
4. Reindex each factor cone along the coordinate projection. A compatible family
   at indices with the same selected coordinate agrees by taking an upper bound
   while keeping that coordinate fixed. The factor limit property now gives a
   unique map into `V_a` (def-weil-pbc-category-colimit).
5. Project any cone over the intersection diagram to each factor. Step 4 gives
   the separate factor maps, even for repeated labels. They have the same map
   to `U` and so give the unique map into the fibre product. This is its scheme
   limit property (def-pc-fibre-product, def-weil-pbc-category-colimit).
6. Compose the cone and transition maps with each surviving factor projection.
   Both sides of each deletion equation agree; product uniqueness proves the
   equations. For deletion to the empty product they are the structure maps to
   `U`; the constant `U`-diagram has limit `U` because the index is nonempty and
   directed. Hence the limit identifications also commute with deletion
   (def-pc-fibre-product, def-weil-pbc-category-colimit). -/
theorem exists_finite_intersection_limit_compatibility
    (X : Scheme.{u}) [IsAffine X] (U : X.AffineProEt)
    {m : ℕ} (hm : 0 < m) (V : Fin m → X.AffineProEt) (f : ∀ a, V a ⟶ U)
    (hcover : Sieve.ofArrows V f ∈ topology X U) :
    ∃ (J : Fin m → Type u) (_ : ∀ a, Preorder (J a))
      (_ : ∀ a, Nonempty (J a)) (_ : ∀ a, IsDirected (J a) (· ≤ ·))
      (D : ∀ a, (J a)ᵒᵖ ⥤ Over U.left)
      (q : ∀ a, (Functor.const (J a)ᵒᵖ).obj (Over.mk (f a).left) ⟶ D a),
      (∀ a i, IsAffine ((D a).obj i).left ∧ Etale ((D a).obj i).hom ∧
        LocallyOfFinitePresentation ((D a).obj i).hom ∧
        QuasiCompact ((D a).obj i).hom ∧
        proAffineEtale (((D a).obj i).hom ≫ U.hom)) ∧
      (∀ a, Nonempty (IsLimit ((Over.forget U.left).mapCone
        (Cone.mk (Over.mk (f a).left) (q a))))) ∧
      (∀ a (i j : (J a)ᵒᵖ) (h : i ⟶ j), IsAffineHom ((D a).map h).left) ∧
      (∀ a i, IsAffineHom ((q a).app i).left) ∧
      (∀ j : ∀ a, J a,
        Sieve.ofArrows (fun a ↦ ((D a).obj (op (j a))).left)
          (fun a ↦ ((D a).obj (op (j a))).hom) ∈ etaleTopology U.left) ∧
      ∃ (π : ∀ (k : ℕ) (α : Fin k → Fin m),
          (Functor.const (∀ a, J a)ᵒᵖ).obj
            (∏ᶜ fun r ↦ Over.mk (f (α r)).left) ⟶
              firstLimitIntersectionDiagram D k α),
        (∀ (k : ℕ) (α : Fin k → Fin m), Nonempty (IsLimit ((Over.forget U.left).mapCone
          (Cone.mk (∏ᶜ fun r ↦ Over.mk (f (α r)).left) (π k α))))) ∧
        (∀ (k : ℕ) (α : Fin k → Fin m), IsAffine (∏ᶜ fun r ↦ Over.mk (f (α r)).left).left ∧
          proAffineEtale ((∏ᶜ fun r ↦ Over.mk (f (α r)).left).hom ≫ U.hom)) ∧
        (∀ (k : ℕ) (α : Fin k → Fin m) (j : (∀ a, J a)ᵒᵖ),
          IsAffine ((firstLimitIntersectionDiagram D k α).obj j).left ∧
          proAffineEtale (((firstLimitIntersectionDiagram D k α).obj j).hom ≫ U.hom)) ∧
        (∀ (k : ℕ) (α : Fin k → Fin m) (i j : (∀ a, J a)ᵒᵖ) (h : i ⟶ j),
          IsAffineHom ((firstLimitIntersectionDiagram D k α).map h).left) ∧
        (∀ (k : ℕ) (α : Fin k → Fin m) (j : (∀ a, J a)ᵒᵖ), IsAffineHom ((π k α).app j).left) ∧
        (∀ (k : ℕ) (α : Fin k → Fin m) (j : (∀ a, J a)ᵒᵖ) (r : Fin k),
          (π k α).app j ≫ Limits.Pi.π
            (fun s ↦ (D (α s)).obj (op (unop j (α s)))) r =
          Limits.Pi.π (fun s ↦ Over.mk (f (α s)).left) r ≫
            (q (α r)).app (op (unop j (α r)))) ∧
        (∀ k (α : Fin (k + 1) → Fin m) (r : Fin (k + 1)) j,
          firstLimitDelete (fun a ↦ Over.mk (f a).left) α r ≫
            (π k (α ∘ r.succAbove)).app j =
          (π (k + 1) α).app j ≫
            firstLimitDelete (fun a ↦ (D a).obj (op (unop j a))) α r) ∧
        (∀ k (α : Fin (k + 1) → Fin m) (r : Fin (k + 1))
            (i j : (∀ a, J a)ᵒᵖ) (h : i ⟶ j),
          (firstLimitIntersectionDiagram D (k + 1) α).map h ≫
            firstLimitDelete (fun a ↦ (D a).obj (op (unop j a))) α r =
          firstLimitDelete (fun a ↦ (D a).obj (op (unop i a))) α r ≫
            (firstLimitIntersectionDiagram D k (α ∘ r.succAbove)).map h) := by
  sorry

end AlgebraicGeometry.Scheme.AffineProEt
