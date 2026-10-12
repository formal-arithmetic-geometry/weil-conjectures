/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.PathCategory.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Lifting a finite diagram with prescribed object models

Source: Stacks Project, Limits, Tag 01ZM (2), (3), and its closing colimit assertion.
(blueprint: lem-weil-pbc-finite-diagram-lift-of-models).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Given object models at a single stage, the generating arrows and finitely many
relations lift after one further base change. No object descent or étaleness descent
is asserted here.

Source: Stacks Project, Limits, Tag 01ZM (2), (3), closing colimit assertion;
step 4 of lem-weil-pbc-etale-finite-data-descent.
(blueprint: lem-weil-pbc-finite-diagram-lift-of-models).

Proof:
1. Conjugate each generating arrow of F by the supplied object isomorphisms.
   Apply 01ZM (2) to each resulting map between pullbacks of the specified models.
   A common upper bound of the finitely many arrow stages and i exists by directedness.
   Pull the maps to that bound, keeping their compatibility with the given limit maps.
2. Lift this quiver map by Paths.lift. The objectwise isomorphisms form a natural
   isomorphism on paths: prove the naturality equation by induction on a path, using
   the generator equations in the successor case and identities for the empty path.
3. The two composites of each relation agree after pullback, by naturality and
   cancellation of the comparison isomorphisms. Apply 01ZM (3) to these two maps.
   A common upper bound for the finitely many relation stages makes every relation
   hold simultaneously. Pull back the functor and comparisons to that stage.
4. At each change of stage the objects are the canonical pullbacks of V a, using
   pullback transitivity to identify iterated pullbacks with these specified objects.
   Transport the arrows through these identifications; functoriality and naturality
   preserve all equations. For an empty vertex, arrow, or relation type, choose i
   or the already chosen stage: the respective conditions are vacuous. -/
theorem finite_diagram_lift_of_models
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (A : Type v) [Finite A] [Quiver.{v} A]
    [Finite (Σ a b : A, Quiver.Hom a b)]
    (R : Type v) [Finite R] (s t : R → Paths A)
    (p q : ∀ r, s r ⟶ t r) (F : Paths A ⥤ Over c.pt)
    (i : Iᵒᵖ) (V : A → Over (D.obj i))
    (hV : ∀ a, LocallyOfFinitePresentation (V a).hom ∧
      QuasiCompact (V a).hom ∧ QuasiSeparated (V a).hom)
    (α : ∀ a, (Over.pullback (c.π.app i)).obj (V a) ≅ F.obj a)
    (hR : ∀ r, F.map (p r) = F.map (q r)) :
    ∃ (j : Iᵒᵖ) (h : j ⟶ i) (G : Paths A ⥤ Over (D.obj j))
      (β : G ⋙ Over.pullback (c.π.app j) ≅ F),
      (∀ a, G.obj a = (Over.pullback (D.map h)).obj (V a)) ∧
      (∀ r, G.map (p r) = G.map (q r)) := by sorry

end AlgebraicGeometry
