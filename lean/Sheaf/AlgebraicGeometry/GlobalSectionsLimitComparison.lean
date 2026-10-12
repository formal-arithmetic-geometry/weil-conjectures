/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
import Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Global sections of pullbacks at cofiltered limits

Source: Stacks Project, Tag 09YQ, degree zero.
(blueprint: lem-weil-pbc-global-sections-limit-comparison)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Global sections of pullbacks of a fixed abelian sheaf commute with a qcqs inverse
limit with affine transition maps. No assumption on the base scheme is needed.
Source: Stacks Project, Tag 09YQ, degree zero.
(blueprint: lem-weil-pbc-global-sections-limit-comparison)

Proof: Replace the cofiltered category by a coinitial directed preorder and restrict
both the limit cone and the system along that functor. Set F_j = π_j^* G. The inverse-image
composition isomorphisms give transition isomorphisms h^* F_j ≅ F_k; their cocycle and unit
laws follow from coherence of inverse image. On the limit, composition identifies the
pullbacks of every F_j with P^* G, and identifies all transitions with the identity. A
filtered category is connected, so this constant cocone is a colimit. Apply Theorem 09YQ
in degree zero to this system and this cocone. The degree-zero identification with global
sections is natural in sheaf maps and carries cohomology pullback to the adjunction-unit
map globalSectionsUpperStarMap. Thus the resulting colimit legs and transitions are the
maps displayed below. The elementwise criterion for filtered colimits of abelian groups
then gives representatives and eventual vanishing. Coinitiality returns these witnesses
to the original category (for vanishing use a common refinement mapping to the given
object); all transition formulas are preserved by inverse-image coherence. -/
theorem globalSections_limit_comparison {R : Scheme.{u}} {J : Type u}
    [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{u})
    (π : D ⟶ (Functor.const J).obj R) (c : Cone D) (P : c.pt ⟶ R)
    (hP : ∀ j, P = c.π.app j ≫ π.app j)
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)] (hc : IsLimit c)
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let A := AddCommGrpCat.{u + 1}
    let Γ := fun X : Scheme.{u} ↦ Sheaf.Γ X.smallEtaleTopology A
    let F := fun {X : Scheme.{u}} (f : X ⟶ R) ↦ (upperStar A f).obj G
    let ρ := fun {X Y : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ R) (g : X ⟶ R)
      (w : g = h ≫ f) ↦ globalSectionsUpperStarMap A h (F f) ≫
        (Γ X).map ((upperStarComp A h f g w).inv.app G)
    (∀ t : (Γ c.pt).obj (F P), ∃ (j : J) (s : (Γ (D.obj j)).obj (F (π.app j))),
      ρ (c.π.app j) (π.app j) P (hP j) s = t) ∧
    ∀ (j : J) (s : (Γ (D.obj j)).obj (F (π.app j))),
      ρ (c.π.app j) (π.app j) P (hP j) s = 0 →
        ∃ (j' : J) (f : j' ⟶ j), ρ (D.map f) (π.app j) (π.app j') (by simp) s = 0 := by
  sorry

end AlgebraicGeometry.Etale
