/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Compatible finite-descent sections lift étale locally

Source: Stacks Project, Étale Cohomology, Remark 09Z3 and Lemma 09Z2.
(blueprint: lem-weil-pbc-sets-finite-descent-local-lifts).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A compatible section belongs étale locally to the image of the adjunction unit.
Source: Stacks Project, Étale Cohomology, Remark 09Z3, proved as Lemma 09Z2
using Proposition 03QP (1) and Lemma 03Q1 (3).
(blueprint: lem-weil-pbc-sets-finite-descent-local-lifts).

Proof: Put A = f_* f⁻¹G and D = X' ×_X X', with h = p₁ ≫ f = p₂ ≫ f.
The projections and h are finite by base change and composition. For a geometric
point x of X, the set P of its lifts to X' with the same algebraically closed
field is nonempty by surjectivity and finite geometric-point lifting. Lifts to D
are pairs of lifts to X'. Finite pushforward stalks identify A_x with the product
of the inverse-image stalks over P; the germ-compatible inverse-image bijections
identify these stalks with G_x. They identify the unit with the diagonal. The
composition-unit formula, tested on germs of unit-pulled-back sections, identifies
the two comparison maps on stalks with the two coordinate projections indexed
by P × P. Such germs generate each inverse-image stalk by its germ bijection,
so this calculation determines the comparison maps on all germs. Compatibility
of s' therefore makes its germ a constant P-indexed family. Choose a lift in P;
its coordinate supplies a germ in G_x mapping to the germ of s'. Represent this
germ by a section over a pointed étale neighbourhood. Equality in the filtered
colimit defining A_x is witnessed after an étale refinement, so on that refinement
the restriction of s' is the unit of this section. These refinements contain a
point above every point of X, choosing an algebraic closure of each residue field,
and hence cover X. Their arrows belong to the image sieve, which consequently
covers X. For empty X the empty sieve covers X, giving the same conclusion.
This statement supplies local existence only; agreement and global gluing are
proved separately in the equalizer module. -/
theorem finiteSurjectiveSetDescent_compatible_locally_lifts
    {X X' : Scheme.{u}} (f : X' ⟶ X) [IsFinite f] [Surjective f]
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    ∀ s' : ((Scheme.etaleSetPullback f).obj G).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
            (Scheme.Etale.mk (𝟙 X)))),
        etaleSetDescentComparison f (pullback.fst f f) G (Scheme.Etale.mk (𝟙 X)) s' =
          eqToHom (congrArg
            (fun k : pullback f f ⟶ X ↦ ((Scheme.etaleSetPullback k).obj G).obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
                (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := f) (g := f)).symm)
            (etaleSetDescentComparison f (pullback.snd f f) G
              (Scheme.Etale.mk (𝟙 X)) s') →
          Presheaf.imageSieve
            ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
              (X.smallGrothendieckTopology @Etale)
              (X'.smallGrothendieckTopology @Etale)).unit.app G).hom s' ∈
            X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) := by
  sorry

end AlgebraicGeometry
