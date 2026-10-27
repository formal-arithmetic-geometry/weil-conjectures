/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q156
-/
module

public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.ModuliInertia
public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.SchemeStackDiagonalPresentation
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.StackPointTopology
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Stabilizer-preserving affine charts for finite-inertia stacks

Source: Stacks Project, stacks-more-morphisms.tex, Tag 0DUE
(lemma-etale-local-finite-inertia), with Tags 0DUL and 0DUM
(blueprint: lem-sfb-finite-inertia-etale-affine-charts).

The inertia comparison is expressed by its canonical map on automorphisms in every
scheme fibre. The quotient presentation retains the original arrows and composition,
while the diagonal presentation identifies both kernel-pair projections.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A finite-inertia algebraic stack has a jointly surjective family of separated,
representable étale, stabilizer-preserving charts with finite flat affine presentations.
Source: Stacks Project, stacks-more-morphisms.tex, Tag 0DUE, all four conclusions;
Tags 0DUL and 0DUM for the finite flat affine groupoid presentation
(blueprint: lem-sfb-finite-inertia-etale-affine-charts).

Proof:
1. For every point x apply lem-sfb-finite-inertia-pointwise-groupoid-chart to get
   h : [U/R] → F and v above x, with U and R affine, finite locally free source
   and target, and the correct scheme-theoretic stabilizer at v. This applies to
   finite inertia without requiring the stack to be DM or the inertia to be smooth.
2. By lem-sfb-proper-inertia-stabilizer-preserving-open, shrink around v to the
   stabilizer-preserving open substack. By lem-sfb-flat-groupoid-quotient-open-presentation
   its inverse image is an invariant open U° in U. Lift v to u in U°. Its orbit
   t(s⁻¹({u})) is finite by lem-weil-pbc-finite-closed-map-finite-fibres.
3. Write U = Spec A = Proj A[T], with T of degree one; its sole standard chart has
   degree-zero ring A. Apply lem-sfb-locally-closed-proj-finite-affine to U° with
   the identity closed immersion, obtaining an affine neighbourhood of that finite
   orbit. Apply lem-sfb-locally-free-groupoid-invariant-affine to get an invariant
   affine open W containing it. The restricted relation R_W has finite locally free
   projections by lem-sfb-flat-groupoid-quotient-open-presentation.
4. That same quotient-open theorem identifies [W/R_W] with an open substack of
   the stabilizer-preserving locus, containing v, and gives its representable,
   surjective, finite flat finitely presented map W → [W/R_W]. The restricted h
   is representable étale by lem-sfb-stack-chartwise-smooth-etale-calculus.
   Full open restriction retains every automorphism sheaf, hence the inertia
   comparison. By lem-weil-pbc-finite-morphism-permanence, R_W is affine and is
   the actual 2-kernel pair, with both projections and their comparison retained.
5. By lem-sfb-finite-flat-affine-groupoid-separated, [W/R_W] is separated over k.
   Apply lem-sfb-separated-source-finite-inertia-target to conclude that its map
   to F is separated, without assuming F itself separated over k.
6. Index these choices by the points of F, using lem-sfb-stack-point-topology
   and def-weil-size-convention. Each point lies in its selected chart's image,
   so the family is jointly surjective. If F is empty choose the empty index set.

Bijectivity of the actual fibre functor on automorphisms, for every scheme T and
object over T, is precisely the canonical inertia isomorphism. It tests nonreduced
schemes too. Finite plus locally of finite presentation implies finite presentation;
thus the scheme tests below express exactly the finite flat finitely presented cover.
The chosen chart universe contains both the scheme universe and that of F, and the
index universe contains its field-valued point set. No nonemptiness is imposed. -/
theorem finite_inertia_etale_affine_charts
    (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (CommRingCat.of k))))
    (hF : IsAlgebraicModuliStack F)
    (hI : IsRepresentableFiniteModuliMap (moduliInertiaProjection F)) :
    ∃ (J : Type (max u w))
      (X : J → BasedCategory.{max u v, max (u + 1) w} (Over (Spec (CommRingCat.of k))))
      (g : ∀ j : J, BasedFunctor (X j) F),
      (∀ x : ModuliPoints F, ∃ (j : J) (y : ModuliPoints (X j)), moduliPointMap (g j) y = x) ∧
      ∀ j : J,
        IsAlgebraicModuliStack (X j) ∧
        IsRepresentableByAlgebraicSpaces (g j) ∧
        ModuliSpaceTest (@Etale) (g j) ∧
        ModuliSchemeTest (@IsProper) (moduliRelativeDiagonal (g j)) ∧
        (∀ (T : Over (Spec (CommRingCat.of k))) (x : Functor.Fiber (X j).p T),
          Function.Bijective (fun α : x ≅ x ↦ (moduliFiberMap (g j) T).mapIso α)) ∧
        ∃ (U : Over (Spec (CommRingCat.of k)))
          (a : BasedFunctor (discreteModuli (yoneda.obj U)) (X j)),
          IsAffine U.left ∧
          ModuliSchemeTest
            (fun _ _ f ↦ IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧ Surjective f) a ∧
          ∃ (R : Over (Spec (CommRingCat.of k))) (s t : R ⟶ U)
            (e : U.left ⟶ R.left) (i : R.left ⟶ R.left)
            (c : pullback s.left t.left ⟶ R.left),
            IsAffine R.left ∧ s.left.IsFiniteLocallyFree ∧ t.left.IsFiniteLocallyFree ∧
            IsSchemeStackDiagonalPresentation a a s t ∧
            Nonempty (SchemeGroupoidQuotientPresentation s t e i c (X j) a) := by
  sorry

end CategoryTheory
