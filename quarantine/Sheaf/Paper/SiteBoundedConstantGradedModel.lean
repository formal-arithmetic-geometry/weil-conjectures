/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.TruncationDescends
import Sheaf.Paper.BoundedTopMorphisms
import Sheaf.Paper.LocalFiniteEpiLifts
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems


/-! # Local models with constant finite graded terms

Source: Stacks Project, Cohomology on Sites, Tag 094G, the inductive construction
before descending the differentials to the coefficient ring.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The cohomological induction produces a bounded sheaf complex whose graded
terms are constant finite modules. Its differentials are still sheaf morphisms.

Source: Stacks Project, Cohomology on Sites, Tag 094G, proof of
`lemma-locally-constant`, construction by induction on the cohomological interval.
(blueprint: lem-weil-pbc-site-bounded-constant-graded-model)

Proof: Induct on the interval length, allowing every localized site. A complex
concentrated in one degree is its homology sheaf in that degree; trivialize this
sheaf. For the induction step, restrict so the top cohomology is the constant sheaf
of a finite module. Choose a finite free surjection onto this module and a
representative complex
upper truncated at b. The cycles-to-homology projection is an epimorphism. The
proved finite-free local lifting theorem lifts the surjection across this
projection after covering. Composing with the cycle inclusion gives a map from
a finite free constant sheaf in degree b to the representative complex.
Its cone has cohomology in [a,b-1]. The long exact sequence identifies its next-to-top
cohomology as an extension of the old cohomology by the kernel of a map between
finite constant sheaves. Noetherianity and the locally constant finite Serre property
therefore give the induction hypotheses for this cone. Apply induction on each slice.
The proved bounded-top chain-representative theorem realizes the boundary from
its bounded model to the free constant sheaf in degree b-1 by an actual chain map.
It uses the cycles-to-cohomology quotient at the top degree and injectivity of
top cohomology on morphisms across the canonical t-structure. The
shifted cone appends that sheaf in degree b and has the required finite constant
terms and bounds. Rotation of triangles and the morphism-of-triangles axiom identify
it with the restricted original object, since the comparisons on the two other
objects are isomorphisms. Compose the finite covering refinements. Empty slices
use zero modules. This construction does not require descending the differentials
to module maps; that is the separate finite-complex descent theorem. -/
theorem exists_site_bounded_constant_graded_model
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (X : C) (hX : IsTerminal X)
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    [HasDerivedCategory.{w} (Sheaf J.toGrothendieck (ModuleCat.{u} B))]
    [∀ U : C, HasDerivedCategory.{w}
      (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B))]
    (K : DerivedCategory (Sheaf J.toGrothendieck (ModuleCat.{u} B)))
    (a b : ℤ) (hab : a < b)
    (hvan : ∀ q : ℤ, q < a ∨ b < q → IsZero
      ((DerivedCategory.homologyFunctor (Sheaf J.toGrothendieck (ModuleCat.{u} B)) q).obj K))
    (hloc : ∀ (q : ℤ) (V : C),
      ∃ (I : Type u) (U : I → C) (f : ∀ i : I, U i ⟶ V),
        Presieve.ofArrows U f ∈ J V ∧
        ∀ i : I, ∃ M : ModuleCat.{u} B, Module.Finite B M ∧ Nonempty
          ((J.toGrothendieck.overPullback (ModuleCat.{u} B) (U i)).obj
            ((DerivedCategory.homologyFunctor
              (Sheaf J.toGrothendieck (ModuleCat.{u} B)) q).obj K) ≅
            (constantSheaf (J.toGrothendieck.over (U i)) (ModuleCat.{u} B)).obj M)) :
    ∃ (I : Type u) (U : I → C) (f : ∀ i : I, U i ⟶ X),
      Presieve.ofArrows U f ∈ J X ∧
      ∀ i : I, ∃ P : CochainComplex
          (Sheaf (J.toGrothendieck.over (U i)) (ModuleCat.{u} B)) ℤ,
        ∃ M : ℤ → ModuleCat.{u} B,
          (∀ q : ℤ, Module.Finite B (M q)) ∧
          (∀ q : ℤ, q < a ∨ b < q → IsZero (M q)) ∧
          (∀ q : ℤ, Nonempty (P.X q ≅
            (constantSheaf (J.toGrothendieck.over (U i)) (ModuleCat.{u} B)).obj (M q))) ∧
          Nonempty
            ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
                (J.toGrothendieck.overPullback (ModuleCat.{u} B) (U i))
                (Functor.additive_of_preserves_binary_products _) _
                ⟨fun _ _ _ ↦ PreservesColimitsOfSize.preservesColimitsOfShape
                  (self := Adjunction.leftAdjoint_preservesColimits
                    (Functor.sheafAdjunctionCocontinuous
                      (Over.forget (U i)) (ModuleCat.{u} B)
                      (J.toGrothendieck.over (U i)) J.toGrothendieck))⟩).obj K ≅
              DerivedCategory.Q.obj P) := by sorry

end CategoryTheory
