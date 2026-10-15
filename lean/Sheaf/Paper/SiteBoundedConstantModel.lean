/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact
import Sheaf.CategoryTheory.TruncationDescends
import Sheaf.Paper.SiteSheafificationSectionsLocal
import Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-! # Local bounded constant models on a small site

Source: Stacks Project, Cohomology on Sites, Tag 094G, proof of
`lemma-locally-constant` (blueprint: lem-weil-pbc-site-bounded-constant-model).

Constant-coefficient module sheaves are encoded as `Sheaf J (ModuleCat B)`:
restriction is precomposition on the slice, and the constant complex is obtained
by applying the constant-sheaf functor to both terms and differentials.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A bounded object with locally constant finite cohomology has local constant
finite-module complex models, with the same degree bounds.

Source: Stacks Project, Tag 094G, strengthened assertion in the induction in the
proof of `lemma-locally-constant`.
(blueprint: lem-weil-pbc-site-bounded-constant-model)

Proof: Induct on `b - a`. Exact slice restriction preserves cohomology and cones
(lem-pur-site-restriction-module-adjunction-exact); constant sheaves restrict to
constant sheaves (lem-weil-pbc-site-constant-restriction), and successive coverings
compose. On empty slices use the zero complex. If `a = b`, canonical truncation
(lem-weil-pbc-truncation-descends) identifies the object with its single nonzero
cohomology sheaf; trivialize that sheaf. Otherwise trivialize the top cohomology
as a finite module M and choose finitely many generators. Exact sheafification
(lem-weil-pbc-site-module-presheaf-sheafification-exact) and local representatives
(lem-weil-pbc-site-sheafification-sections-local) lift the generators locally to
cycles, giving a map from a constant finite free module in degree b. Its cone
has cohomology in [a,b-1]; the long exact sequence
(lem-sf-derived-homology-long-exact) and the Serre property
(lem-weil-pbc-locally-constant-derived-serre) give locally constant finite
cohomology. Apply induction. Represent the boundary to the free module shifted
by b-1 using a right fraction (lem-pc-right-fraction-representation and
lem-pc-quasi-isomorphisms-multiplicative-system). Upper truncate the roof;
its top component factors through top cohomology and hence yields an actual
chain map out of the constant model. Its top component locally comes from a
module map (lem-weil-pbc-site-constant-morphism-local). On a nonempty slice,
local equality in the constant presheaf makes the constant functor faithful,
so this module map annihilates the preceding differential. Append the free
module in degree b. The resulting constant complex is the shifted cone of the
boundary; rotation and the morphism-of-triangles axiom
(def-weil-triangulated-category), followed by the long exact cohomology
sequence, identify it with the original object. Compose the finitely many
covering refinements. No points or Tor-amplitude assumption is used. -/
theorem exists_site_bounded_constant_model
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (X : C) (hX : IsTerminal X)
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    [HasDerivedCategory.{w} (Sheaf J.toGrothendieck (ModuleCat.{u} B))]
    [∀ U : C, HasDerivedCategory.{w}
      (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B))]
    (K : DerivedCategory (Sheaf J.toGrothendieck (ModuleCat.{u} B)))
    (a b : ℤ) (hab : a ≤ b)
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
      ∀ i : I, ∃ M : CochainComplex (ModuleCat.{u} B) ℤ,
        (∀ q : ℤ, Module.Finite B (M.X q)) ∧
        (∀ q : ℤ, q < a ∨ b < q → IsZero (M.X q)) ∧
        Nonempty
          ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
              (J.toGrothendieck.overPullback (ModuleCat.{u} B) (U i))
              (Functor.additive_of_preserves_binary_products _) _
              ⟨fun _ _ _ ↦ PreservesColimitsOfSize.preservesColimitsOfShape
                (self := Adjunction.leftAdjoint_preservesColimits
                  (Functor.sheafAdjunctionCocontinuous
                    (Over.forget (U i)) (ModuleCat.{u} B)
                    (J.toGrothendieck.over (U i)) J.toGrothendieck))⟩).obj K ≅
            DerivedCategory.Q.obj
              ((Functor.mapHomologicalComplex
                (constantSheaf (J.toGrothendieck.over (U i)) (ModuleCat.{u} B))
                (ComplexShape.up ℤ)).obj M)) := by
  sorry

end CategoryTheory
