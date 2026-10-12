/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence

/-!
# Naturality of acyclic-resolution comparisons

Source: literature/stacks-project/derived.tex, Tag 015E (blueprint:
`lem-sc-acyclic-comparison-natural`).
-/

@[expose] public section

universe u v u' v'

namespace CategoryTheory

open Limits

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] [Abelian C]
  [HasInjectiveResolutions C] [Abelian D]

/-- Naturality of the comparison from an acyclic resolution to a right derived functor.

(blueprint: lem-sc-acyclic-comparison-natural).

Source: Stacks Project, Tag 015E, canonical acyclic-resolution comparison.
The comparison maps are the inverses of `F.rightDerivedObjIsoOfResolution`.

Proof (the four steps of the node):
1. Choose injective resolutions of `X` and `X'`, and a lift of `h` between them using
   `lem-weil-pbc-injective-resolution-lift-exists`. The augmentations are degreewise-monic
   quasi-isomorphisms. Use `lem-weil-pbc-lift-along-injective-quasi-iso` to lift their identity
   maps into the injective resolutions. Item 2 of `lemma-weil-pbc-leray-acyclicity` identifies
   the induced homology maps with the displayed comparison isomorphisms.
2. The two composites from `I` to the injective resolution of `X'` agree after `ι`, by `w`.
   They are homotopic by `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`.
3. Apply the additive functor `F` to this homotopy. By
   `lem-weil-pbc-homotopic-maps-equal-cohomology`, the induced homology maps agree.
4. Identify the homology map of the lift of `h` with `(F.rightDerived n).map h` using
   `lem-weil-pbc-derived-functor-map-via-lift`. Substitute the comparison maps in the equality
   from Step 3 to obtain the displayed square.
(blueprint: lem-sc-acyclic-comparison-natural).
-/
theorem acyclicComparison_naturality
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    {X X' : C} {I I' : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ I)
    (ι' : (CochainComplex.single₀ C).obj X' ⟶ I')
    [QuasiIso ι] [QuasiIso ι']
    (hI : ∀ n, F.rightAcyclic (I.X n))
    (hI' : ∀ n, F.rightAcyclic (I'.X n))
    (h : X ⟶ X') (φ : I ⟶ I')
    (w : ι ≫ φ = (CochainComplex.single₀ C).map h ≫ ι')
    (n : ℕ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) n ≫
        (F.rightDerivedObjIsoOfResolution ι' hI' n).inv =
      (F.rightDerivedObjIsoOfResolution ι hI n).inv ≫ (F.rightDerived n).map h := by
  sorry

end CategoryTheory
