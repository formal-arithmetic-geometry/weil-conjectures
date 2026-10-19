/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.RelativeFlatModuleStalk
import WeilConjectures.AlgebraicGeometry.RelativeFlatOfStalks
import Sheaf.RingTheory.FlatnessFaithfullyFlatExtension

/-!
# Relative flatness detected on a flat source cover

Source: Stacks Project, Morphisms, Tag 02JZ, `lemma-flat-permanence`, with the
pointwise definition in Tag 01U3 and its affine-section characterization in Tag 01U4
(blueprint: lem-trf-relative-flatness-source-cover).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

set_option autoImplicit false

/-- Relative flatness of a quasi-coherent module is detected pointwise by a morphism
flat at the chosen point, and globally by any jointly surjective family of flat morphisms.
The pointwise scalar actions are restriction along the respective scheme stalk maps;
the global condition is the recorded affine-section predicate `IsFlatOver`.

Source: Stacks Project, Morphisms, Tag 02JZ, `lemma-flat-permanence`; Tags 01U3 and 01U4
(blueprint: lem-trf-relative-flatness-source-cover).

Proof:
1. For a point `x`, put `y = h x`, `s = f y`, `A = O_{S,s}`, `B = O_{Y,y}`,
   `C = O_{X,x}`, and `N = G_y`. The local stalk map `B → C` is flat by hypothesis,
   hence faithfully flat by lem-pc-local-flat-faithful-flat-reflects-surjective.
   The isomorphism lem-weil-pbc-module-stalk-pullback identifies the pulled-back stalk
   with `C ⊗[B] N`. Functoriality of the scheme stalk maps identifies its `A`-action
   with that through `h ≫ f`.
2. Apply lem-trf-flatness-faithfully-flat-extension to `A → B → C` and `N`.
   Flatness of `N` over `A` is equivalent to flatness of `C ⊗[B] N` over `A`.
   The stalk isomorphism of Step 1 gives the first conjunct.
3. For the family, lem-weil-pbc-module-pullback-quasi-coherent gives quasi-coherence
   of every pulled-back module. If `G.IsFlatOver f`, lem-pc-relative-flat-module-stalk
   gives flatness at every point of `Y`; Step 2 gives flatness at every point of each
   `X i`, and lem-pc-relative-flat-of-stalks gives the required global flatness there.
   Conversely, apply lem-pc-relative-flat-module-stalk to each pulled-back module.
   For each `y`, joint surjectivity supplies `i` and `x` with `h i x = y`.
   Step 2 then gives flatness of `G` at `y`, and lem-pc-relative-flat-of-stalks gives
   `G.IsFlatOver f`. This also applies to empty schemes and empty covering families. -/
theorem relative_flatness_source_cover {Y S : Scheme.{u}} (f : Y ⟶ S)
    (G : Y.Modules) [G.IsQuasicoherent] :
    (∀ (X : Scheme.{u}) (h : X ⟶ Y) (x : X), (h.stalkMap x).hom.Flat →
      (Module.Flat (S.presheaf.stalk (f (h x)))
        ((ModuleCat.restrictScalars (f.stalkMap (h x)).hom).obj
          ((RingedSpace.moduleStalkFunctor Y.toRingedSpace (h x)).obj G)) ↔
       Module.Flat (S.presheaf.stalk ((h ≫ f) x))
        ((ModuleCat.restrictScalars ((h ≫ f).stalkMap x).hom).obj
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
            ((Scheme.Modules.tensorPullback h).obj G))))) ∧
    (∀ (I : Type v) (X : I → Scheme.{u}) (h : ∀ i : I, X i ⟶ Y),
      (∀ i : I, Flat (h i)) →
      (∀ y : Y, ∃ (i : I) (x : X i), h i x = y) →
      (G.IsFlatOver f ↔
        ∀ i : I, ((Scheme.Modules.tensorPullback (h i)).obj G).IsFlatOver (h i ≫ f))) := by
  sorry

end AlgebraicGeometry
