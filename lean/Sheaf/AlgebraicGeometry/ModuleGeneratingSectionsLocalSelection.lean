/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.Coherent

/-! # Finite support of a generating family near a point

Source: Stacks Project, Modules, Lemmas 01BB and 01B8.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- Near any point of an open on which a module sheaf is finite type, finitely many
members of a specified global generating family generate. Compactness is not assumed.

Source: Stacks Project, Modules, Lemma 01BB, first paragraph of the proof, applied
to the directed finite sub-coproducts of the free sheaf; Lemma 01B8.
https://stacks.math.columbia.edu/tag/01BB
https://stacks.math.columbia.edu/tag/01B8
(blueprint: lem-weil-pbc-module-generating-sections-local-selection).

Proof: Restrict to K and choose a finite local generating family near x, using
finite type. The given epimorphism from the free sheaf on sigma.I locally lifts
these finitely many generators, after intersecting finitely many neighbourhoods.
Each lifted germ is a finite sum of basis germs: the free sheaf is the filtered
colimit of its finite sub-coproducts, and stalks preserve this colimit. Take the
union S of the supports of these finitely many germs. Represent their lifts in
the finite free sheaf on S and shrink the neighbourhood so that the images of
the lifts equal the chosen generating sections as sections. The finite-support
map is then epi on this neighbourhood because its image contains the local
generators. Restriction preserves free sheaves and their basis maps, so this is
the stated overMap morphism. If the local generating family is empty, choose
S empty: the restricted target is zero. If sigma.I is empty, its epimorphism
already forces the target to vanish, so again S empty works. There is no point
x to consider if K is empty. No quasi-coherence or finite presentation is used.
-/
theorem exists_finset_generatingSections_near_point
    (X : Scheme.{u}) (V K : X.Opens) (hKV : K ≤ V)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [(H.over K).IsFiniteType] (σ : (H.over V).GeneratingSections) (x : K) :
    ∃ (U : X.Opens) (hUK : U ≤ K), (x : X) ∈ U ∧ ∃ S : Finset σ.I,
      Epi ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE (hUK.trans hKV))).map
          (SheafOfModules.freeMap (R := (moduleRings X.toRingedSpace).over V)
            ((↑) : S → σ.I) ≫ σ.π)) := by sorry

end AlgebraicGeometry.Scheme.Modules
