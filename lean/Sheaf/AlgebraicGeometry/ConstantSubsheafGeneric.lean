/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Generic constancy of a subsheaf of a constant finite sheaf

Source: Stacks Project, Tag 03RY, Proposition 59.74.1(3), with Tag 03RZ,
Lemma 59.71.6 (blueprint: lem-weil-pbc-constant-subsheaf-generic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- A subsheaf of a finite constant module sheaf becomes constant on a nonempty open.

The proof follows Tags 03RZ and 03RY: loci of stalk elements are open, and on an
irreducible scheme their finite intersection over the generic stalk is a nonempty open;
the resulting stalkwise identification is an isomorphism by conservativity of geometric
stalks. Source: Stacks Project, Tags 03RY and 03RZ
(blueprint: lem-weil-pbc-constant-subsheaf-generic).

1. For every element m of M, represent membership in a geometric stalk by a section on
   an etale neighbourhood, refined until its image is the constant section m. Its image
   is open by `lem-weil-pbc-flat-lfp-open`; the union of these images is the locus W_m.
   Membership is independent of the geometric point over the underlying point.
2. Let M' be the generic stalk. Every nonempty W_m contains η, so elements outside M'
   have empty locus. Intersect the finitely many W_m for m in M': this contains η.
   On this open the stalks of H equal M'. The natural inclusion of the constant M'
   sheaf into H is an isomorphism at all geometric stalks, hence an isomorphism by
   `lemma-weil-pbc-geometric-stalk-conservative`, compatible with the inclusions into M. -/
theorem constant_subsheaf_generic
    (W : Scheme.{u}) [Nonempty W] [IrreducibleSpace W]
    (η : W) (_hη : IsGenericPoint η Set.univ)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (H : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hH : H ⟶ (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
    [Mono hH] :
    ∃ (U : W.Opens) (_hU : (U : Set W).Nonempty) (M' : Submodule Λ M),
      ∃ (e : ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj H) ≅
          (constantSheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ M')),
        e.hom ≫
            (constantSheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
              (ModuleCat.ofHom (Submodule.subtype M')) =
          (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).map hH ≫
            (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) U.ι).hom.app M := by
  sorry

end AlgebraicGeometry
