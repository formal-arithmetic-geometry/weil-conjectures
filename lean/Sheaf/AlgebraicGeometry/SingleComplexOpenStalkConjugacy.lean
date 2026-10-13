/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Source-open conjugacy of the canonical stalk comparison

Source: Stacks Project, Tag 0DJ8, locality of equation-bc on X'; Tag 0DJ9,
source-open induction.
(blueprint: lem-pc-single-complex-open-stalk-conjugacy).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

/-- The original and source-open comparisons are isomorphic as additive arrows.
No invertibility of either comparison is assumed.

Proof: write j = U.ι, p = pullback.fst g' j, q = pullback.snd g' j.
The base change p of j is an open immersion. Restrict c.P and c.N termwise along
j and p. Exact restriction preserves K-flatness, and its derived functor is
canonically derived pullback on an open immersion. The underived pullback
composition isomorphisms give a chain map from q* of the restricted source to
the restricted target. The defining universal-counit equation for the derived
composition comparisons gives its represents equation for the displayed phiU.
This produces coordinates r for phiU with the restricted representatives.

At z, the isomorphisms j.stalkMap (q z) and p.stalkMap z identify the original
rings A and C with the restricted rings. The commutative square identifies the
base rings R and B; the stalkMap_comp equations identify their algebra actions.
The restriction-stalk extension isomorphisms identify the complexes degreewise.
Thus derived tensor over R with B gives an isomorphism of the model cohomology
objects, compatible with the A-tensor-R-B action (multiplication is natural).
After extension to C this gives the source vertical isomorphism. Exact stalks
and cohomology give the target vertical isomorphism. The comparison_eq and
localized_eq equations of the cohomology models identify their horizontal maps
with the universal derived tensor counits and their scalar-extension transposes.
Naturality of these counits, of tensorStalkIso, and of the restricted chain map
therefore gives a commuting square for c and r.

For arbitrary d, its e and e' compared with those of r give derived isomorphisms
of the representatives. Apply the same source transport and pullback naturality
used in coordinate invariance: after normalizing the targets by e', both maps
are induced by phiU because of represents. These give another commuting square
with invertible vertical maps for r and d. Compose the squares and forget the
module scalars. Arrow.isoMk packages the two additive isomorphisms and the
commutativity equation. This uses no flatness over R and does not assert that
the localized comparison itself is invertible. For an empty open there is no z;
for the top open the same ring isomorphisms apply. Zero complexes and zero rings
are also allowed, since every transport is through a ring or derived isomorphism.
Source: Stacks Project, perfect.tex, Tag 0DJ8, proof of locality of condition (1);
Tag 0DJ9, the comparison for U and its inverse image.
(blueprint: lem-pc-single-complex-open-stalk-conjugacy). -/
theorem nonempty_stalkComparison_open_arrow_iso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (c : Coordinates g' K K' φ)
    (U : X.Opens)
    (sqU : IsPullback (pullback.snd g' U.ι) (pullback.fst g' U.ι ≫ f') (U.ι ≫ f) g) :
    let φU :=
      ((Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))))
        (pullback.snd g' U.ι) U.ι).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
        (pullback.condition (f := g') (g := U.ι)).symm) ≫
      ((Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))))
        (pullback.fst g' U.ι) g').inv.app K ≫
      (derivedPullback (pullback.fst g' U.ι)).map φ
    ∀ (d : Coordinates (pullback.snd g' U.ι) ((derivedPullback U.ι).obj K)
        ((derivedPullback (pullback.fst g' U.ι)).obj K') φU)
      (z : (pullback g' U.ι : Scheme.{u})) (i : ℤ),
      Nonempty
        (Arrow.mk ((forget₂ (ModuleCat.{u} (X'.presheaf.stalk (pullback.fst g' U.ι z)))
            AddCommGrpCat.{u}).map
              (stalkComparison f f' g g' sq c (pullback.fst g' U.ι z) i)) ≅
          Arrow.mk ((forget₂ (ModuleCat.{u} ((pullback g' U.ι).presheaf.stalk z))
            AddCommGrpCat.{u}).map
              (stalkComparison (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
                g (pullback.snd g' U.ι) sqU d z i))) := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
