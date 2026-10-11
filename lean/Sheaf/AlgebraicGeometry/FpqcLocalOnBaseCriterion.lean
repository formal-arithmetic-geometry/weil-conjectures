/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: K1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Sites.Fpqc

universe u w

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-!
# Criterion for a property of morphisms to descend along fpqc coverings

Source: Stacks Project, Descent, Lemma Tag 02KP
(blueprint: lem-weil-pbc-fpqc-local-on-base-criterion).
-/

/-- A property of morphisms satisfying invariance under isomorphism, flat base change,
Zariski locality on the base, and affine faithfully-flat descent descends along fpqc coverings.
Source: Stacks Project, Descent, Lemma Tag 02KP and Definition Tag 02KO;
Topologies, Definition Tag 022B and Lemma Tag 022E
(blueprint: lem-weil-pbc-fpqc-local-on-base-criterion).

The isomorphism invariance and Zariski locality are encoded by `IsZariskiLocalAtTarget P`.
Its preservation of open restrictions follows from `hflat`, since open immersions are flat.
Thus its two-way locality adds nothing to conditions (0), (1), and (2) of the node.

Proof (the seven steps of the node, expanding the source's omitted details):
1. Reduce by Zariski locality to each affine open `U` of `S` (`def-pc-scheme`).
2. Refine the fpqc family over `U` by finitely many affine opens `V_j` of its members,
   whose images cover `U` (022E and `def-weil-pbc-fpqc-covering`).
3. Their finite disjoint union `U'` is affine (`lem-weil-pbc-affine-morphism-permanence`)
   and maps surjectively to `U`. The component inclusions cover `U'`
   (`lem-weil-pbc-scheme-coproduct-family`), and their stalk maps are isomorphisms
   (`def-weil-open-immersion`), so this map is flat (`def-weil-flat-morphism`) and
   surjective (`def-weil-surjective-morphism`). The empty union is `Spec 0`.
4. Base change each given `P`-morphism to `V_j` by the flat open inclusion using `hflat`.
   Open preimages are fibre products (`lem-weil-pbc-open-preimage-fibre-product`);
   uniqueness (`def-pc-fibre-product`), invariance under isomorphisms, and cartesian
   pasting (`lem-weil-pbc-cartesian-square-pasting`) identify these with the required
   base changes of the restriction of `f` to `U`.
5. Restrict its base change to `U'` to the component images. The component-to-image
   isomorphisms (`lem-weil-pbc-open-immersion-iso-onto-image`), open-preimage fibre
   products, and cartesian pasting identify these restrictions with step 4.
   Isomorphism invariance and Zariski locality on `U'` give `P` for this base change.
6. Apply `hdesc` to the flat surjection `U' ⟶ U` between affine schemes; uniqueness
   of fibre products transports `P` to the chosen pullback if necessary.
7. Every affine restriction of `f` has `P`; the affine opens cover `S`, so Zariski
   locality gives `P f`. -/
theorem fpqc_local_on_base_criterion
    (P : MorphismProperty Scheme.{u})
    (hflat : ∀ {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S),
      Flat g → P f → P (pullback.snd f g))
    [IsZariskiLocalAtTarget P]
    (hdesc : ∀ {S T X : Scheme.{u}} [IsAffine S] [IsAffine T]
      (f : X ⟶ S) (g : T ⟶ S),
      Flat g → Surjective g → P (pullback.snd f g) → P f)
    {S : Scheme.{u}} {Z : Scheme.{u}} (f : Z ⟶ S)
    {ι : Type w} {S' : ι → Scheme.{u}} (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (H : ∀ i, P (pullback.snd f (g i))) : P f := by
  sorry

end AlgebraicGeometry
