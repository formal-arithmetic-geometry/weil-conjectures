/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.SpaceEtaleSourceAtlasDetection
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# The unmarked finite-open-part algebraic space

Source: Stacks Project, More on Groupoids in Spaces, Tag 04QH, equation (04PD)
and Tag 04PE (blueprint: lem-sfb-unmarked-finite-open-parts-space).

The bijections identify actual sheaf sections with pairs consisting of a map to the
target and an open of the scheme fibre product, finite over the test scheme.
Their naturality is written using the uniquely determined map of fibre products,
so no equality transport of dependent open-set types is hidden in the statement.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The finite-open-part functor of a separated locally finite type scheme morphism is an
algebraic space, and its forgetful map to the target is chartwise étale. The sigma type
is the pair set P(T). The second conjunct says precisely that sheaf restriction pulls
back the pair: the two projection equations uniquely specify the fibre-product map.
The atlas in `E.property` consists of schemes in the same universe as `S`.
Source: Stacks Project, More on Groupoids in Spaces, Tags 04PC, 04PD, 04PE and 04QH
(blueprint: lem-sfb-unmarked-finite-open-parts-space).

Proof:
1. Pull back maps and open parts along test-scheme maps. Open immersions and finite
   morphisms survive base change (lem-weil-pbc-open-immersion-base-change and
   lem-weil-pbc-finite-morphism-permanence). Fibre-product uniqueness gives the functor
   laws. The lemma lem-sfb-finite-open-parts-fppf-sheaf gives fppf descent for these pairs.
2. For pairs with the same target map, lem-sfb-finite-open-equality-locus represents
   their equality by an open of the test scheme. For different target maps first take
   their scheme equalizer, then this open equality locus. The absolute diagonal is
   consequently representable by schemes, using def-pc-fibre-product.
3. Use lem-sfb-finite-open-geometric-chart-family to choose étale target charts and
   finite open parts on them. Their Yoneda maps to P are representable étale: a test
   pullback is the open equality locus inside the fibre product with the target chart.
   Apply lem-weil-pbc-etale-base-change-finite-limits and
   lem-weil-pbc-etale-composition-cancellation to its projection.
4. Take the small coproduct of these charts (lem-weil-pbc-scheme-coproduct-family).
   Glue their pairs using the sheaf condition. On tests its pullback is the coproduct
   of the equality loci, hence étale by lem-weil-pbc-etale-local-on-source. The coproduct
   is in the chosen universe by def-weil-size-convention.
5. For each point of a test scheme, restrict the pair to its residue field. The lifting
   property of lem-sfb-finite-open-geometric-chart-family, and
   lem-weil-pbc-morphism-from-spec-field, give a point of this atlas pullback over it.
   Thus the atlas projection is surjective on every scheme test.
6. The sheaf, diagonal and atlas give def-trf-algebraic-space. Its sections are the
   pair sets and its restriction is the stated pullback. The atlas composite to Y is
   étale; scheme fibre products show that its Yoneda map is representable étale.
   Regard Y as def-trf-scheme-algebraic-space and apply clause (3) of
   lem-trf-space-etale-source-atlas-detection. Testing the resulting representable
   étale composite of any scheme chart with p on the identity of Y proves the final
   scheme-étaleness assertion. No separation or representability of p is required. -/
theorem exists_unmarked_finite_open_parts_space {S : Scheme.{u}} (X Y : Over S)
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] :
    ∃ (E : AlgebraicSpace S) (p : E.obj.obj ⟶ yoneda.obj Y)
      (e : ∀ T : Over S, E.obj.obj.obj (op T) ≃
        (Σ a : T ⟶ Y, {Z : (pullback f.left a.left).Opens //
          IsFinite (Z.ι ≫ pullback.snd f.left a.left)})),
      (∀ (T : Over S) (x : E.obj.obj.obj (op T)),
        (e T x).1 = p.app (op T) x) ∧
      (∀ (T T' : Over S) (h : T' ⟶ T) (x : E.obj.obj.obj (op T)),
        ∃ b : pullback f.left (e T' (E.obj.obj.map h.op x)).1.left ⟶
            pullback f.left (e T x).1.left,
          b ≫ pullback.fst f.left (e T x).1.left =
            pullback.fst f.left (e T' (E.obj.obj.map h.op x)).1.left ∧
          b ≫ pullback.snd f.left (e T x).1.left =
            pullback.snd f.left (e T' (E.obj.obj.map h.op x)).1.left ≫ h.left ∧
          (e T' (E.obj.obj.map h.op x)).2.val = b ⁻¹ᵁ (e T x).2.val) ∧
      (∀ (V : Over S) (c : yoneda.obj V ⟶ E.obj.obj),
        AlgebraicSpace.IsEtale c → Etale (yoneda.preimage (c ≫ p)).left) := by
  sorry

end AlgebraicGeometry
