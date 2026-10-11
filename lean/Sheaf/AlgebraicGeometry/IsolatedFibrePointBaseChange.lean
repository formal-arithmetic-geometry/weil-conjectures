import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Points isolated in their fibre stay isolated after base change

Source: literature/stacks-project/morphisms.tex, Lemma 01TM (1)
(blueprint: lem-weil-pbc-isolated-fibre-point-base-change).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Source: literature/stacks-project/morphisms.tex, Lemmas 01TM (1) and 01TH (1)-(2);
literature/stacks-project/algebra.tex, proof of Lemma 00PP (1).
(blueprint: lem-weil-pbc-isolated-fibre-point-base-change).
If a point is isolated in the fibre of a locally finite type morphism, then
any point above it after base change is isolated in the new fibre.

Proof:
1. By `lem-weil-pbc-fibre-of-base-change`, identify the new fibre with the base change
   of the old fibre along the residue field extension. Its map to the old fibre sends
   the new fibre point to the old one: use commutativity of the fibre projections and
   their injectivity (`def-pc-scheme-fibre`). The old singleton is open by hypothesis.
2. Let W be the open subscheme consisting of this singleton (`def-weil-open-immersion`).
   Its inclusion is locally of finite type by `lem-weil-pbc-immersion-base-change-lft` (2).
   The old fibre is locally of finite type over its residue field by
   `lem-weil-pbc-lft-base-change`; composition with the inclusion is locally of finite
   type by `lem-weil-pbc-proper-fp-permanence` (e). The one-point space W is discrete.
3. By `lem-weil-pbc-discrete-field-base-change-artinian`, the base change of W along
   the residue field extension is discrete. By `lem-weil-pbc-open-fibre-product`, its
   map into the new fibre is an open immersion (`def-weil-open-immersion`) whose image
   is the inverse image of W. Thus this inverse image is both open and discrete.
4. The chosen new fibre point belongs to this inverse image. Its singleton is open
   there by discreteness, and hence is open in the whole new fibre.
-/
theorem isolated_fiber_point_base_change
    {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (x' : ↥(pullback f g))
    (hx : IsOpen ({f.asFiber (pullback.fst f g x')} :
      Set (f.fiber (f (pullback.fst f g x'))))) :
    IsOpen ({(pullback.snd f g).asFiber x'} :
      Set ((pullback.snd f g).fiber ((pullback.snd f g) x'))) := by
  sorry

end AlgebraicGeometry
