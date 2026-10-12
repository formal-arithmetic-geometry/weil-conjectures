/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf

/-!
# Inverse image of representable sheaves on the small étale site

Source: Stacks Project, Étale Cohomology, Tag 03Q1, part (4), and Sites, Tag 04D3
(blueprint: lem-galois-inverse-image-representable).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Inverse image carries the representable sheaf of an étale `Y`-scheme to the
representable sheaf of its base change, naturally in the étale `Y`-scheme.
Source: Stacks Project, Tag 03Q1 (4), and Tag 04D3
(blueprint: lem-galois-inverse-image-representable).

Here `f.Etale` sends `V` to `V ×_Y X` with projection to `X`; symmetry of the
scheme fibre product identifies this with `X ×_Y V` with its first projection.
The existing subcanonical instance packages the representable presheaves as sheaves,
as asserted by `lem-weil-pbc-small-etale-representable-presheaf-sheaf`.
`uliftYoneda` only raises the universe of the sets of morphisms.

Proof:
1. Étale morphisms are stable under base change
(`lem-weil-pbc-etale-scheme-base-change`), and the fibre-product universal property
(`def-pc-fibre-product`) gives the functor `f.Etale`.
2. The adjunction identifies maps from `L(h_V)` to `F` with maps from `h_V` to
`f_* F`. The representable-sheaf lemma above, the full sheaf subcategory
(`def-weil-pbc-etale-sheaf-of-sets`), and Yoneda
(`lem-galois-yoneda-hom-bijection`) identify these with `(f_* F)(V)`.
3. By direct-image evaluation this is `F(V ×_Y X)`. The same representable-sheaf
lemma and Yoneda identify it with maps from `h_(V ×_Y X)` to `F`, naturally in `F`.
4. Apply `lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection` to these Hom bijections.
Naturality of adjunction, Yoneda evaluation, and base change in a morphism `V → V'`
shows that the resulting objectwise isomorphisms form the asserted natural isomorphism.
-/
theorem nonempty_inverseImage_representable_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Sheaf Y.smallEtaleTopology (Type (max u v)) ⥤
      Sheaf X.smallEtaleTopology (Type (max u v)))
    (_adj : L ⊣ f.Etale.sheafPushforwardContinuous (Type (max u v))
      Y.smallEtaleTopology X.smallEtaleTopology) :
    Nonempty
      (Y.smallEtaleTopology.uliftYoneda.{v} ⋙ L ≅
        f.Etale ⋙ X.smallEtaleTopology.uliftYoneda.{v}) := by
  sorry

end AlgebraicGeometry
