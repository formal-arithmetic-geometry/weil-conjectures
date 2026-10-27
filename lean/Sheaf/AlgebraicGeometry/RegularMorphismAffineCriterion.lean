module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.RegularSchemeMorphism
public import WeilConjectures.RingTheory.GRing

import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.RingTheory.FibreRingNoetherian

/-! # Regular morphisms on affine coordinate rings

Source: Stacks Project, More on Morphisms, Tag 07R8, lemma-regular, (2) iff (3)
(blueprint: lem-per-regular-morphism-affine-criterion).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism of locally Noetherian schemes is regular exactly when its induced maps
on all compatible affine opens are regular ring maps. The map `f.appLE V U h` is
`f.app V` followed by restriction from `f ⁻¹ᵁ V` to `U`.

Source: Stacks Project, More on Morphisms, Tag 07R8, lemma-regular, (2) iff (3)
(blueprint: lem-per-regular-morphism-affine-criterion).

Proof:
1. For affine opens `U = Spec B` and `V = Spec A` with `f(U) ⊆ V`, and a point
   `y ∈ V` corresponding to a prime `p`, identify the scheme residue field with
   `κ(p)` using lem-weil-pbc-spec-residue-field-identification. By
   lem-weil-pbc-open-fibre-product and lem-weil-pbc-fibre-product-affine-spectra,
   the open fibre `U_y` in `X_y` is `Spec (B ⊗[A] κ(p))`. These opens cover each
   fibre. By pqf-lem-affine-open-locnoeth, `B` is Noetherian; by
   lem-weil-pbc-fibre-ring-noetherian, its fibre ring is Noetherian. Thus each
   scheme fibre is locally Noetherian, as required by Tag 07R8.
2. If `f` is regular, def-per-regular-scheme-morphism gives flatness and regularity
   of every fibre after each finite residue-field extension. By
   lem-weil-pbc-flat-morphism-affine-criterion the map `A → B` is flat. Apply
   lem-per-geometric-regularity-affine-cover, (1) implies (2), to `X_y` and `U_y`.
   Each fibre ring is geometrically regular. Together with flatness this is
   precisely def-weil-pbc-g-ring's regularity of `A → B`.
3. Conversely, suppose all these ring maps are regular. Their flatness implies
   flatness of `f` by lem-weil-pbc-flat-morphism-affine-criterion. For each `y`,
   their geometrically regular fibre rings give the affine cover of `X_y` from
   step 1. Apply lem-per-geometric-regularity-affine-cover, (3) implies (1), to
   obtain regularity after every finite extension of `κ(y)`. Together with
   flatness, these are the conditions of def-per-regular-scheme-morphism. -/
theorem isRegularSchemeMorphism_iff_regular_appLE
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) :
    IsRegularSchemeMorphism f ↔
      ∀ (U : X.Opens) (V : Y.Opens), IsAffineOpen U → IsAffineOpen V →
        ∀ (h : U ≤ f ⁻¹ᵁ V), RingHom.IsRegular (f.appLE V U h).hom := by
  sorry

end AlgebraicGeometry
