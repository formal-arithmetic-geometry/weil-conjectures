module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sober

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.Irreducible
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Sections of separated morphisms that are isomorphisms over a nonempty open

Source: Stacks Project, Varieties, Tag 0BFP, final paragraph of proof (4);
Schemes, Tags 01KT and 0356
(blueprint: lem-sfb-integral-generic-section-isomorphism).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A section of a separated morphism between integral schemes that is an isomorphism
over a nonempty open is its inverse and takes the generic point to the generic point.

Source: Stacks Project, Varieties, Tag 0BFP, final paragraph of proof (4);
Schemes, Tags 01KT and 0356
(blueprint: lem-sfb-integral-generic-section-isomorphism).

Proof:
1. By `lem-weil-pbc-section-separated-closed-immersion`, the section `s` is a closed
   immersion: apply `IsClosedImmersion.of_comp` to `s` and `f`, using `hs` and
   separatedness of `f`. Thus its image `C` is closed in `Y`.
2. Choose the nonempty open `V` in the hypothesis and put `W = f ⁻¹ᵁ V`. The
   isomorphism `f ∣_ V` makes `W` nonempty. For `y` in `W`, the section identity
   gives `f (s (f y)) = f y`; both points lie in `W`, so injectivity of the restricted
   isomorphism gives `s (f y) = y`. Hence `W` lies in `C`. Integrality makes `Y`
   irreducible, so its nonempty open `W` is dense. Closedness of `C` yields `C = Y`.
3. Integrality also makes `Y` reduced. Apply
   `lem-weil-pbc-reduced-source-factors-through-closed-subscheme`, namely
   `IsClosedImmersion.existsUnique_fac_of_range_subset_range`, to `s` and the
   identity of `Y`. Step 2 gives its range containment. This produces `t : Y ⟶ X`
   with `t ≫ s = 𝟙 Y`. The section identity implies `t = f`, proving `f ≫ s = 𝟙 Y`.
   Together with `hs`, these are the two inverse identities.
4. The resulting scheme isomorphism induces a homeomorphism of underlying spaces.
   It carries the closure of the singleton generic point of `X`, which is all of
   `X`, to all of `Y`. Thus its image is the generic point of `Y`, uniquely since
   schemes are sober. This proves the stated generic-point equality.
-/
theorem section_inverse_of_isIntegral_of_isIso_morphismRestrict
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsSeparated f]
    (hV : ∃ V : X.Opens, (V : Set X).Nonempty ∧ IsIso (f ∣_ V))
    (s : X ⟶ Y) (hs : s ≫ f = 𝟙 X) :
    f ≫ s = 𝟙 Y ∧ s (genericPoint X) = genericPoint Y := by
  sorry

end AlgebraicGeometry
