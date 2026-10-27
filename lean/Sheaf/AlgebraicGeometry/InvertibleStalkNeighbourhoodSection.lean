module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism

/-! # Spreading an inverse stalk map to a neighbourhood section

Source: Stacks Project, Varieties, Tag 0BFP, proof (4); Morphisms, Tag 0BX6,
case (2)(c) (blueprint: lem-sfb-invertible-stalk-neighbourhood-section).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An invertible stalk map of a locally finite-type morphism over a locally Noetherian
scheme spreads to a section through the given point. Its stalk map is the given inverse,
using the canonical stalk identification for the open subscheme. The same section factors
through the inverse-image open as a section of the restricted morphism.

Source: Stacks Project, Varieties, Tag 0BFP, proof (4); Morphisms, Tag 0BX6, case (2)(c)
(blueprint: lem-sfb-invertible-stalk-neighbourhood-section).

Proof: (1) Put x = f(y). The inverse of the local ring isomorphism f.stalkMap y is
local, since a ring isomorphism preserves units and hence the maximal ideals of local
rings. By morphism-from-spec-local-ring (SpecToEquivOfLocalRing), the pair consisting of
y and this inverse gives a morphism phi : Spec O_{X,x} to Y. By the composition formula
for stalk maps, f composed with phi has normalized stalk map the identity at the closed
point. The same bijection identifies this composite with X.fromSpecStalk x
(spec-local-ring-canonical-morphism).
(2) Apply local-ring-map-spread (spread_out_of_isGermInjective') with base X, source X
and structure map the identity, target Y and structure map f. Local Noetherianness and
local finite type give an open neighbourhood W and s : W to Y with s followed by f equal
to the inclusion, and phi equal to the canonical local-spectrum map followed by s.
(3) Evaluate the latter equality at the closed point to get s(x) = y. Taking its
normalized stalk map, using scheme-stalk-map-composition and the identity normalized
stalk map of the canonical local-spectrum morphism, gives the displayed inverse formula.
Finally open-preimage-fibre-product identifies the pullback of f along W with f^{-1}(W).
The pair (s, identity) therefore gives t to this open, with projection to W the identity;
conversely composing such a section with the open inclusion recovers s. -/
theorem exists_neighbourhood_section_of_isIso_stalkMap
    {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : Y ⟶ X) [LocallyOfFiniteType f] (y : Y) [IsIso (f.stalkMap y)] :
    ∃ (W : X.Opens) (hx : f y ∈ W) (s : W.toScheme ⟶ Y)
      (hy : s ⟨f y, hx⟩ = y),
      s ≫ f = W.ι ∧
      (Y.presheaf.stalkCongr (Inseparable.of_eq hy)).inv ≫
        s.stalkMap ⟨f y, hx⟩ ≫ (W.stalkIso ⟨f y, hx⟩).hom = inv (f.stalkMap y) ∧
      ∃ t : W.toScheme ⟶ (f ⁻¹ᵁ W).toScheme,
        t ≫ (f ⁻¹ᵁ W).ι = s ∧ t ≫ (f ∣_ W) = 𝟙 W.toScheme := by
  sorry

end AlgebraicGeometry.Scheme
