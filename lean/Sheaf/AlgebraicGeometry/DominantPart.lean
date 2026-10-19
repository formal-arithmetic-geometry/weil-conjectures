module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Sober

/-!
# Reduced dominant part

Source: Illusie--Laszlo--Orgogozo, Exposé II, 1.2.5 (blueprint: def-per-dominant-part).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

noncomputable section

/-- The closed subset swept out by the generic points of the base.
Source: Illusie--Laszlo--Orgogozo, Exposé II, 1.2.5, printed p. 25
(blueprint: def-per-dominant-part). -/
def dominantPartClosed (X S : Scheme.{u}) (p : X ⟶ S) : TopologicalSpace.Closeds X :=
  ⟨closure (p ⁻¹' genericPoints S), isClosed_closure⟩

/-- The reduced induced closed subscheme on the dominant components of `X` over `S`.
Source: Illusie--Laszlo--Orgogozo, Exposé II, 1.2.5, printed p. 25
(blueprint: def-per-dominant-part). -/
def dominantPart (X S : Scheme.{u}) (p : X ⟶ S) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal (dominantPartClosed X S p)).subscheme

/-- The canonical closed immersion of the dominant part into `X`.
Source: Illusie--Laszlo--Orgogozo, Exposé II, 1.2.5, printed p. 25
(blueprint: def-per-dominant-part). -/
def dominantPartι (X S : Scheme.{u}) (p : X ⟶ S) : dominantPart X S p ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal (dominantPartClosed X S p)).subschemeι

end

end AlgebraicGeometry
