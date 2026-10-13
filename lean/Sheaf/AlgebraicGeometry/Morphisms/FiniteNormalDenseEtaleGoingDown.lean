/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Ideal.GoingDown

import Sheaf.AlgebraicGeometry.NormalSectionsFiniteProduct
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Going down on stalks of a finite map with dense etale locus

Source: Stacks Project, Tags 00H8, 0357 and 01UA.
(blueprint: new-finite-normal-dense-etale-stalk-going-down)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A finite map between locally Noetherian normal schemes that is etale over
an open with dense source preimage satisfies going down on each stalk map.

Source: Stacks Project, Tags 00H8 (going down over a normal domain), 0357
(normal components), and 01UA (flat finite presentation maps are open).
(blueprint: new-finite-normal-dense-etale-stalk-going-down)

Proof: Work over a normal affine neighbourhood of the image of the given point.
Locally Noetherian normal schemes have locally finite, disjoint irreducible
components, which are open and closed. Shrink to the component containing the
image. The finite preimage is affine and normal, so it is a finite disjoint union
of normal integral affine components. Each component meets the dense preimage
of the given open. On that open the morphism is etale and hence open. The image
of its intersection with a component is therefore a nonempty open in the
integral target component. Thus each source component dominates the target,
and the corresponding finite map of domains is injective and integral.
Apply going down over the integrally closed target domain (Tag 00H8).
Localize at the source prime and its contraction: for primes in the localized
target lying below the contraction of a source prime, going down on the affine
component supplies a prime contained in that source prime. It survives the
source localization and contracts to the required localized target prime.
The canonical affine stalk isomorphisms identify these localization maps with
the scheme stalk map. Transport the going-down property across these isomorphisms.
This also covers an empty source vacuously. No surjectivity of the whole finite
map is assumed: only the components met by its source points are used. -/
theorem finite_normal_dense_etale_stalk_goingDown {X Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y))
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (V : Y.Opens) (hdense : Dense (↑(f ⁻¹ᵁ V) : Set X))
    (hetale : Etale (f ∣_ V)) (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    Algebra.HasGoingDown (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by sorry

end AlgebraicGeometry.Scheme
