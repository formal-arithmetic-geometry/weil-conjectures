module


public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Over
import Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends
import Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions

/-!
# Geometric connectedness of a connected scheme receiving a geometrically connected map

Source: Stacks Project, `varieties.tex`, Tag 056R,
`lemma-geometrically-connected-criterion`
(blueprint: lem-trf-geometrically-connected-image-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A connected scheme receiving a morphism from a geometrically connected scheme over a
field is geometrically connected.

Source: Stacks Project, `varieties.tex`, Tag 056R,
`lemma-geometrically-connected-criterion`
(blueprint: lem-trf-geometrically-connected-image-criterion).

Proof: For a finite separable extension of the base field, embed it into a finite Galois
extension. The source remains connected after this extension, and the two field-extension
projections from the target base changes are surjective. A hypothetical clopen partition of
the Galois base change pulls back to the connected source; the nonempty image of the source
lies in one part. Intersect all Galois translates of that part. The intersection and its
complement are nonempty invariant clopen subsets, so the invariant closed-subset descent
statement descends them to a separation of the original connected target. Hence the Galois
base change is connected, and connectedness descends along the projection to the original
finite separable base change. The finite-separable test for geometric connectedness then
gives the conclusion.
-/
theorem GeometricallyConnected.of_connectedSpace_of_geometricallyConnected
    {k : Type u} [Field k] {T X : Scheme.{u}}
    [T.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : T ⟶ X) [f.IsOver (Spec (.of k))]
    [GeometricallyConnected (T ↘ Spec (.of k))] [ConnectedSpace X] :
    GeometricallyConnected (X ↘ Spec (.of k)) := by
  sorry

end AlgebraicGeometry

end
