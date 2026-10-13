/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Normalization

/-!
# Relative normalization in a dense open of a normal scheme

Sources: Stacks Project, Tags 0357, 035I and 0AB1.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A locally Noetherian normal scheme is its own relative normalization in a dense open.

Source: Stacks Project, Tags 0357 (normal components), 035I (relative normalization),
and 0AB1 (integral birational maps to normal schemes).
(blueprint: lem-sbc-normalization-dense-open)

Proof: This is local on X. On an affine open Spec A, the Noetherian normal ring A
is a finite product of integrally closed domains A_i (0357). The intersection of V
with each Spec A_i is a nonempty open, since V is dense. It therefore contains the
generic point. Its section ring embeds in Frac(A_i), by restriction to the generic
point: sections on an integral scheme are determined by their generic germ.
Every section integral over A_i then lies in A_i by integral closedness. Conversely,
every element of A_i gives an integral section. Taking the finite product shows
that the integral closure of A in the sections on V intersect Spec A is exactly A.
The relative normalization over Spec A is the spectrum of this integral closure
(035I), so its canonical map to Spec A is an isomorphism. These local assertions
show the canonical map is an isomorphism on X. Empty affine opens contribute the
zero ring; if X is empty the same assertion holds. No nonemptiness of X is needed. -/
theorem isIso_fromNormalization_denseOpen
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hnormal : ∀ z : X, IsDomain (X.presheaf.stalk z) ∧
      IsIntegrallyClosed (X.presheaf.stalk z))
    (V : X.Opens) (hV : Dense (V : Set X)) :
    IsIso V.ι.fromNormalization := by sorry

end AlgebraicGeometry.Scheme
