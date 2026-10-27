/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.DensePoints
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.Regular

/-! # Smooth curves interpolating finitely many rational points of an integral variety

Source: Charles--Poonen, Bertini irreducibility theorems over finite fields,
Corollary 1.9, printed p. 4, followed by normalization; Stacks Project, Tags
0BXR, 0BX2 and 038X. The dimension-zero case uses a constant projective-line map.
(blueprint: lem-sfb-integral-variety-smooth-curve-interpolation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite nonempty set of rational points on an integral separated finite-type variety
lifts to rational points on one smooth separated connected curve of dimension exactly one.

Source: Charles--Poonen, Corollary 1.9, printed p. 4, together with normalization
(Stacks Project, Tags 0BXR, 0BX2 and 038X).
(blueprint: lem-sfb-integral-variety-smooth-curve-interpolation).

Proof plan:
1. By lem-kun-dimension-finite-type, the nonempty integral scheme has finite dimension.
   The marked sections are closed immersions by
   lem-weil-pbc-section-separated-closed-immersion, hence give closed points.
2. In dimension zero, an affine neighbourhood is all of X, with coordinate ring a field.
   A marked k-point identifies this field with k. Take the projective line with the
   constant map to that point and choose its point [1:0] for every mark. Its properties
   follow from lem-asd-projective-line-genus-zero and def-weil-proper-morphism.
3. In positive dimension, iterate lem-sfb-bertini-prescribed-point-dimension-cut until an
   integral closed curve C containing the marked points is obtained (take C = X in
   dimension one). Each marked section factors through C by its defining ideal.
4. Normalize C using def-sc-normalization and lem-sc-normalization-exists. The normalization
   D is integral, nonempty and connected, and has dimension one. It is separated and finite
   type by lem-weil-pbc-finite-over-separated-finite-type. The field k is perfect, so
   lem-sc-normalized-curve-smooth gives smoothness.
5. The finite surjective normalization has nonempty finite fibres over the marked k-points.
   By def-weil-finite-integral-morphism their fibre algebras are nonzero finite-dimensional
   k-algebras. A maximal quotient is a finite field extension of the algebraically closed
   k, hence k itself. Choose the resulting rational lift of each mark, even at singular
   points or points with several branches.
6. Compose the normalization with C's inclusion into X. Its composites with the chosen
   rational lifts are exactly the given sections. -/
theorem exists_smooth_connectedCurve_interpolating
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (F : Set (f.fieldPoints k)) (hF : F.Finite) (hne : F.Nonempty) :
    ∃ (D : Scheme.{u}) (p : D ⟶ Spec (.of k)), IsConnectedCurve p ∧ Smooth p ∧
      ∃ (g : D ⟶ X), g ≫ f = p ∧
        ∃ d : F → p.fieldPoints k, ∀ s : F, (d s).val ≫ g = s.val.val :=
  sorry

end AlgebraicGeometry.Scheme.Hom
