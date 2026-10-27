module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses
public import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Ideal.Maximal

/-! # Finite type points of algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tag 06EF, conditions (1) and (2),
and Tag 06EH (blueprint: lem-sfb-space-finite-type-point-characterization).

Points use the existing quotient of field-valued representatives. Local finite type
is tested on all compatible representable étale scheme charts, using the existing
`EtalePresentation` structure also for a scheme source represented by Yoneda.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A point has a closed lift in an étale scheme chart if and only if it has a
locally finite type field-valued representative. No finiteness or separation
condition is imposed on the base or on the algebraic space.

Source: Stacks Project, Morphisms of Spaces, Tags 06EF and 06EH
(blueprint: lem-sfb-space-finite-type-point-characterization).

Proof: (1) Given a closed point w of W and an étale e : W → X, take K = κ(w).
The canonical map Spec κ(w) → W is locally of finite type by the scheme field-point
criterion [lem-sfb-finite-type-field-point-characterization]: w is closed in an affine
neighbourhood and its residue extension is the identity. Étale maps are locally of
finite type, and composition preserves this property, by
[lem-sfb-stack-chartwise-smooth-etale-calculus]. The composite represents e(w).
(2) Conversely, pull a surjective étale scheme atlas U → X back along a locally
finite type representative Spec K → X. The pullback V is a nonempty scheme, and
V → U is locally of finite type by [lem-trf-space-fibre-products-etale-covers],
[lem-sfb-stack-chartwise-smooth-etale-calculus] and
[lem-sfb-space-local-properties-chart-test].
(3) In a nonempty affine open V₀ = Spec A, choose a maximal ideal, using
[lem-weil-pbc-proper-ideal-contained-in-maximal]. Its point v is closed in V₀.
The scheme field-point criterion makes Spec κ(v) → V locally of finite type.
The composite to U is locally of finite type as well, so its image u is closed
in some affine open U₀ of U, again by that criterion.
(4) Restrict the atlas to U₀. The resulting map U₀ → X is representable étale,
by [lem-weil-pbc-open-immersion-etale], the chartwise composition calculus, and
representability of the atlas. The pullback identity shows that its value at u and
the original representative agree after a common field extension. Indeed maps of
field spectra are field extensions, and [lem-weil-pbc-morphism-from-spec-field]
factors Spec κ(v) → U through Spec κ(u). Thus the two classes equal x. -/
theorem closed_etale_lift_iff_locallyOfFiniteType_representative
    {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Point X.obj.obj) :
    (∃ (W : Over S) (w : W.left) (e : yoneda.obj W ⟶ X.obj.obj),
      IsClosed ({w} : Set W.left) ∧ IsEtale e ∧ schemePointMap e w = x) ↔
    ∃ p : PointRepresentative X.obj.obj,
      Quot.mk _ p = x ∧
        ∀ D : EtalePresentation (yonedaEquiv.symm p.value), LocallyOfFiniteType D.h.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
