/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldScalarNormalizedData
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Normalized scalar data for one field inclusion

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md, paragraph (1).
(blueprint: lem-sp-field-scalar-single-inclusion).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale.FieldScalar

/-- Normalized scalar extension and reduction for one inclusion of finite coefficient fields.
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md, paragraph (1).
(blueprint: lem-sp-field-scalar-single-inclusion).

Proof:
1. Give F its E-algebra structure using the indicated inclusion. The compatible
spectral norms identify the integral inclusion with integralScalarIntegerInclusion.
Choose an integral basis of O_F over O_E. Reducing its unique coordinates modulo
ell^(n+1) gives the quotient basis, including ramified extensions. Apply constant
sheafification to the quotient maps. Their compatibility with all quotient transitions
is checked on residue classes. The limit universal property supplies the integral map;
transport along the normalized coefficient comparisons gives integral_projection.
2. Extend each level by sheafified tensor and use x tensor b maps to t(x) tensor q(b)
for the transitions. Balancing and composition hold on tensor generators. Restriction
is the unchanged underlying system with restricted actions. The fixed basis identifies
restricted extension with the finite power, naturally on whole systems; the columns
are exactly the reductions of the chosen basis vectors. It follows that extension is
additive and preserves finite limits and colimits. Descend its termwise functor through
quasi-isomorphisms. Its localization counit is invertible on every complex and satisfies
the universal derived property. Derived restriction gives the same finite-power iso.
3. At each level finite-free scalar calculus preserves constructibility and each
specified cohomological and Tor interval. Noetherianity supplies finite stratifications.
Successive tensor normalization identifies the reduction maps after extension with
extension of the original reduction maps, so normalized systems remain normalized.
4. The same integral basis gives the completed coefficient coordinate isomorphism.
For an integral module the ordinary reduction comparison multiplies the two coefficient
factors, with inverse inserting one. Tensor balancing proves both inverse equations;
the formulas commute with all transitions, module maps, and cochain differentials.
On a flat-term K-flat representative the same formulas compute both derived composites.
Ringed scalar extension preserves flatness and K-flatness. Strict tensor descent and
the universal counits therefore give a natural derived comparison on whole systems,
including roofs, with exactly the representative equation in ReductionComparison.
This does not include identity or successive-field comparison data. -/
theorem field_scalar_single_inclusion (l : ℕ) [Fact l.Prime] (E F : Type u)
    [Field E] [Field F] [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) (T : Scheme.{u}) [IsNoetherian T]
    (DA : SpCoefficientTowersAbelian.{u, u} l E T)
    (DB : SpCoefficientTowersAbelian.{u, u} l F T)
    (RA : SpReductionTower l E T DA) (RB : SpReductionTower l F T DB) :
    Nonempty (ScalarData l E F ι T DA DB RA RB) := by sorry

end AlgebraicGeometry.ProEtale.FieldScalar
