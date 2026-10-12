/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.AlgebraicGeometry.Curve.ReductionIdealPowerQuotient
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.Algebra.Category.Grp.Ulift
import Sheaf.AlgebraicGeometry.Curve.ReductionUnitsPowerInclusion

/-! # Comparison of the multiplicative and additive nilradical-power cokernels

Source: blueprint `lem-sc-brauer-zero-all-curves`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-units-power-cokernel)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- The cokernel of the constructed inclusion of consecutive nilpotent-units kernels
is the additive étale sheaf of the constructed module `N^(j+1)/N^(j+2)`.
Source: blueprint `lem-sc-brauer-zero-all-curves`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-units-power-cokernel)

Proof: On an affine étale object V over an affine open U of X, write A=Γ(U,O_X),
B=Γ(V,O_V), I=N(U)^(j+1), and J=N(U)^(j+2). Base change of the closed subschemes
identifies the kernels with 1+IB and 1+JB inside B's units. The constructed kernel
inclusion is the ordinary subgroup inclusion, since both inclusions into Gm agree.
Flatness of B over A identifies the sections of the pullback of the constructed
module cokernel with IB/JB. Send 1+a to the class of a. The formula
(1+a)(1+b)=1+a+b+ab is additive modulo JB, since I²⊆J (2j+2≥j+2).
Its kernel is exactly 1+JB. Every quotient class lifts to a in IB; all such a are
nilpotent, because each is a finite sum of multiples of nilpotent elements.
Thus 1+a is invertible, and the map is surjective on these affine objects.
Restriction maps carry a to its ring image, so these local maps agree on affine
étale refinements and glue to a morphism of sheaves. Its categorical cokernel
property follows from the just established kernel and local surjectivity.
Uniqueness of cokernels gives the claimed isomorphism. The coefficient universe
lift is an additive equivalence onto the lifted groups and preserves this
cokernel comparison sectionwise. If N=0 or X is empty both sides are zero;
for j=0 the required exponent inequality is equality. No Noetherian or global
nilpotence hypothesis enters the construction. -/
theorem nonempty_reductionUnitsPowerCokernelIso (X : Scheme.{u}) (j : ℕ) :
    Nonempty (cokernel (X.reductionUnitsPowerInclusion j) ≅
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf (X.reductionIdealPowerQuotient j)))) := by sorry

end AlgebraicGeometry.Scheme
