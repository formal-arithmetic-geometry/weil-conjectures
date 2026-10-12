/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift
import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
import Sheaf.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Degree-two vanishing for the infinitesimal units kernel on a curve

Source: blueprint `lem-sc-brauer-zero-all-curves`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-units-kernel-h2)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

/-- The kernel of the units comparison on the reduction of a curve has zero H^2.
Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-h2/
lem-sc-brauer-zero-all-curves.md, Proof, Step 1 and the following Claim.
(blueprint: lem-sc-reduction-units-kernel-h2)

Proof: Finite type over a field makes C Noetherian. The coherent nilradical N is
nilpotent, with N^m = 0 for a uniform m found on a finite affine cover. On an affine
etale V over C, flatness identifies the pulled-back N with the reduction ideal.
Consequently the kernel of G_m,C -> i_*G_m,C_red is 1 + N_et. Filter it by 1 + N^j
for j >= 1. The successive quotients are the additive quasi-coherent sheaves
(N^j/N^(j+1))_et: multiplication becomes addition because ab belongs to N^(j+1).
Their H^q vanishes for q >= 2. Indeed, a finite affine cover has affine intersections
by separatedness; affine etale acyclicity and the Cech spectral sequence compare
etale cohomology with Zariski cohomology. Grothendieck vanishing gives zero in degrees
above dim C <= 1. The long exact sequences of the filtration, descending from
1 + N^m = 0, now give H^2(C,1 + N_et) = 0. Reduction induces an exact equivalence
of etale topoi. Applying i^* identifies the above kernel with the kernel of
upperStarGmSheafToGmSheaf i, since its counit on G_m,C_red is an isomorphism.
Topological invariance of cohomology transports the vanishing to C_red. Empty,
zero-dimensional, disconnected and reduced curves are covered by the same argument. -/
theorem subsingleton_H_two_reduction_units_kernel {k : Type u} [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] :
    Subsingleton (Sheaf.H
      (kernel (Scheme.upperStarGmSheafToGmSheaf C.nilradical.subschemeι)) 2) := by
  sorry

end AlgebraicGeometry.IsCurve
