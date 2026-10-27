/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z9
-/
module

public import Sheaf.AlgebraicGeometry.HilbertSamuelInvariant
public import WeilConjectures.Compactification.StrictTransform
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Algebra.Field.ULift

import Sheaf.AlgebraicGeometry.HilbertSamuelNearNormalCone
import Sheaf.RingTheory.NormalConeDirectrixMinimalPrimes
import WeilConjectures.Compactification.StrictTransformBlowup
import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Every component through a near point survives at that point

Source: ILO VIII 2.3.13, p.94; the normal-cone component argument in steps 1--3 of
lem-trf-hilbert-samuel-equality-component-rigidity.
(blueprint: lem-trf-hilbert-samuel-near-component-incidence).
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertSamuel

/-- At a near point, the unchanged part of every original component through its image
has that near point in its closure. This is an incidence assertion only; it makes no
claim about dimensions or the classification of components upstairs.

Source: ILO VIII 2.3.13, p.94, with the normal-cone argument of steps 1--3 of
lem-trf-hilbert-samuel-equality-component-rigidity; Stacks Tags 0804 and 080E.
(blueprint: lem-trf-hilbert-samuel-near-component-incidence).

Proof:
1. Write x for the image of y. Since x belongs to the support, choose its preimage z
   on the centre. Identify the intrinsic blowup with the strict transform by Tag 080E.
   The isomorphism preserves the stalks, their maximal-ideal powers and lengths, and
   the residue fields over Q; it therefore preserves the normalized function. Apply
   near_normal_cone to the centre inclusion and the point corresponding to y. It
   supplies a flat normal cone and a graded polynomial decomposition S = B[T] of its
   exceptional fibre with y on the linear vertex defined by B's positive degrees.
2. On an affine neighbourhood of x, the component W through x corresponds to a minimal
   prime of the local ring at x. Apply normalCone_directrix_minimalPrimes. The kernel
   of the component-fibre quotient lies in the vertex kernel, hence in the homogeneous
   prime of y. This inclusion concerns actual homogeneous primes and also holds for
   nonclosed y. It implies membership of y in the Proj of that component fibre.
3. The component's intrinsic blowup is its scheme-theoretic strict transform (080E).
   The Rees fibre in degree n is Ibar^n tensor k, which is
   (Ibar^n/Ibar^(n+1)) tensor_(R/I) k because I acts trivially on k. These identifications
   respect multiplication and the canonical quotient maps. Arbitrary Proj base change
   therefore identifies this fibre with the component normal-cone fibre of step 2.
4. The component blowup's underlying image is precisely the closure of the unchanged
   part of W: on each Rees chart the preserved open is schematically dense, and W is
   reduced, so its schematic closure has this topological support. Thus step 3 is
   exactly the asserted membership. If W is contained in the centre its unchanged
   part and its component Proj are empty, so step 2 rules this out as a consequence;
   no such exclusion was imposed. The assertion is vacuous for an empty blowup. -/
theorem near_point_mem_component_closure {X Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ Z)
    [Smooth p] [IsImmersion i] [IsReduced X]
    [LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)]
    (I : X.IdealSheafData) [Smooth (I.subschemeι ≫ i ≫ p)]
    (hconstant : IsLocallyConstant (fun c : I.subscheme ↦ function (i ≫ p) (I.subschemeι c)))
    (y : I.strictTransform (𝟙 X))
    (hy : strictTransformToSource (𝟙 X) I.blowupMap I.support.compl y ∈ I.support)
    (hnear : function
      (strictTransformToSource (𝟙 X) I.blowupMap I.support.compl ≫ i ≫ p) y =
        function (i ≫ p)
          (strictTransformToSource (𝟙 X) I.blowupMap I.support.compl y))
    (W : Set X) (hW : W ∈ irreducibleComponents X)
    (hpoint : strictTransformToSource (𝟙 X) I.blowupMap I.support.compl y ∈ W) :
    y ∈ closure
      (strictTransformToSource (𝟙 X) I.blowupMap I.support.compl ⁻¹'
        (W \ (I.support : Set X))) := by sorry

end AlgebraicGeometry.HilbertSamuel
