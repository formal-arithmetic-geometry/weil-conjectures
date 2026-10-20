/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.Paper.RingComplexGodementConstruction
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Paper.FiniteOrderedFlasqueCechComparison
import Sheaf.Paper.ModuleCupGodementModelQuasiIso
import Sheaf.Paper.ModuleCupGodementObjectFlasque
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Sheaf.Paper.ModuleCupFlasqueAcyclicity
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import Sheaf.Paper.RingComplexCechData
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
import Sheaf.Paper.PQFCohomology

/-! # The augmented ordered localization model of Godement ring complexes -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

/-- The Godement mapping fibre has the augmented ordered localization model.
Source: Stacks Project, Tags 099D(d), 0FKS, 01ET, 01EQ, 01FJ.
(blueprint: lem-weil-pbc-ring-complex-godement-cech)

Proof: cover Spec A minus V(I) by D(f_i) for the supplied generating list. Its
ordered intersections are the principal affine opens for the corresponding
products; sections of the structure sheaf are their specified localizations.
The structure module is quasi-coherent. Its higher cohomology on those affine
intersections vanishes. The prescribed Godement augmentation is a quasi-isomorphism
and its terms are flasque; restriction to an open preserves both properties.
The acyclic-resolution comparison therefore makes each section augmentation a
quasi-isomorphism. Apply finiteOrderedFlasqueCechComparison to get the natural
augmented roof between localization sections, the finite double total, and
Godement sections. Adjoin A as the first term to each arrow. Equivalently, take
mapping fibres of the augmented maps from A[0]. The identity on A and the two
quasi-isomorphisms on sections give quasi-isomorphisms on these fibres, by the
long exact cohomology sequence. The fibre of the localization augmentation has
exactly the displayed coordinates; negate successive positive-degree coordinates
as necessary to identify the mapping-cone signs with the displayed differential.
The projection in degree zero is the identity. Invert the roof in the derived
category. For r=0, the open complement is empty, all section terms are zero, and
the fibre is A[0]. Zero rings and zero or repeated generators obey the same formulas. -/
theorem ringComplex_godement_cech (A : CommRingCat.{u})
    [HasDerivedCategory.{w} (RingSiteModules A)] (I : {I : Ideal A // I.FG}) :
    RingComplexHasCechModel A I.val (ringComplexGodement A I.val)
      (ringComplexGodementAugmentation A I.val) := by sorry

end AlgebraicGeometry
