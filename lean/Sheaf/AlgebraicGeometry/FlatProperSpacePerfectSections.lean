/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Sheaf.AlgebraicGeometry.ProperSupportTensorPerfect
import WeilConjectures.AlgebraicGeometry.PerfectAffineBoundedProjective
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence

/-! # Perfect derived sections on a flat proper algebraic space

Source: Stacks Project, spaces-perfect.tex, Tag 0CTM(1),
lemma-flat-proper-perfect-direct-image-general; affine identification by Tags 071Q,
08HG, 08EB and 06Z0 (blueprint: lem-sfb-flat-proper-space-perfect-sections).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Derived global sections of a perfect complex on a flat proper finitely presented
algebraic space over an affine scheme form a perfect complex of base-ring modules.
The affine presentation `e` records the base ring; scalar sections use its actual
chartwise structural ring maps. The small affine étale model is the existing equivalent
ringed topos, retaining the original section universe.

Source: Stacks Project, spaces-perfect.tex, Tag 0CTM(1), with Tags 071Q, 08HG,
08EB, 06Z0 and 0D6E (blueprint: lem-sfb-flat-proper-space-perfect-sections).

Proof:
1. Take the coefficient complex G to be O_X in degree zero. It is bounded,
quasi-coherent and finitely presented. Flatness of f gives relative flatness of its
stalks; its annihilator is zero, so its closed support is X, proper over the base.
2. Apply lem-sfb-proper-support-tensor-perfect. The tensor unit identifies
E tensor^L O_X with E, giving a perfect quasi-coherent derived direct image K.
3. By lem-sfb-scheme-derived-etale-qcoh-comparison write K as the étale pullback
of a Zariski quasi-coherent derived object L. The equivalence in
lem-sfb-etale-detects-perfect makes L perfect. Then
lem-pc-perfect-affine-bounded-projective realizes L by the associated sheaf complex
of a bounded complex P of finite projective A-modules.
4. The composition comparison
lem-weil-pbc-ringed-topoi-derived-pushforward-composition identifies RΓ(X,E)
with RΓ(Y_et,K), with the structural A-action. The global-sections part of
lem-sfb-scheme-derived-etale-qcoh-comparison identifies this with RΓ(Y_Zar,L).
Finally lem-pc-affine-qcoh-derived-equivalence identifies the derived sections
of the associated sheaf complex of P with P in D(A). Compose these isomorphisms. -/
theorem flatProperSpace_perfect_sections
    {S : Scheme.{u}} (A : Type u) [CommRing A]
    (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)
    [HasDerivedCategory.{w} X.SmallModules]
    (_hflat : MapIsFlat f) (_hproper : MapIsProper f)
    (_hfp : MapIsLocallyOfFinitePresentation f ∧ MapIsQuasiCompact f.hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (E : X.DerivedModules)
    (_hE : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      X.smallStructureSheaf E) :
    DerivedCategory.IsPerfectRingComplex ((affineDerivedSections A Y e X f).obj E) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
