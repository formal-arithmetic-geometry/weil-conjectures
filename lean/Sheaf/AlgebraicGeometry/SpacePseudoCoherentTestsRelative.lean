/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativePseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
import Sheaf.AlgebraicGeometry.SpaceDerivedChowNeighbourhood
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import Sheaf.AlgebraicGeometry.SpaceFlatProperPseudoCoherentDirectImage
import WeilConjectures.AlgebraicGeometry.PseudoCoherentQCoh
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import Sheaf.AlgebraicGeometry.SpaceDerivedQCohPullbackTensor
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.AlgebraicGeometry.SpaceDerivedChowTransformRestriction

/-! # Pseudo-coherent tensor tests detect relative pseudo-coherence

Source: Stacks Project, spaces-more-morphisms.tex, Tag 0CTT,
lemma-characterize-pseudo-coherent
(blueprint: lem-sfb-space-pseudocoherent-tests-relative).

The unbounded categories and canonical tensor and K-injective global sections use the
existing small ringed model. The test ranges over all pseudo-coherent derived objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w wZ

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Pseudo-coherent global tensor tests imply pseudo-coherence relative to the affine base.
Source: Stacks Project, Tag 0CTT, lemma-characterize-pseudo-coherent
(blueprint: lem-sfb-space-pseudocoherent-tests-relative).

Proof:
1. At each point x choose the derived Chow neighbourhood of
   lem-sfb-space-derived-chow-neighbourhood. Write T = X times_A P^n_A, with projections
   p and q, and W -> X etale, W -> V a finitely presented closed immersion into an open
   V of projective space. Retain the pseudo-coherent graph kernel E on T.
2. For each integer d, tensor E with Lq* O(d). Line twists are locally trivial, so this
   remains pseudo-coherent. By lem-sfb-space-flat-proper-pseudocoherent-direct-image,
   its projective direct image G_d under p is pseudo-coherent on X.
3. The finite-free local models have quasi-coherent cohomology by
   lem-sc-pseudo-coherent-qcoh, lem-sfb-derived-etale-zariski-equivalence and
   lem-sfb-etale-pseudocoherence-descent. Pullback and tensor preserve it by
   lem-sfb-space-derived-qcoh-pullback-tensor. The qcqs direct-image theorem
   lem-sfb-qcqs-space-pushforward-right-adjoint gives M = Rq*(Lp*K tensor E) in D_QCoh.
4. Apply lem-sfb-space-qcqs-derived-projection-formula to q and then p, and composition
   of derived direct images from lem-weil-pbc-ringed-topoi-derived-pushforward-composition.
   RGamma(P, M tensor O(d)) is isomorphic to RGamma(X, K tensor G_d), which is
   pseudo-coherent by the hypothesis and tensor symmetry. No flatness of q is used.
5. The etale/Zariski comparison intertwines tensor and global sections. The twist test
   lem-sfb-projective-space-pseudocoherence-twist-test for d = 0,...,n makes M
   pseudo-coherent. Descent and restriction give pseudo-coherence on V.
6. By lem-sfb-space-derived-chow-transform-restriction its restriction is Rj*(K|_W),
   for the closed immersion j : W -> V and etale restriction W -> X.
7. Transport to Zariski scheme categories. Since V is flat and locally finitely presented
   over A, lem-sfb-flat-ambient-relative-pseudocoherence makes K|_W relatively
   pseudo-coherent over A.
8. These neighbourhoods cover X. Apply
   lem-sfb-space-relative-pseudocoherence-etale-locality separately for every integer m.
   This is precisely the conclusion; the empty space uses the empty covering. -/
theorem isPseudoCoherentRelativeTo_of_pseudoCoherent_tensor_tests
    (A : CommRingCat.{u}) (X : AlgebraicSpace (Spec A))
    [HasDerivedCategory.{w} X.SmallModules]
    [∀ T : Scheme.{u},
      HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec A))))
    (_hsep : MapIsSeparated f)
    (_hfp : MapIsQuasiCompact f.hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal f.hom.hom) ∧ MapIsLocallyOfFinitePresentation f)
    (K : X.DerivedQCoh)
    (_htests : ∀ E : X.DerivedModules, X.IsPseudoCoherent E →
      DerivedCategory.IsPseudoCoherent
        ((affineDerivedSections A (Over.mk (𝟙 (Spec A))) (Iso.refl _) X f).obj
          (X.derivedDualityModel.closed.tensor.obj (E, K.obj)))) :
    IsPseudoCoherentRelativeTo f K := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
