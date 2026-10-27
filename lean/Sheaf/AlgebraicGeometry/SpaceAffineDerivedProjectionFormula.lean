/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.AlgebraicGeometry.SpaceAffineProjectionData
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Sheaf.CategoryTheory.RingedToposMorphism
import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.ProjectionMateExact
import Sheaf.AlgebraicGeometry.SpacePerfectLocalizingGeneration
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.AlgebraicGeometry.SpaceDerivedQCohPullbackTensor
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.RingedProjectionTensorComposition

/-! # The affine projection formula for a flat qcqs algebraic space

Source: Stacks Project, spaces-perfect.tex, Tag 08IN, lemma-cohomology-base-change;
flat-pullback paragraph preceding lemma-check-quasi-coherence-on-covering
(blueprint: lem-sfb-space-affine-derived-projection-formula).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
namespace AlgebraicGeometry.AlgebraicSpace

/-- The affine derived projection formula, including exact scalar pullback, quasi-coherence,
its degree-zero representative, and naturality for every coefficient homomorphism.
Source: Stacks Project, spaces-perfect.tex, Tag 08IN, lemma-cohomology-base-change,
flat-pullback paragraph preceding lemma-check-quasi-coherence-on-covering
(blueprint: lem-sfb-space-affine-derived-projection-formula).

Proof:
1. On every affine étale chart Spec B the scalar functor is B tensor_A N. The
Zariski/étale quasi-coherent comparison, affine pullback sections, and preservation
of quasi-coherence by space pullback give quasi-coherence of F_N. Chartwise flatness
and flat tensor exactness give exactness, which is local on the étale site.
2. A map F_N to M is equivalent to the A-linear map n to g(1 tensor n) into
compatible sections, with inverse b tensor n to b times that section. This pins
the structural action and the ordinary adjunction. Exact derived factorization
computes pullback termwise and gives the stated canonical single comparison.
K-flat resolutions and the balanced formula b tensor (c tensor x) to bc tensor x
identify this with the composite pullback through Spec A. Derived adjunction and
tensor pullback give the displayed representative and transpose normalizations.
3. The affine étale derived-module realization identifies D(A) with D_QCoh(Spec A),
with inverse derived sections. Its tensor dictionary is the counit-defined mate,
by full faithfulness and the ordinary unit normalization.
4. The qcqs-space pushforward-right-adjoint theorem makes Rf_* preserve coproducts
on D_QCoh. Perfect localizing generation identifies these with ambient coproducts.
Tensor and pullback preserve coproducts as left adjoints; space derived pullback
and tensor preserve quasi-coherent cohomology.
5. Fix E. The exact projection-mate theorem makes its two functors exact and its
mate compatible with shifts and connecting maps. At A[0] the unit normalization
makes it the identity; hence it is invertible on every shift A[k].
6. Its isomorphism locus is closed under triangles, coproducts, isomorphisms and
retracts. On a retract use T(r) followed by the inverse at the larger object,
followed by U(i). Derived-module free generation gives every unbounded input.
7. Specialize to N[0] and apply derived sections on Spec A. The affine dictionary
and derived direct-image composition give the displayed source and target. The
projection-composition identity identifies the actual arrow with the map defined
above, including its counit. Naturality of each comparison gives simultaneous
naturality in E and every N to N'. No boundedness or flatness of N is required. -/
theorem space_affine_derived_projection_formula (A : CommRingCat.{u})
    (X : AlgebraicSpace (Spec A))
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec A))))
    (hflat : MapIsFlat f) (hqc : MapIsQuasiCompact f.hom.hom)
    (hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} X.SmallModules] :
    ∃ d : AffineProjectionData A X,
      (∀ N : ModuleCat.{u} A,
        (X.smallModuleEquivalence.inverse.obj (affineScalarSheaf A X N)).IsQuasicoherent) ∧
      (∀ (E : X.DerivedQCoh) (N : ModuleCat.{u} A),
        IsIso (affineDerivedProjectionMap A X d E.obj N)) ∧
      (∀ (E E' : X.DerivedQCoh) (e : E ⟶ E')
          (N N' : ModuleCat.{u} A) (n : N ⟶ N'),
        (tensor (DerivedCategory (ModuleCat.{u} A))).map
          (Prod.mkHom ((affineProjectionRGamma A X d.G d.sections_additive).map e.hom)
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map n)) ≫
          affineDerivedProjectionMap A X d E'.obj N' =
        affineDerivedProjectionMap A X d E.obj N ≫
          (affineProjectionRGamma A X d.G d.sections_additive).map
            ((affineProjectionTensor A X).map
              (Prod.mkHom e.hom ((DerivedCategory.singleFunctor X.SmallModules 0).map
                (affineScalarSheafMap A X n))))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
