/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.AlgebraicGeometry.ProperSupportTensorPerfect
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! # Flat proper direct image preserves pseudo-coherence on algebraic spaces

Source: Stacks Project, spaces-perfect.tex, Tag 0CTN,
lemma-flat-proper-pseudo-coherent-direct-image-general (pseudo-coherence conclusion);
spaces-more-morphisms.tex, Tag 0CTT, lemma-characterize-pseudo-coherent, proof.
(blueprint: lem-sfb-space-flat-proper-pseudocoherent-direct-image).

The ambient categories are unbounded. Finite presentation is local finite presentation,
quasi-compactness, and quasi-compactness of the diagonal. The projective specialization
uses the actual sheaf fibre product and its first projection.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Flat proper finitely presented direct image preserves pseudo-coherent complexes.
Source: Stacks Project, Tag 0CTN, pseudo-coherence conclusion
(blueprint: lem-sfb-space-flat-proper-pseudocoherent-direct-image).

Proof: (1) Restrict the target to affine etale charts using
lem-trf-space-fibre-products-etale-covers, lem-sfb-space-flat-proper-fp-locality,
lem-sfb-space-fp-qcqs-source and lem-sfb-space-derived-etale-chart-calculus.
(2) Choose the upper bound N from lem-sfb-space-derived-pushforward-upper-bound.
For each integer m put a = m-N-1. The perfect approximation of F from
lem-sfb-space-pseudocoherent-perfect-approximation has cone C with H^i(C)=0 for i >= a,
by lem-sf-derived-homology-long-exact.
(3) Apply lem-sfb-proper-support-tensor-perfect to the perfect approximation P and
O_Y in degree zero. Its sole nonzero term is finitely presented, quasi-coherent,
flat over the base by lem-sfb-space-module-flat-chart-test and
lem-sfb-space-local-properties-chart-test, and has proper support Y. Zero terms have
empty proper support by lem-sfb-space-proper-support-closed-operations. The tensor unit
identification gives that Rg_*P is perfect.
(4) The upper bound applied to C with b=a-1 gives vanishing of Rg_*C in degrees
j >= m-2. The derived distinguished triangle (lem-pc-right-derived-functor-triangulated)
and its long exact sequence make H^i(Rg_*P) -> H^i(Rg_*F) invertible for i >= m.
(5) Quasi-coherence follows from lem-sfb-space-derived-pushforward-coproducts.
Use lem-sfb-derived-etale-zariski-equivalence, then
lem-sfb-etale-pseudocoherence-descent for every m, and
def-pur-pseudo-coherent-complex to obtain local bounded-above finite-free models.
(6) Return to the original target. Choose one K-injective representative by
prop-pur-kinjective-resolutions-exist. Restriction preserves K-injectivity by
lem-pur-kinjective-restrict-localized. By lem-sc-kinjective-quasi-iso-comparison the local
derived isomorphisms lift to quasi-isomorphisms into this representative. Pulling back
covering sieves and restricting these maps verifies def-sfb-space-pseudocoherent-complex.
No lower cohomological bound or Noetherian hypothesis occurs. -/
theorem isPseudoCoherent_derivedDirectImage_of_flat_proper
    {S : Scheme.{u}} {Y Z : AlgebraicSpace S}
    [HasDerivedCategory.{w} Y.SmallModules] [HasDerivedCategory.{w} Z.SmallModules]
    (g : Y ⟶ Z) (_hflat : MapIsFlat g) (_hproper : MapIsProper g)
    (_hfp : MapIsLocallyOfFinitePresentation g ∧ MapIsQuasiCompact g.hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal g.hom.hom))
    (F : Y.DerivedModules) (_hF : Y.IsPseudoCoherent F) :
    Z.IsPseudoCoherent ((derivedDirectImage g).obj F) := by
  sorry

/-- The structural map of projective n-space as the actual representable sheaf map.
Source: Stacks Project, constructions.tex, Tags 01NF and 01NG; Tag 0CTT, proof
(blueprint: lem-sfb-space-flat-proper-pseudocoherent-direct-image).
There are n+1 homogeneous coordinates, also when n=0. -/
def projectiveSpaceStructureMap (A : CommRingCat.{u}) (n : ℕ) :
    schemeSpace (Over.mk (ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec A) ↘ Spec A)) ⟶
      schemeSpace (Over.mk (𝟙 (Spec A))) :=
  ObjectProperty.homMk ((Scheme.fppfTopology.over (Spec A)).yoneda.map
    (Over.homMk (ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec A) ↘ Spec A)))

/-- The projective projection preserves pseudo-coherence over every commutative ring.
Source: Stacks Project, Tag 0CTT, proof using Tag 0CTN
(blueprint: lem-sfb-space-flat-proper-pseudocoherent-direct-image).

Proof: (7) On an affine etale chart Spec R of X, identify the fibre product with P^n_R
using lem-trf-free-projective-bundle-base-change-space and
lemma-nagata-projective-space-base-change-pullback. Its projection is proper by
lemma-nagata-projective-space-base-change-proper. By
lem-weil-pbc-projective-space-standard-charts it is covered by n+1 affine polynomial
charts. Each is flat by lem-nagata-polynomial-projection-flat and finitely presented
(n generators and no relations). Apply lem-sfb-scheme-etale-source-target-properties.
(8) Properness gives quasi-compactness and separatedness; lem-weil-pbc-qcqs-over-affine
and lem-weil-pbc-qcqs-morphism-permanence give the required quasi-separatedness.
Use lem-sfb-space-local-properties-chart-test and def-sfb-space-morphism-properties
to identify scheme properties with space properties. Apply steps (1)--(6) of
isPseudoCoherent_derivedDirectImage_of_flat_proper to the chart projection.
The comparison of lem-sfb-space-derived-etale-chart-calculus and the representative
descent of step (6) give the result on X. For n=0 the sole chart has ring R;
empty spaces and the zero ring require no exception. -/
theorem isPseudoCoherent_derivedDirectImage_projectiveProjection
    (A : CommRingCat.{u}) (X : AlgebraicSpace (Spec A))
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec A)))) (n : ℕ)
    [HasDerivedCategory.{w} X.SmallModules]
    [HasDerivedCategory.{w}
      (enlargedFibreProduct f (projectiveSpaceStructureMap A n)).SmallModules]
    (F : (enlargedFibreProduct f (projectiveSpaceStructureMap A n)).DerivedModules)
    (_hF : (enlargedFibreProduct f (projectiveSpaceStructureMap A n)).IsPseudoCoherent F) :
    X.IsPseudoCoherent
      ((derivedDirectImage
        (enlargedFibreProductFst f (projectiveSpaceStructureMap A n))).obj F) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
