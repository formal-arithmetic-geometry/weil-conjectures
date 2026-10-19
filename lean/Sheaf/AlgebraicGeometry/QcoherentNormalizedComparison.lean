/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z7
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import WeilConjectures.AlgebraicGeometry.EtaleAffineTensorCechVanishing
import Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen
import WeilConjectures.AlgebraicGeometry.EtaleFiniteAffineCechBasis
import Sheaf.AlgebraicGeometry.EtaleQcoherentULiftCohomologyNatural
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsRightExact
import Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison
import Sheaf.AlgebraicGeometry.ModuleCechBetaAffineQuasiIso
import Sheaf.AlgebraicGeometry.ModuleCechComparison
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization
import Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility
import Sheaf.CategoryTheory.DoubleComplexTotal
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites
import WeilConjectures.CategoryTheory.EffaceableDeltaFunctorUniversal
import WeilConjectures.CategoryTheory.SiteCechMathlibComparison

/-! # Normalized quasi-coherent comparison on a quasi-compact separated scheme

Source: Stacks Project, Tags 03P2, 03FD, 010S, 010T and 01FD.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option autoImplicit false

/-- Existence of the normalized comparison on one quasi-compact separated scheme.
The comparison is specified as a morphism of delta functors, in addition to its
normalization on sections. The uniqueness clause determines every component.

Source: Stacks Project, Etale Cohomology, Tag 03P2, separated-case affine-cover
argument; Cohomology on Sites, Tag 03FD; Homology, Tags 010S and 010T.
(blueprint: lem-weil-pbc-qcoherent-normalized-comparison-exists)

Proof: Choose a finite affine open cover. Separatedness makes all nonempty
finite intersections affine. The module Cech alpha map is a quasi-isomorphism
by injective Cech acyclicity, and beta is a quasi-isomorphism by affine
quasi-coherent vanishing. The associated etale sheaf, including its coefficient
lift, is likewise acyclic on these intersections by the affine Cech vanishing
criterion. Its normalized Cech edge is consequently invertible. Identify the
two section complexes tuple by tuple using ULift.down; this commutes with the
signed face maps and is inverted by ULift.up. Compose the module edge with the
inverse etale edge to obtain the inverse of c. In degree zero both edges are
gluing of sections, giving the displayed unit formula. Forgetting module
scalars gives the fixed moduleAbelianCohomologyLarge comparison: its common
resolution construction preserves the normalized edges. Thus c transported
along this comparison is normalized on the underlying abelian cohomology.
The total-complex sign (-1)^(t*r) fixes both augmentation axes, so it does not
change this assertion. Lift a short exact sequence to resolutions; the same
augmentation diagram commutes with the connecting morphisms, with Ext's
connecting-class convention. This proves IsNormalizedCoherentEtaleComparison.
Coefficient naturality also holds directly for c: combine normalized
naturality with moduleCohomologyExtResolutionEquiv_naturality. Changing the Ext
presentation universe preserves postcomposition, since homAddEquiv takes both
composites to composition with the same degree-zero derived morphism. Cancel
the inverse fixed comparison. For uniqueness, use the monomorphism from F into the finite product of
j_i*(F restricted to U_i), where j_i are the affine cover inclusions. These
inclusions are affine because X is separated. Their pushforwards preserve
quasi-coherence and are exact on quasi-coherent modules. Each factor is
cohomologically acyclic, since U_i is affine, and so is the finite product.
The cokernel is quasi-coherent, as can be checked on affine opens. The full
subcategory of quasi-coherent modules is abelian: kernels and cokernels are
computed in modules and their quasi-coherence is checked on affine opens.
View both cohomologies as delta functors on that category. These
embeddings efface every positive degree of quasi-coherent cohomology. The
ordinary etale/Zariski and coefficient-lift comparison theorems give the same
vanishing on the lifted etale side. The associated sheaf construction is
exact on quasi-coherent modules: check after affine etale pullback, which is
flat, and sheafify. Thus both sides are effaceable delta functors. Extend the
section identification by dimension shifting along these embeddings. The
connecting-map identities force this extension uniquely, independently of
the embeddings; the same construction for the inverse section map proves
that it is an isomorphism in every degree. Conjugate by the fixed
moduleAbelianCohomologyLarge comparison to obtain uniqueness of c. Empty schemes
and zero modules give zero complexes;
no nonemptiness, properness, smoothness or field assumption is required. -/
theorem exists_unique_qcoherentNormalizedComparison
    (X : Scheme.{u}) [CompactSpace X] [Scheme.IsSeparated X] :
    ∃! c : ∀ (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
      ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≃+
        Sheaf.H (liftedCoherentEtaleSheaf F) q,
      IsNormalizedCoherentEtaleComparison X
          (fun F _ q ↦ (moduleAbelianCohomologyLarge X F q).symm.trans (c F q)) ∧
        (∀ (F : X.Modules) [F.IsQuasicoherent] (s : Γ(F, ⊤)),
          Sheaf.H.equiv₀ (liftedCoherentEtaleSheaf F) terminalIsTerminal
            (c F 0
              ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app F s)) =
            ULift.up (tensorSectionsUnit (⊤_ X.Etale).hom F s)) ∧
        ∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
          (φ : F ⟶ G) (q : ℕ)
          (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F),
          c G q ((RingedSpace.moduleCohomology X.toRingedSpace q).map φ x) =
            Sheaf.H.map (coherentEtaleMap F G φ) q (c F q x) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
