/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Sheaf.AlgebraicGeometry.EtaleTensorPositiveObjectCohomology
import Sheaf.AlgebraicGeometry.ModuleCohomologyCoefficientTransport
import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge
import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization
import Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives
import Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility
import Sheaf.CategoryTheory.RingedSiteCechRefinementSquare
import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyNatural
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.Paper.PQFCohomology

/-! Comparison squares for additive structure-sheaf cohomology. -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical coherent-etale comparison commutes with structural pullback.
Source: Stacks Project, Tags 03P2, 03FD, 01FD and 01FB.
(blueprint: new-coherent-etale-comparison-pullback).

Proof: Choose finite affine covers of the proper schemes and refine the target
cover so each target open maps into an open of the source cover. Separatedness
makes all tuple intersections affine. The structure modules are quasi-coherent;
affine vanishing, module-to-abelian comparison, and etale object vanishing give
acyclicity on all tuples. Use normalized Cech edges on both sites. The
change-of-site edge square for the Zariski-to-etale inclusion identifies the
normalized comparison with the common-section-complex comparison, by its
naturality, connecting-map compatibility and degree-zero normalization.
The adjoint formula hu says that the etale pullback cochain map on this refinement
is precisely structural pullback of regular functions. The ringed-site refinement
square gives the identical cochain map for the resolution-defined module fmap.
The module-forgetting edge square uses the fixed resolution comparison, by its
normalization on arbitrary injective resolutions. Thus the two composites agree
on every Cech class. Surjectivity of the acyclic Cech edges proves the displayed
identity for every class. This is valid in degree zero and for empty schemes; it
does not assert flat base change or identify inverse image of the structure
sheaf with the target structure sheaf. -/
theorem coherentEtaleComparison_pullback
    {k K : Type u} [Field k] [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (g : Y ⟶ Spec (.of K)) [IsProper g] (j : Y ⟶ X) (q : ℕ)
    (u : (Etale.upperStar AddCommGrpCat.{u + 1} j).obj
      (structureTensorEtaleSheaf X) ⟶ structureTensorEtaleSheaf Y)
    (hu : ∀ (U : X.Etale) (s : (structureTensorEtaleSheaf X).obj.obj (op U)),
      (tensorPullbackObjUnitToUnit
          ((MorphismProperty.Over.pullback @Etale ⊤ j).obj U).hom).app ⊤
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).homEquiv
          (structureTensorEtaleSheaf X) (structureTensorEtaleSheaf Y) u).hom.app
            (op U) s).down =
        (pullback.fst U.hom j).appTop
          ((tensorPullbackObjUnitToUnit U.hom).app ⊤ s.down))
    (x : Sheaf.H (structureTensorEtaleSheaf X) q) :
    structureCoherentEtaleComparison g q
        (Sheaf.H.map u q (Etale.cohomologyMap j (structureTensorEtaleSheaf X) q x)) =
      (moduleCohomologyFMap j
        (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) q).hom
        (structureCoherentEtaleComparison f q x) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
