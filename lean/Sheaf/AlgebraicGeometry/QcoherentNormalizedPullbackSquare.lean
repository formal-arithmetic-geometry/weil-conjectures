/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z7
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import Sheaf.AlgebraicGeometry.QcoherentPullbackSections
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import WeilConjectures.AlgebraicGeometry.EtaleAffineTensorCechVanishing
import Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen
import WeilConjectures.AlgebraicGeometry.EtaleFiniteAffineCechBasis
import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsMapNaturality
import WeilConjectures.AlgebraicGeometry.ModuleCechBetaAffineQuasiIso
import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization
import Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import Sheaf.CategoryTheory.RingedSiteCechRefinementSquare
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites
import WeilConjectures.CategoryTheory.EffaceableDeltaFunctorUniversal
import WeilConjectures.CategoryTheory.SiteCechMathlibComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # The normalized cohomology refinement square

Source: Stacks Project, Tags 03P2, 03FD, 010S and 01FD.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option autoImplicit false

/-- The Cech comparison intertwines the two canonical cohomology maps.
The comparisons are given; this assertion supplies their pullback compatibility
and the coefficient sheaf morphism, not their existence.

Source: Stacks Project, Cohomology, Tag 01FD; Etale Cohomology, Tag 03P2;
Cohomology on Sites, Tags 03AX and 03FD.
(blueprint: lem-weil-pbc-qcoherent-normalized-pullback-square)

Proof: For each etale U over X, use structural tensor-section pullback to
U times_X Y, followed by the pullback of psi. These maps are additive. To
check restrictions, the two paths around a map of pullback squares are the
same composite structural pullback: use unit naturality and associativity
of the adjunction-mate composition isomorphisms, then coefficient naturality.
Apply ULift to the component maps; its functor law preserves naturality.
This constructs theta, and its evaluation is the displayed section formula.
Choose finite affine covers on X and Y, refining the inverse image of
X's cover by affine opens on Y. Separatedness makes all tuple intersections
affine. The inverse images before refinement need not be affine. Both ordinary
and lifted associated-etale coefficients are acyclic on these intersections,
so their normalized Cech edges are invertible. The maps on tuple sections for
the two covers are structural pullback followed by the pullback of psi.
The component formula just proved identifies theta with exactly this map.
Coordinatewise ULift.down intertwines the two Cech maps. Apply the
ringed-site Cech refinement square in the Zariski and etale sites. Its abelian
specialization computes the etale cohomology map as cohomologyMap followed by
the adjoint coefficient map, since set-valued etale inverse image is exact.
Its module specialization computes the Zariski map as moduleCohomologyFMap of
the tensor adjoint of psi. The normalized Cech comparisons agree with cX and
cY: they are morphisms of delta functors with the same section normalization,
and quasi-coherent cohomology is effaceable on these qcqs schemes. Cancel the
invertible Cech edges to get the stated equality. All transports use the
common-resolution moduleAbelianCohomologyLarge, whose normalized edge square
respects the connecting-class convention. Empty schemes and zero modules
produce zero complexes and are included. No flatness of g is required. -/
theorem qcoherentNormalizedComparison_pullback_square
    (X Y : Scheme.{u}) [CompactSpace X] [Scheme.IsSeparated X]
    [CompactSpace Y] [Scheme.IsSeparated Y]
    (cX : ∀ (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
      ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≃+
        Sheaf.H (liftedCoherentEtaleSheaf F) q)
    (cY : ∀ (G : Y.Modules) [G.IsQuasicoherent] (q : ℕ),
      ((RingedSpace.moduleCohomology Y.toRingedSpace q).obj G) ≃+
        Sheaf.H (liftedCoherentEtaleSheaf G) q)
    (hcX : IsNormalizedCoherentEtaleComparison X
      (fun F _ q ↦ (moduleAbelianCohomologyLarge X F q).symm.trans (cX F q)))
    (hcY : IsNormalizedCoherentEtaleComparison Y
      (fun G _ q ↦ (moduleAbelianCohomologyLarge Y G q).symm.trans (cY G q)))
    (g : Y ⟶ X) (F : X.Modules) (G : Y.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (ψ : (tensorPullback g).obj F ⟶ G) :
    ∃ θ : liftedCoherentEtaleSheaf F ⟶
        (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (liftedCoherentEtaleSheaf G),
      (∀ (U : X.Etale) (s : (etaleTensorSectionsSheaf F).obj.obj (op U)),
        θ.hom.app (op U) (ULift.up s) = ULift.up
          (qcoherentPullbackSection g F G ψ U
            ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj U)
            (pullback.fst U.hom g) pullback.condition s)) ∧
      ∀ (q : ℕ) (x : Sheaf.H (liftedCoherentEtaleSheaf F) q),
        (cY G q).symm (Sheaf.H.map
          ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
            (liftedCoherentEtaleSheaf F) (liftedCoherentEtaleSheaf G) |>.symm θ)
          q (Etale.cohomologyMap g (liftedCoherentEtaleSheaf F) q x)) =
        moduleCohomologyFMap g
          ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv F G ψ)
          q ((cX F q).symm x) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
