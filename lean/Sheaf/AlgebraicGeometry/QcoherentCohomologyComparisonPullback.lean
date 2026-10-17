/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.PQFCohomology
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.TensorPullback
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift
import Sheaf.AlgebraicGeometry.EtaleFiniteAffineCechBasis
import Sheaf.AlgebraicGeometry.EtaleAffineTensorCechVanishing
import WeilConjectures.CategoryTheory.SiteCechMathlibComparison
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen
import Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility
import Sheaf.AlgebraicGeometry.ModuleCechComparison
import Sheaf.AlgebraicGeometry.ModuleCechBetaAffineQuasiIso
import Sheaf.CategoryTheory.DoubleComplexTotal
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Sheaf.CategoryTheory.RingedSiteCechRefinementSquare
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap

/-! # Quasi-coherent cohomology comparison and pullback

Source: Stacks Project, Étale Cohomology, Tag 03P2; Cohomology, Tag 01FD.
(blueprint: lem-weil-pbc-qcoherent-cohomology-comparison-pullback).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false

/-- Structural pullback of a tensor section across a square, followed by the module map.
Source: Stacks Project, Tags 03P2, 03DR and 01FD.
(blueprint: lem-weil-pbc-qcoherent-cohomology-comparison-pullback). -/
def qcoherentPullbackSection {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) (ψ : (tensorPullback g).obj F ⟶ G)
    (U : X.Etale) (V : Y.Etale) (p : V.left ⟶ U.left)
    (h : p ≫ U.hom = V.hom ≫ g) :
    Γ((tensorPullback U.hom).obj F, ⊤) ⟶ Γ((tensorPullback V.hom).obj G, ⊤) :=
  tensorSectionsUnit p ((tensorPullback U.hom).obj F) ≫
    ((tensorSectionsComp p U.hom).hom.app F).app ⊤ ≫
    (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) h)).app ⊤ ≫
    ((tensorSectionsComp V.hom g).inv.app F).app ⊤ ≫
    ((tensorPullback V.hom).map ψ).app ⊤

/-- The simultaneous normalized comparison, natural for arbitrary scheme pullback.
Source: Stacks Project, Étale Cohomology, Tag 03P2 and Cohomology, Tag 01FD.
(blueprint: lem-weil-pbc-qcoherent-cohomology-comparison-pullback).

Proof: Choose finite affine covers by qcqs-scheme-cofinal-finite-coverings. Separatedness
makes tuple intersections affine (separated-affine-open-intersection); identify their
fibre products by zariski-etale-inclusion-morphism-of-sites. Quasi-coherent restriction
and etale-cohomology-over-open reduce ordinary affine acyclicity to etale-affine-qcoherent.
For lifted coefficients use finite-affine-cech-basis, affine-tensor-cech-vanishing,
site-cech-mathlib-comparison and cech-vanishing-criterion. The acyclic-cech-edge-compatibility
and module-cech-comparison, together with module-cech-beta-affine-quasi-iso, give invertible
normalized edges. Between them insert coordinatewise ULift.down. It commutes with the
signed face restrictions and has inverse ULift.up. The double-complex-total sign
(-1)^(tr) identifies the two totalizations and is identity on the augmentation axes.
This proves normalization in degree zero. Common affine refinements and the
ringed-site-cech-refinement-square show independence of the cover. For a morphism g,
refine the inverse image cover on Y by affine opens, without assuming the inverse images
are affine. The same refinement square for the etale sites (sets-etale-inverse-image-exact)
and the ringed Zariski sites identifies the two cochain maps: structurally pull back
and apply ψ. Coordinatewise down commutes with this formula. Cancel the invertible
edges to obtain naturality for cohomology-pullback and module-cohomology-fmap. Finally
specialize g to identity and ψ to multiplication; cohomology-pullback-functorial gives
the scalar clause. -/
theorem exists_qcoherentCohomologyComparisonPullback :
    ∃ c : ∀ (X : Scheme.{u}) [CompactSpace X] [Scheme.IsSeparated X]
      (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
      Sheaf.H (liftedCoherentEtaleSheaf F) q ≃+
        ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F),
      (∀ (X : Scheme.{u}) [CompactSpace X] [Scheme.IsSeparated X]
        (F : X.Modules) [F.IsQuasicoherent]
        (s : Γ(F, ⊤)),
        c X F 0 ((Sheaf.H.equiv₀ (liftedCoherentEtaleSheaf F)
          terminalIsTerminal).symm (ULift.up (tensorSectionsUnit (⊤_ X.Etale).hom F s))) =
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app F s) ∧
      (∀ (X Y : Scheme.{u}) [CompactSpace X] [Scheme.IsSeparated X]
        [CompactSpace Y] [Scheme.IsSeparated Y] (g : Y ⟶ X)
        (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
        (ψ : (tensorPullback g).obj F ⟶ G),
        ∃ θ : liftedCoherentEtaleSheaf F ⟶
          (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (liftedCoherentEtaleSheaf G),
          (∀ (U : X.Etale) (s : (etaleTensorSectionsSheaf F).obj.obj (op U)),
            θ.hom.app (op U) (ULift.up s) = ULift.up
              (qcoherentPullbackSection g F G ψ U
                ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj U)
                (pullback.fst U.hom g) (pullback.condition) s)) ∧
          ∀ (q : ℕ) (x : Sheaf.H (liftedCoherentEtaleSheaf F) q),
            c Y G q (Sheaf.H.map
              ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
                (liftedCoherentEtaleSheaf F) (liftedCoherentEtaleSheaf G) |>.symm θ)
              q (Etale.cohomologyMap g (liftedCoherentEtaleSheaf F) q x)) =
            moduleCohomologyFMap g
              ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv F G ψ)
              q (c X F q x)) ∧
      (∀ (X : Scheme.{u}) [CompactSpace X] [Scheme.IsSeparated X]
        (F : X.Modules) [F.IsQuasicoherent] (a : Γ(X, ⊤)) (q : ℕ)
        (x : Sheaf.H (liftedCoherentEtaleSheaf F) q),
        c X F q (Sheaf.H.map (coherentEtaleMap F F (F.smulHom a)) q x) =
          (RingedSpace.moduleCohomology X.toRingedSpace q).map (F.smulHom a) (c X F q x)) := by
  sorry

end

end AlgebraicGeometry.Scheme.Modules
