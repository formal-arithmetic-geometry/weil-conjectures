/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Paper.CechRefinementCochainMap
public import Sheaf.AlgebraicGeometry.ModuleCechComparison

/-! # Augmentation compatibility for the canonical refinement map

Source: Stacks Project, Tag 01FD, the resolution double-complex diagram.
(blueprint: lem-sc-cech-refinement-resolution-canonical-beta)
-/

@[expose] public section

universe v
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Augmentation compatibility for the total-homology map transported through source alpha.
Source: Stacks Project, Tag 01FD, proof of Lemma 20.15.1, augmentation pentagon.
(blueprint: lem-sc-cech-refinement-resolution-canonical-beta)

Proof: apply the Cech double-complex functor to D.beta and D.lambda. Its coefficient
maps commute with restriction and augmentation. The latter map is a quasi-isomorphism
on resolution columns: on each intersection, pushforward injectives and injectives
are section-acyclic, so sections preserve the quasi-isomorphism D.lambda. Transpose
and use first-quadrant total column comparison to invert it on total homology.
Compose the map induced by D.beta, this inverse, and tuplewise pullback/restriction
from the pushforward complex to the target family. D.compatible gives the augmentation
pentagon. The tuplewise composite on the augmented row is gamma by hgamma. Taking
homology gives the beta equation for this zigzag map. Restriction naturality gives
its alpha square; D.sections identifies the global sections of the pushforward with
those on X'. Cancelling the invertible sections map of D.lambda gives the raw map r
in that square. Since source H(alpha) is invertible, the zigzag map equals the displayed
explicit map. Substituting it into the beta equation proves the claim. No target
cover is needed; empty target families and zero modules yield zero target complexes. -/
theorem cechRefinement_resolution_canonical_beta (X X' : Scheme.{v}) (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (F : X.Modules) [F.IsQuasicoherent]
    [EnoughInjectives X.Modules] [EnoughInjectives X'.Modules]
    [(RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive]
    [(RingedSpace.globalSectionsFunctor X'.toRingedSpace).Additive] (p : ℕ)
    (gamma : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat))
    (hgamma : IsCechRefinementMap f U U' refine hrefine F gamma)
    (D : ModuleCohomologyFMapData f F ((tensorPullback f).obj F)
      ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F)) :
    let r := (((RingedSpace.globalSectionsComplex D.J).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat)).inv ≫
      HomologicalComplex.homologyMap
        (((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          forget₂ _ AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).map D.β) p ≫
      inv (I := D.invertible p) (HomologicalComplex.homologyMap (D.a.hom ≫
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          forget₂ _ AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).map D.lambda) p) ≫
      (((RingedSpace.globalSectionsComplex D.I).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat)).hom
    letI := moduleCechAlpha_isIso U hU D.J p
    let t := (forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat).map
        (inv (HomologicalComplex.homologyMap (moduleCechAlpha U D.J) p)) ≫ r ≫
      (forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat).map
        (HomologicalComplex.homologyMap (moduleCechAlpha U' D.I) p)
    (forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat).map
        (HomologicalComplex.homologyMap (moduleCechBeta U D.J) p) ≫ t =
      cechRefinementHomology gamma p ≫
        (forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat).map
          (HomologicalComplex.homologyMap (moduleCechBeta U' D.I) p) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
