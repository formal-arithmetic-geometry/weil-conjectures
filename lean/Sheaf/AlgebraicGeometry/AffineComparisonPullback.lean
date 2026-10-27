/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AffineCohomologyComparisonData
public import Sheaf.AlgebraicGeometry.QcoherentPullbackSections
public import Sheaf.AlgebraicGeometry.AffinePullbackCoefficientMap
public import Sheaf.AlgebraicGeometry.CoherentEtalePullbackData
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare
import Sheaf.AlgebraicGeometry.AffineNormalizedComparisonFamily
import Sheaf.AlgebraicGeometry.AffineComparisonChosenEquality
import Sheaf.AlgebraicGeometry.AffineRestrictionEquation

/-! # Affine specialization of normalized coherent pullback

Source: Stacks Project, Tags 03Q8, 03FD, 01FT and 03DR.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

private theorem normalized_square_transport
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
    [F.IsQuasicoherent] [G.IsQuasicoherent] (ψ : (tensorPullback g).obj F ⟶ G)
    (q : ℕ)
    (eF : Sheaf.H (liftedCoherentEtaleSheaf F) q →
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj F)
    (eG : Sheaf.H (liftedCoherentEtaleSheaf G) q →
      (RingedSpace.moduleCohomology Y.toRingedSpace q).obj G)
    (r : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F →
      (RingedSpace.moduleCohomology Y.toRingedSpace q).obj G)
    (heF : ∀ x, eF x = (cX F q).symm x)
    (heG : ∀ x, eG x = (cY G q).symm x)
    (hr : ∀ x, r x = moduleCohomologyFMap g
      ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv F G ψ) q x) :
    ∃ θ : liftedCoherentEtaleSheaf F ⟶
        (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (liftedCoherentEtaleSheaf G),
      (∀ (U : X.Etale) (s : (etaleTensorSectionsSheaf F).obj.obj (op U)),
        θ.hom.app (op U) (ULift.up s) = ULift.up
          (qcoherentPullbackSection g F G ψ U
            ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj U)
            (pullback.fst U.hom g) pullback.condition s)) ∧
      ∀ (x : Sheaf.H (liftedCoherentEtaleSheaf F) q),
        eG (Sheaf.H.map
          ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
            (liftedCoherentEtaleSheaf F) (liftedCoherentEtaleSheaf G) |>.symm θ)
          q (Etale.cohomologyMap g (liftedCoherentEtaleSheaf F) q x)) =
        r (eF x) := by
  obtain ⟨θ, hθ, hq⟩ := qcoherentNormalizedComparison_pullback_square X Y cX cY
    hcX hcY g F G ψ
  refine ⟨θ, hθ, ?_⟩
  intro x
  exact (heG _).trans ((hq q x).trans
    ((hr _).symm.trans (congrArg r (heF x).symm)))

attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf

attribute [local irreducible] affineRealizationComparison
  IsNormalizedCoherentEtaleComparison moduleAbelianCohomologyLarge

private theorem canonical_square_transport
    (X Y : Scheme.{u}) [CompactSpace X] [Scheme.IsSeparated X]
    [CompactSpace Y] [Scheme.IsSeparated Y]
    (g : Y ⟶ X) (F : X.Modules) (G : Y.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (ψ : (tensorPullback g).obj F ⟶ G)
    (q : ℕ)
    (eF : Sheaf.H (liftedCoherentEtaleSheaf F) q →
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj F)
    (eG : Sheaf.H (liftedCoherentEtaleSheaf G) q →
      (RingedSpace.moduleCohomology Y.toRingedSpace q).obj G)
    (r : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F →
      (RingedSpace.moduleCohomology Y.toRingedSpace q).obj G)
    (heF : ∀ x, eF x = affineRealizationComparison X F q x)
    (heG : ∀ x, eG x = affineRealizationComparison Y G q x)
    (hr : ∀ x, r x = moduleCohomologyFMap g
      ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv F G ψ) q x) :
    ∃ θ : liftedCoherentEtaleSheaf F ⟶
        (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (liftedCoherentEtaleSheaf G),
      HasQcoherentPullbackSectionFormula g F G ψ θ ∧
      ∀ (x : Sheaf.H (liftedCoherentEtaleSheaf F) q),
        eG (coherentEtalePullbackMap g F G θ q x) =
        r (eF x) := by
  let cX := affineNormalizedComparisonFamily X
  let cY := affineNormalizedComparisonFamily Y
  have hs := normalized_square_transport X Y cX cY
    (affineNormalizedComparisonFamily_normalized X)
    (affineNormalizedComparisonFamily_normalized Y)
    g F G ψ q eF eG r
    (fun x ↦ (heF x).trans (DFunLike.congr_fun
      (affineRealizationComparison_eq_family X F q) x))
    (fun x ↦ (heG x).trans (DFunLike.congr_fun
      (affineRealizationComparison_eq_family Y G q) x)) hr
  obtain ⟨θ, hθ, hq⟩ := hs
  refine ⟨θ, (hasQcoherentPullbackSectionFormula_iff g F G ψ θ).mpr hθ, ?_⟩
  intro x
  exact (congrArg eG (coherentEtalePullbackMap_apply g F G θ q x)).trans (hq x)

attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange

attribute [local irreducible] RingedSpace.moduleCohomology
  tensorPullback tensorPullbackObj tensorSectionsComp
  tensorSectionsUnit qcoherentPullbackSection
  affineRealizationAffineComparison affineRealizationRestriction moduleCohomologyFMap
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

/-- The canonical normalized affine comparison carries structural etale
pullback to tensor-composition restriction on ordinary module cohomology.
This square concerns arbitrary Ext classes and contains no raw derived-Hom class.
Source: Stacks Project, Tags 03P2 (coherent etale comparison), 03FD
(module/abelian cohomology), and 01FD (Cech refinement).
(blueprint: lem-weil-pbc-affine-comparison-pullback).

Proof: Put Y=V times_S X and Y'=V' times_S X, with induced etale map b.
Base change of quasi-compactness makes Y and Y' compact over the affine charts.
Separatedness over an affine scheme gives absolute separatedness of each.
Let c and c' be the uniquely normalized comparison families chosen in
exists_unique_qcoherentNormalizedComparison. The definitions of
affineRealizationComparison and affineRealizationAffineComparison use exactly
these families. Take psi to be tensorSectionsComp(b,pullback.snd) followed by
the transport along b.w. Apply qcoherentNormalizedComparison_pullback_square
to c,c', their normalization properties, and psi. It supplies theta and exactly
the section formula in the statement. Its equation holds for every Ext class x.
Rewrite the affine comparisons using affineRealizationAffineComparison_eq;
unfold affineRealizationComparison to identify them with c.symm and c'.symm.
Unfold affineRealizationRestriction: its chosen tensor adjunction and psi are
precisely those in the ordinary map of the square. Substitute these equalities.
No raw comparison or Ext-to-derived evaluation is used. Empty charts, zero
coefficients and degree zero are covered by the same equations. -/
theorem affineRealizationComparison_pullback {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (q : ℕ) (V V' : S.Etale) [IsAffine V.left] [IsAffine V'.left] (h : V' ⟶ V) :
    ∃ θ : liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V) ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} (affineRealizationChartMap f h)).obj
        (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V')),
      HasQcoherentPullbackSectionFormula (affineRealizationChartMap f h)
        (affineRealizationCoefficient f G V) (affineRealizationCoefficient f G V')
        (affineRealizationCoefficientMap f G h) θ ∧
      ∀ x : Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q,
        affineRealizationAffineComparison f G q V'
          (coherentEtalePullbackMap (affineRealizationChartMap f h)
            (affineRealizationCoefficient f G V) (affineRealizationCoefficient f G V') θ q x) =
          affineRealizationRestriction f G q h
            (affineRealizationAffineComparison f G q V x) := by
  let Y : Scheme := Limits.pullback V.hom f
  let Y' : Scheme := Limits.pullback V'.hom f
  let : IsAffine ((𝟭 Scheme).obj V.left) := ‹IsAffine V.left›
  let : IsAffine ((𝟭 Scheme).obj V'.left) := ‹IsAffine V'.left›
  let : CompactSpace ((𝟭 Scheme).obj V.left) :=
    Scheme.compactSpace_of_isAffine V.left
  let : CompactSpace ((𝟭 Scheme).obj V'.left) :=
    Scheme.compactSpace_of_isAffine V'.left
  let : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.fst V.hom f)
  let : CompactSpace Y' :=
    QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.fst V'.hom f)
  let : Scheme.IsSeparated Y :=
    (HasAffineProperty.iff_of_isAffine (P := @IsSeparated)
      (Q := fun Z _ _ _ ↦ Scheme.IsSeparated Z)
      (f := Limits.pullback.fst V.hom f)).mp inferInstance
  let : Scheme.IsSeparated Y' :=
    (HasAffineProperty.iff_of_isAffine (P := @IsSeparated)
      (Q := fun Z _ _ _ ↦ Scheme.IsSeparated Z)
      (f := Limits.pullback.fst V'.hom f)).mp inferInstance
  have hF := affineRealizationAffineComparison_eq f G q V
  have hG := affineRealizationAffineComparison_eq f G q V'
  have hR := affineRealizationRestriction_apply f G q h
  have hs := canonical_square_transport (Limits.pullback V.hom f)
    (Limits.pullback V'.hom f) (affineRealizationChartMap f h)
    (affineRealizationCoefficient f G V) (affineRealizationCoefficient f G V')
    (affineRealizationCoefficientMap f G h) q
  refine hs
    (fun x ↦ affineRealizationAffineComparison f G q V x)
    (fun x ↦ affineRealizationAffineComparison f G q V' x)
    (fun x ↦ affineRealizationRestriction f G q h x) ?_ ?_ hR
  · intro x
    exact DFunLike.congr_fun hF x
  · intro x
    exact DFunLike.congr_fun hG x

end
end AlgebraicGeometry.Scheme.Modules
