/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleOrderedIntegration
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleProjectionIntegration
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleProjectiveLineTraceSupplement
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleProjectiveCoefficient
import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.SupportedProjectiveChernComparison
import all WeilConjectures.AlgebraicGeometry.Open.OpenSiteEvaluationCounit
import all WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
import all WeilConjectures.AlgebraicGeometry.Projection.ProjectionComparisonEtaleOrigin
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProperCounitComparison

/-! # Site comparison of a normalized affine-line counit

Source: blueprint sk-prop-an, affine-space top trace, proof paragraphs 1--2;
Stacks 099R, 09AF, 0B65, and 0GL1.
(blueprint: lem-pur-line-counit-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] Etale.affineTraceOpenLeft
attribute [local implicit_reducible] affineTraceLineCompactification affineTraceTower
attribute [local implicit_reducible] Etale.cartierAbelianPro Etale.cartierAbelianEtale

end AlgebraicGeometry.ProEtale.VectorIntegrationSite

namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

private theorem open_counit_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (M : Etale.DerivedCategoryModule A (ProjectiveLine T)) :
    (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} A) (ProjectiveLine.affineChart T)).hom.app
        ((Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart T)).obj M) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} A)
        (ProjectiveLine.affineChart T)).mapDerivedCategory.map
          ((pullback A (ProjectiveLine.affineChart T)).hom.app M) ≫
      (openAdjunction A (ProjectiveLine.affineChart T)).counit.app
        ((comparison A (ProjectiveLine T)).obj M) =
      (comparison A (ProjectiveLine T)).map
        ((Etale.affineTraceOpenAdjunction A T).counit.app M) := by
  let B := ModuleCat.{u + 1} A
  let j := ProjectiveLine.affineChart T
  let e := mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso B j
  let a := Functor.mapDerivedCategorySquareIso
    (comparisonUpperStarCompUpperStarIso B j).symm
  have h := counit_of_unit
    (Etale.openImmersionLowerShriekUpperStarAdjunction B j).mapDerivedCategoryAdjunction
    (openImmersionLowerShriekUpperStarAdjunction B j).mapDerivedCategoryAdjunction
    (comparisonUpperStar B (AffineSpace PUnit.{u + 1} T)).mapDerivedCategory
    (comparisonUpperStar B (ProjectiveLine T)).mapDerivedCategory
    e a (derived_unit A j) M
  let de := Etale.leftDerivedUpperStarIsoMapDerivedCategory B j
  let dp := leftDerivedUpperStarIsoMapDerivedCategory B j
  have ha : (pullback A j).hom.app M =
      (comparison A _).map (de.hom.app M) ≫ a.hom.app M ≫
        dp.inv.app ((comparison A _).obj M) := by
    simp only [pullback, geoP1PullComparison, a, Functor.mapDerivedCategorySquareIso,
      Iso.symm_hom, Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm]
    simp only [Category.assoc]
    rfl
  have he := e.hom.naturality (de.hom.app M)
  dsimp only [Functor.comp_map] at he
  have ht : (openImmersionLowerShriek B j).mapDerivedCategory.map
        (dp.inv.app ((comparison A _).obj M)) ≫
      (openImmersionLowerShriek B j).mapDerivedCategory.map
        (dp.hom.app ((comparison A _).obj M)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app]
    exact CategoryTheory.Functor.map_id _ _
  change e.hom.app ((Etale.ordinaryFinitePullback A j).obj M) ≫
      (openImmersionLowerShriek B j).mapDerivedCategory.map ((pullback A j).hom.app M) ≫
      (openAdjunction A j).counit.app ((comparison A _).obj M) = _
  rw [ha]
  simp only [openAdjunction, Etale.affineTraceOpenAdjunction,
    Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app,
    Iso.symm_inv, Functor.map_comp, Category.assoc]
  rw [reassoc_of% ht]
  with_unfolding_all erw [← reassoc_of% he, ← h]
  rfl

private theorem paste_open_proper_counits
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    (Je : C ⥤ D) (Jp : C' ⥤ D') (Le : D ⥤ C) (Lp : D' ⥤ C')
    (Re : D ⥤ E) (Rp : D' ⥤ E')
    (CU : C ⥤ C') (CP : D ⥤ D') (CT : E ⥤ E')
    (ae : Je ⊣ Le) (ap : Jp ⊣ Lp)
    (o : Je ⋙ CP ≅ CU ⋙ Jp) (a : Le ⋙ CU ≅ CP ⋙ Lp)
    (b : Re ⋙ CT ⟶ CP ⋙ Rp)
    (M : D) (H : D') (rho : CP.obj M ⟶ H)
    (K : E) (ep : Rp.obj H ⟶ CT.obj K) (ee : Re.obj M ⟶ K)
    (ho : o.hom.app (Le.obj M) ≫ Jp.map (a.hom.app M) ≫
      ap.counit.app (CP.obj M) = CP.map (ae.counit.app M))
    (hp : b.app M ≫ Rp.map rho ≫ ep = CT.map ee) :
    (b.app (Je.obj (Le.obj M)) ≫ Rp.map (o.hom.app (Le.obj M))) ≫
      Rp.map (Jp.map (a.hom.app M ≫ Lp.map rho)) ≫
      Rp.map (ap.counit.app H) ≫ ep =
    CT.map (Re.map (ae.counit.app M) ≫ ee) := by
  have hn := ap.counit.naturality rho
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  have hnRp := congrArg (fun f ↦ Rp.map f) hn
  simp only [Functor.map_comp] at hnRp
  rw [reassoc_of% hnRp]
  have hoRp := congrArg (fun f ↦ Rp.map f) ho
  simp only [Functor.map_comp] at hoRp
  rw [reassoc_of% hoRp]
  have hb := b.naturality (ae.counit.app M)
  dsimp only [Functor.comp_map] at hb
  rw [← reassoc_of% hb, hp, ← CT.map_comp]

/-- Canonical site comparison preserves the independently normalized line counit
on every bounded-below ordinary coefficient. Source: blueprint affine-space top trace,
proof paragraphs 1--2; Stacks 099R, 09AF, 0B65, and 0GL1
(blueprint: lem-pur-line-counit-comparison).

Proof: CartierKummerChern identifies the supported pro-etale Chern arrow with the
ordinary Chern arrow under the root-normalized Tate comparison. The inverse-image
comparison and direct-image counit mate identify their adjoints and the twisted
unit components. The biproduct injections identify the projective decompositions;
inverting and taking the second projection identifies their traces. The proper
projection comparison, including symmetry, tensor comparison, and right unitor,
therefore carries the ordinary coefficient counit to projectiveEpsilon, by its
unique ProperIntegrationEquation. The exact open-extension comparison preserves
the open counit: transpose the two expressions under the open adjunction, where
both are the identity with the same inverse-image comparison. Compose the proper
and open equations and use naturality of the direct-image mate. The resulting
source comparison is exactly lineSiteComparison, which is defined from that mate
and extension comparison. This yields the displayed equality. All arguments work
for every Noetherian base with l invertible, with no finite-type field hypothesis,
and for the zero coefficient ring and empty scheme.
-/
theorem lineCounit_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    lineCounit l E n T hT (infinityCartier T) r hA K =
      (lineSiteComparison (Scheme.finiteTateCoefficient l E n) T
        ⟨_, rightTower_plus l E n T hT r hA 1 K⟩).hom ≫
      (comparison (Scheme.finiteTateCoefficient l E n) T).map
        ((Etale.affineTraceLineAdjunction _ (l ^ (r + 1)) hA
          (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
          T (by simpa only [Nat.cast_pow] using hT.pow (r + 1))
          (Etale.projectiveLineTraceDatum _ (pow_pos (Fact.out : l.Prime).pos _) _ hA
            T (by simpa only [Nat.cast_pow] using hT.pow (r + 1)))).counit.app K.obj) := by
  let A := Scheme.finiteTateCoefficient l E n
  let B := ModuleCat.{u + 1} A
  let P := ProjectiveLine T
  let j := ProjectiveLine.affineChart T
  let q : P ⟶ T := P ↘ T
  let M := (Etale.ordinaryFiniteP1Right A (l ^ (r + 1)) hA T).obj K.obj
  let J : DerivedCategory.Plus (Sheaf (AffineSpace PUnit.{u + 1} T).smallEtaleTopology B) :=
    ⟨_, rightTower_plus l E n T hT r hA 1 K⟩
  have hc := supportedProjectiveChern_comparison l E n T hT (infinityCartier T) r hA
  have hp := proper_counit_comparison l E n T hT (infinityCartier T) r hA hc K
  dsimp only at hp
  rw [pushComparison_mate] at hp
  have ho := open_counit_comparison A T M
  have h := paste_open_proper_counits
    (Etale.openImmersionLowerShriek B j).mapDerivedCategory
    (openImmersionLowerShriek B j).mapDerivedCategory
    (Etale.ordinaryFinitePullback A j) (upperStar B j).leftDerivedFunctor
    (Etale.ordinaryFinitePushforward A q) (lowerStar B q).rightDerivedFunctor
    (comparison A _) (comparison A P) (comparison A T)
    (Etale.affineTraceOpenAdjunction A T) (openAdjunction A j)
    (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso B j)
    (pullback A j) (BoundaryComparison.directImageMate B q)
    M (projectiveRight l E n r hA T K.obj)
    (projectiveRightComparison l E n r hA T K.obj).hom K.obj
    (projectiveEpsilon l E n T hT (infinityCartier T) r hA K)
    _ ho hp
  change lineCounit l E n T hT (infinityCartier T) r hA K =
    (lineSiteComparison A T J).hom ≫ _
  apply (cancel_epi (lineSiteComparison A T J).inv).1
  rw [Iso.inv_hom_id_assoc]
  rw [Etale.affineTraceLineAdjunction_counit]
  unfold lineCounit lineRightComparison pullbackThen
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  unfold lineSiteComparison
  simp only [Iso.app_inv]
  rw [compact_comparison_inv_mate]
  exact h

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
