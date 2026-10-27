/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups H7 and G8
-/
module

public import Sheaf.Paper.AffineOrderedCounitData
import Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization
import Sheaf.Paper.AffineOrderedCounitDescentComparison
import Sheaf.AlgebraicGeometry.AffineTraceCompactComparisonRestriction
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.Compactification.Defs

/-! # The ordinary ordered coefficient-counit induction -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
open CategoryTheory.Limits
open scoped CategoryTheory.Functor

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
  AffineSpacePurity.C._proof_1 AffineSpacePurity.C._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000]
  Etale.ordinaryFinitePullback._proof_1 Etale.ordinaryFinitePullback._proof_2
  Etale.ordinaryFinitePullback._proof_3 Etale.ordinaryFinitePullback._proof_4
  Etale.ordinaryFinitePullback._proof_5 Etale.ordinaryFinitePullback._proof_6
  Etale.ordinaryFinitePullback._proof_7 Etale.ordinaryFinitePullback._proof_8
  Etale.ordinaryFinitePullback._proof_9 Etale.ordinaryFinitePullback._proof_10
  Etale.ordinaryFinitePullback._proof_11 Etale.ordinaryFinitePullback._proof_12
  Etale.ordinaryFinitePullback._proof_13

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.finiteEtaleTateLine DerivedCategory.TStructure.t
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory DerivedCategory.singleFunctors

attribute [local implicit_reducible] affineTraceTower affineTraceProjection
  Etale.derivedTensorRight Etale.derivedTensorRightFunctor
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
attribute [local irreducible] Etale.affineTraceUnboundedCompactComparison
  Etale.rightDerivedLowerShriekOfCompactificationIso
  Etale.unboundedEtaleLowerShriekCompIso Etale.unboundedEtaleLowerShriekId
  Etale.rightDerivedLowerShriekOfCompactificationPlusIso
  Etale.rightDerivedLowerShriekPlusCompIso Etale.upperStar

private theorem compactComparison_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    (Y : Scheme.{u}) [IsNoetherian Y] (d : ℕ)
    (M : DerivedCategory.Plus
      (Sheaf (affineTraceTower Y d).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ordinaryCompactComparison A Y d M =
      (Etale.affineTraceUnboundedCompactComparison A Y d).app M.obj := by
  apply Iso.ext
  change (Etale.affineTracePlusCompatibility A Y d).inv.app M ≫
    DerivedCategory.Plus.ι.map
      ((Etale.affineTraceCompactSupportComparison A Y d).hom.app M) ≫
    (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
      (affineTraceProjection Y d)).hom.app M =
    (Etale.affineTraceUnboundedCompactComparison A Y d).hom.app
      (DerivedCategory.Plus.ι.obj M)
  apply (cancel_epi ((Etale.affineTracePlusCompatibility A Y d).hom.app M)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  exact (Etale.affineTraceUnboundedCompactComparison_restriction A Y d M).symm

private theorem unboundedComparison_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    (Y : Scheme.{u}) [IsNoetherian Y] (d : ℕ) :
    Etale.affineTraceUnboundedCompactComparison A Y d =
      Etale.affineDualizingTowerComparison A Y d := by
  delta Etale.affineTraceUnboundedCompactComparison Etale.affineDualizingTowerComparison
  rfl

private theorem linearComparison_eq (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :
    Etale.affineLinearCompactComparison N hN A hA Y hY d =
      (Etale.affineDualizingTowerComparison A Y d).app
        ((Etale.affineTraceRight A N hA Y d).obj (Etale.ordinaryFiniteUnit A Y)) := by
  change ordinaryCompactComparison A Y d _ = _
  rw [compactComparison_eq, unboundedComparison_eq]

private theorem normalization_transport {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (TC : C ⥤ C) (TD : D ⥤ D)
    (pf : ∀ W : C, TD.obj (F.obj W) ⟶ F.obj (TC.obj W))
    (hp : ∀ {W V : C} (c : W ⟶ V), TD.map (F.map c) ≫ pf V =
      pf W ≫ F.map (TC.map c))
    {W V J : C} {K U : D} (c : W ≅ V) (eW : J ≅ TC.obj W)
    (eV : J ≅ TC.obj V) (he : eV = eW ≪≫ TC.mapIso c)
    (z : F.obj J ⟶ K) (tW : F.obj W ⟶ U) (tV : F.obj V ⟶ U)
    (ht : tV = F.map c.inv ≫ tW) (un : TD.obj U ⟶ K)
    (hn : pf V ≫ F.map eV.inv ≫ z = TD.map tV ≫ un) :
    pf W ≫ F.map eW.inv ≫ z = TD.map tW ≫ un := by
  have h := congrArg (TD.map (F.map c.hom) ≫ ·) hn
  simp only [he, ht, Iso.trans_inv, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc] at h
  rw [reassoc_of% (hp c.hom)] at h
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id] at h
  simpa only [TC.map_id, F.map_id, Category.id_comp] using h

private theorem trace_transport {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {L W V : C} {K : D}
    (b : L ≅ W) (a : L ≅ V) (z : F.obj L ⟶ K) :
    F.map a.inv ≫ z = F.map (b.symm ≪≫ a).inv ≫ F.map b.inv ≫ z := by
  calc
    _ = F.map a.inv ≫ (F.map b.hom ≫ F.map b.inv) ≫ z := by
      rw [← F.map_comp, b.hom_inv_id, F.map_id, Category.id_comp]
    _ = _ := by
      simp only [Iso.trans_inv, Iso.symm_inv, F.map_comp, Category.assoc]

private theorem projection_forward {C : Type*} [Category C]
    {X Y Z : C} (q : X ≅ Y) {p : X ⟶ Y} {z z' : Y ⟶ Z} {t : X ⟶ Z}
    (hp : q.hom = p) (hz : z' = z) (h : z' = q.inv ≫ t) : p ≫ z = t := by
  rw [← hp, ← hz, h, Iso.hom_inv_id_assoc]

private theorem projection_paste {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {a b c d e f : C}
    {x y z v : D} (l : x ⟶ y) (s : y ⟶ z) (s' : x ⟶ v)
    (p : z ⟶ F.obj a) (p' : v ⟶ F.obj b)
    (u : a ⟶ c) (u' : b ⟶ d) (t : c ⟶ e) (t' : d ⟶ f)
    (m : v ⟶ z) (r : b ⟶ a) (q : d ⟶ c) (n : f ⟶ e)
    (hs : l ≫ s = s' ≫ m) (hp : m ≫ p = p' ≫ F.map r)
    (hu : r ≫ u = u' ≫ q) (ht : q ≫ t = t' ≫ n) :
    l ≫ s ≫ p ≫ F.map u ≫ F.map t =
      (s' ≫ p' ≫ F.map u' ≫ F.map t') ≫ F.map n := by
  rw [reassoc_of% hs, reassoc_of% hp]
  simp only [Category.assoc]
  rw [← F.map_comp_assoc, hu, F.map_comp, Category.assoc,
    ← F.map_comp, ht, F.map_comp]

private theorem projection_naturality (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {W W' : Etale.DerivedCategoryModule A X} (c : W ⟶ W')
    (K : Etale.DerivedCategoryModule A Y) :
    ((Etale.ordinaryFiniteTensor A Y).obj K).map
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map c) ≫
      Etale.compactSupportProjectionMap A f W' K =
    Etale.compactSupportProjectionMap A f W K ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((Etale.ordinaryFiniteTensor A X).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).map c) := by
  let F := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
  let Q := Etale.ordinaryFinitePullback A f
  let U := (Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
  let T := Etale.derivedTensor (ModuleCat.{u + 1} A) X
  have hs := ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).naturality
    (F.map c)
  have hp := NatTrans.naturality_app
    (Etale.projectionMap (ModuleCat.{u + 1} A) f) K c
  have he := ((T.map c).naturality
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app K)).symm
  have ht := ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app
    (U.obj K)).naturality c
  change ((Etale.ordinaryFiniteTensor A Y).obj K).map (F.map c) ≫
      (_ ≫ ((Etale.projectionMap (ModuleCat.{u + 1} A) f).app W').app K ≫
        F.map ((T.obj W').map _) ≫ F.map _) =
    (_ ≫ ((Etale.projectionMap (ModuleCat.{u + 1} A) f).app W).app K ≫
        F.map ((T.obj W).map _) ≫ F.map _) ≫ F.map _
  dsimp only [Functor.flip_obj_map, Functor.flip_map_app] at hs ht
  change ((T.map c).app (Q.obj K)) ≫ (T.obj W').map _ =
    (T.obj W).map _ ≫ (T.map c).app (U.obj K) at he
  change ((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).map (F.map c)).app K ≫
      ((Etale.projectionMap (ModuleCat.{u + 1} A) f).app W').app K =
    ((Etale.projectionMap (ModuleCat.{u + 1} A) f).app W).app K ≫
      F.map ((T.map c).app (Q.obj K)) at hp
  exact projection_paste F _ _ _ _ _ _ _ _ _ _ _ _ _ hs hp he ht

private theorem bifunctor_iso_transport {C D E : Type*}
    [Category C] [Category D] [Category E] (T : C ⥤ D ⥤ E)
    {K K' : D} {L M N : C} (u : K ≅ K') (v : L ≅ M) (a : L ≅ N) :
    (T.obj L).mapIso u ≪≫ (T.mapIso a).app K' =
      (T.mapIso v).app K ≪≫ (T.obj M).mapIso u ≪≫
        (T.mapIso (v.symm ≪≫ a)).app K' := by
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Functor.map_comp, NatTrans.comp_app]
  rw [← reassoc_of% ((T.map v.hom).naturality u.hom)]
  simp only [← NatTrans.comp_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id, T.map_id, NatTrans.id_app, Category.id_comp]

private theorem tensorRightMapIso_refl (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (K : Etale.DerivedCategoryModule A X)
    {L M : Etale.DerivedCategoryModule A X} (c : L ≅ M) :
    Etale.ordinaryFiniteTensorRightMapIso A X (Iso.refl K) c =
      ((Etale.ordinaryFiniteTensor A X).obj K).mapIso c := by
  apply Iso.ext
  simp only [Etale.ordinaryFiniteTensorRightMapIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.refl_hom,
    (Etale.derivedTensorRight (ModuleCat.{u + 1} A) X L).map_id, Category.id_comp]
  rfl

private theorem natIso_refl_app {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (K : C) : (Iso.refl F).app K = Iso.refl (F.obj K) := rfl

private theorem reassociation_eq (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y) (d : ℕ) :
    Etale.OrdinaryAffineCounitTensorNormalization.reassociation
      (AffineLinePurity.Ring P) (exponent P)
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
      (transport P) Y (exponentUnit P Y aY) d K =
    ordinarySourceIso P Y aY K d ≪≫
      Etale.ordinaryFiniteTensorRightMapIso (AffineLinePurity.Ring P) (affineTraceTower Y d)
        (Iso.refl _) ((coefficientComparison P Y aY d).symm ≪≫
          Etale.CoordinateCounitArrows.towerTateIso (AffineLinePurity.Ring P) (exponent P)
            (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
            (transport P) Y (exponentUnit P Y aY) d) := by
  unfold Etale.OrdinaryAffineCounitTensorNormalization.reassociation
  rw [normalized_source_descent]
  unfold ordinarySourceIso ordinarySourceIsoFixed coefficientComparison
  simp only [Iso.trans_assoc]
  congr 2
  unfold Etale.ordinaryFiniteTensorRightMapIso
  simpa only [Functor.mapIso_refl, Iso.refl_trans, Iso.trans_refl,
    Functor.mapIso_trans, NatIso.trans_app, natIso_refl_app, Iso.trans_symm,
    Iso.symm_symm_eq, Iso.trans_assoc, Etale.derivedTensorRight,
    Etale.derivedTensorRightFunctor, Etale.ordinaryFinitePullback] using
    bifunctor_iso_transport
      (Etale.derivedTensorRightFunctor
        (ModuleCat.{u + 1} (AffineLinePurity.Ring P)) (affineTraceTower Y d))
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
        (affineTraceProjection Y d)).app K)
      (Etale.vectorIntegrationBaseCoefficientPullback (AffineLinePurity.Ring P)
        (exponent P) (annihilates P) (transport P) (affineTraceProjection Y d)
        (exponentUnit P Y aY) d)
      ((Etale.affineLinearCoefficientDescent (AffineLinePurity.Ring P)
        (exponent P) (annihilates P) (transport P) Y (exponentUnit P Y aY) d).symm ≪≫
        Etale.CoordinateCounitArrows.towerTateIso (AffineLinePurity.Ring P) (exponent P)
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
          (transport P) Y (exponentUnit P Y aY) d)

attribute [local irreducible] ordinaryCompactComparison

private theorem ordinaryCounit_eq (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hK : etaleFiniteTor (AffineLinePurity.Ring P) Y K) (d : ℕ) :
    ordinaryCounit P Y aY K hK d =
      (Etale.affineDualizingTowerComparison (AffineLinePurity.Ring P) Y d).inv.app _ ≫
        (orderedAdjunction P Y aY d).counit.app K := by
  unfold ordinaryCounit
  rw [compactComparison_eq (AffineLinePurity.Ring P) Y d
    ⟨_, ordinarySource_plus P Y aY K hK d⟩, unboundedComparison_eq]
  rfl

attribute [local irreducible] ordinaryCounit ordinarySourceIso

private theorem normalizedCounit_eq (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hK : etaleFiniteTor (AffineLinePurity.Ring P) Y K) (d : ℕ) :
    Etale.OrdinaryAffineCounitTensorNormalization.counit
      (AffineLinePurity.Ring P) (exponent P)
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
      (transport P) (projectiveDatum P) Y (exponentUnit P Y aY) d K =
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (affineTraceProjection Y d)).map
        (Etale.OrdinaryAffineCounitTensorNormalization.reassociation
          (AffineLinePurity.Ring P) (exponent P)
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
          (transport P) Y (exponentUnit P Y aY) d K).inv ≫
      ordinaryCounit P Y aY K hK d := by
  rw [ordinaryCounit_eq]
  rfl

private theorem normalizedTrace_eq (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    Etale.OrdinaryAffineCounitTensorNormalization.trace
      (AffineLinePurity.Ring P) (exponent P)
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
      (transport P) (projectiveDatum P) Y (exponentUnit P Y aY) d =
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (affineTraceProjection Y d)).map
        ((coefficientComparison P Y aY d).symm ≪≫
          Etale.CoordinateCounitArrows.towerTateIso (AffineLinePurity.Ring P) (exponent P)
            (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
            (transport P) Y (exponentUnit P Y aY) d).inv ≫
      ordinaryTraceRaw P Y aY d := by
  unfold Etale.OrdinaryAffineCounitTensorNormalization.trace ordinaryTraceRaw
  rw [linearComparison_eq]
  exact trace_transport _ (coefficientComparison P Y aY d)
    (Etale.CoordinateCounitArrows.towerTateIso (AffineLinePurity.Ring P) (exponent P)
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
      (transport P) Y (exponentUnit P Y aY) d) _

attribute [local irreducible] Etale.OrdinaryAffineCounitTensorNormalization.reassociation
  Etale.OrdinaryAffineCounitTensorNormalization.counit
  Etale.OrdinaryAffineCounitTensorNormalization.trace

set_option linter.unusedVariables false in
/-- One-coordinate propagation of the ordinary coefficient-counit formula.
The hypothesis is the preceding rank formula for every finite-Tor coefficient input;
no assertion about the zero-coordinate normalization is included.
Source: current blueprint, projection-purity agreement proof, final paragraph;
expanded ordered-transpose argument, Steps 5 and 6.
(blueprint: lem-pur-affine-ordered-counit-successor).

Proof: apply the existing ordinaryAffineCounit_tensor_normalization in rank d+1.
Its source descent has the same zero clause as ordinarySourceDescent, by the tensor
trace formula at the identity. Naturality of inverse-image composition identifies
the successor clauses; uniqueness of the specified recursion identifies the families.
The bounded compact-support comparison is the restriction of the unbounded one, which
has the same recursion as affineDualizingTowerComparison. Thus their counit maps agree.
Change the coefficient from the ordered product to the shifted Tate object by
coefficientComparison inverse followed by towerTateIso. Tensor bifunctor naturality
identifies the source isomorphisms; cancellation identifies their traces. Naturality
of the actual compact-support projection transports the existing normalization back
to OrdinaryCounitEquation. This argument applies in every rank and does not need the
preceding-rank hypothesis. -/
theorem ordinary_counit_successor (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ)
    (ih : ∀ (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hK : etaleFiniteTor (AffineLinePurity.Ring P) Y K),
    OrdinaryCounitEquation (AffineLinePurity.Ring P) (affineTraceProjection Y d)
      (Etale.affineLinearBaseCoefficient (AffineLinePurity.Ring P) (exponent P) (annihilates P)
        (affineTraceTower Y d) d) K _ (ordinarySourceIso P Y aY K d)
      (ordinaryCounit P Y aY K hK d) (ordinaryTraceRaw P Y aY d)) :
    ∀ (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hK : etaleFiniteTor (AffineLinePurity.Ring P) Y K),
    OrdinaryCounitEquation (AffineLinePurity.Ring P) (affineTraceProjection Y (d + 1))
      (Etale.affineLinearBaseCoefficient (AffineLinePurity.Ring P) (exponent P) (annihilates P)
        (affineTraceTower Y (d + 1)) (d + 1)) K _ (ordinarySourceIso P Y aY K (d + 1))
      (ordinaryCounit P Y aY K hK (d + 1)) (ordinaryTraceRaw P Y aY (d + 1)) := by
  -- The existing normalization supplies the coefficient formula in every rank.
  clear ih
  intro K hK
  let n := d + 1
  let A := AffineLinePurity.Ring P
  let hN : 0 < exponent P := pow_pos (Fact.out : P.coefficients.l.Prime).pos _
  let F := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection Y n)
  let W := Etale.affineLinearBaseCoefficient A (exponent P) (annihilates P)
    (affineTraceTower Y n) n
  let V := Etale.SectionLocalDualizingComparisons.tateObject A (exponent P)
    (annihilates P) (affineTraceTower Y n) n
  let TC := (Etale.ordinaryFiniteTensor A (affineTraceTower Y n)).obj
    ((Etale.upperStar (ModuleCat.{u + 1} A)
      (affineTraceProjection Y n)).mapDerivedCategory.obj K)
  let TD := (Etale.ordinaryFiniteTensor A Y).obj K
  let c : W ≅ V := (coefficientComparison P Y aY n).symm ≪≫
    Etale.CoordinateCounitArrows.towerTateIso A (exponent P) hN (annihilates P)
      (transport P) Y (exponentUnit P Y aY) n
  let eV := Etale.OrdinaryAffineCounitTensorNormalization.reassociation
    A (exponent P) hN (annihilates P) (transport P) Y (exponentUnit P Y aY) n K
  have he : eV = ordinarySourceIso P Y aY K n ≪≫ TC.mapIso c := by
    simpa only [tensorRightMapIso_refl] using reassociation_eq P Y aY K n
  have hz : Etale.OrdinaryAffineCounitTensorNormalization.counit
      A (exponent P) hN (annihilates P) (transport P) (projectiveDatum P)
      Y (exponentUnit P Y aY) n K =
      F.map eV.inv ≫ ordinaryCounit P Y aY K hK n := by
    exact normalizedCounit_eq P Y aY K hK n
  have ht : Etale.OrdinaryAffineCounitTensorNormalization.trace
      A (exponent P) hN (annihilates P) (transport P) (projectiveDatum P)
      Y (exponentUnit P Y aY) n = F.map c.inv ≫ ordinaryTraceRaw P Y aY n := by
    exact normalizedTrace_eq P Y aY n
  obtain ⟨q, hq, hn⟩ := Etale.ordinaryAffineCounit_tensor_normalization
    (exponent P) hN A (annihilates P) (transport P) (projectiveDatum P)
    Y (exponentUnit P Y aY) n K
  have hn' : Etale.compactSupportProjectionMap A (affineTraceProjection Y n) V K ≫
      F.map eV.inv ≫ ordinaryCounit P Y aY K hK n =
      TD.map (Etale.OrdinaryAffineCounitTensorNormalization.trace
        A (exponent P) hN (annihilates P) (transport P) (projectiveDatum P)
        Y (exponentUnit P Y aY) n) ≫ (Etale.derivedTensorSingleUnitIso K).hom := by
    exact projection_forward q hq hz hn
  unfold OrdinaryCounitEquation
  rw [Etale.ordinaryFiniteTensorTrace_app]
  exact normalization_transport F TC TD
    (fun M ↦ Etale.compactSupportProjectionMap A (affineTraceProjection Y n) M K)
    (fun f ↦ projection_naturality A (affineTraceProjection Y n) f K)
    c (ordinarySourceIso P Y aY K n) eV he (ordinaryCounit P Y aY K hK n)
    (ordinaryTraceRaw P Y aY n) _ ht (Etale.derivedTensorSingleUnitIso K).hom hn'


end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
